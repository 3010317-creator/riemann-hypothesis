import Lean.Fmt
import Lean.Language.Lean
import Batteries.Tactic.OpenPrivate

/-!
Batch driver for the auto-formatter of Lean 4 pull request 15218.

The formatter's own entry point, `Lean.Fmt.fileMain`, takes a language-server snapshot of one file,
which means importing the file's dependencies and elaborating it. This driver instead

* imports a fixed set of modules once and reuses that environment for every file, and
* parses each file command by command, elaborating only the commands that can change how later
  text is parsed (`namespace`, `section`, `end`, `open`, notation and macro declarations, ...).

It then renders each command exactly as `fileMain` does: `commandMain`, the reparse check, and the
raw fallback. No `choice` node is resolved, because nothing is elaborated. The module header
(`module` and the imports) is kept as written.

usage: lean --run BatchFmt.lean LIST SRC_ROOT OUT_ROOT LOG TIMEOUT_SECONDS PRELUDE MODULE...

PRELUDE is a Lean file whose commands are all elaborated on top of the imports before any file is
formatted, or `-`. LIST holds one path per line, relative to SRC_ROOT. A formatted file is written under OUT_ROOT only
if it differs from its input. LOG gets one tab-separated line per file:
`STATUS  milliseconds  commands  kept-raw  path  detail`.
-/

open Lean Elab

open private normalize commandRaw from Lean.Fmt.FmtM.Main

namespace BatchFmt

/-- Last components of the kinds of commands that can change how later text is parsed. -/
def parsingKinds : List String :=
  ["namespace", "section", "noncomputableSection", "end", "open", "export", "set_option",
   "universe", "notation", "mixfix", "syntax", "syntaxAbbrev", "syntaxCat", "macro",
   "macro_rules", "elab", "elab_rules", "binderPredicate", "notation3", "scopedNS"]

partial def affectsParsing (stx : Syntax) : Bool :=
  if stx.isOfKind ``Lean.Parser.Command.in then
    stx.getNumArgs > 0 && affectsParsing stx[stx.getNumArgs - 1]
  else
    match stx.getKind with
    | .str _ s => parsingKinds.contains s
    | _ => false

def elabCmd (inputCtx : Parser.InputContext) (cmd : Syntax) (st : Command.State)
    : BaseIO Command.State := do
  let ctx : Command.Context := {
    fileName := inputCtx.fileName, fileMap := inputCtx.fileMap, snap? := none, cancelTk? := none
  }
  match ← (Command.elabCommandTopLevel cmd |>.run ctx |>.run st).toBaseIO with
  | .ok (_, st') => return { st' with messages := {} }
  | .error _ => return st

/-- The namespaces that an `open` command names, also below `… in`. -/
partial def openedNamespaces (cmd : Syntax) : Array Name :=
  if cmd.isOfKind ``Lean.Parser.Command.in then
    openedNamespaces cmd[0]
  else if !cmd.isOfKind ``Lean.Parser.Command.open then
    #[]
  else
    let decl := cmd[1]
    if decl.isOfKind ``Lean.Parser.Command.openSimple then
      decl[0].getArgs.map (·.getId)
    else if decl.isOfKind ``Lean.Parser.Command.openScoped then
      decl[1].getArgs.map (·.getId)
    else
      #[decl[0].getId]

/--
`open A B` fails as a whole when `B` is unknown, and then the scoped notation of `A` is not
activated. Namespaces of the project are unknown here, because no declaration is elaborated, so
they are registered before the command runs.
-/
def registerOpened (cmd : Syntax) (st : Command.State) : Command.State := Id.run do
  let scope := st.scopes.head!
  let mut env := st.env
  for n in openedNamespaces cmd do
    if !n.isAnonymous &&
        (ResolveName.resolveNamespace env scope.currNamespace scope.openDecls n).isEmpty then
      env := env.registerNamespace n
  return { st with env }

/--
What `open` does that matters for parsing, following `Lean.Elab.elabOpenDecl`: it activates the
scoped syntax of the opened namespaces and records them, so that later namespaces resolve
relative to them. Unlike `elabOpenDecl` it does not fail on a namespace or a name that is unknown
here, which is the case for everything the project itself declares.
-/
def openForParsing (cmd : Syntax) : Command.CommandElabM Unit := do
  let decl := cmd[1]
  if decl.isOfKind ``Lean.Parser.Command.openSimple then
    for id in decl[0].getArgs do
      go id.getId true []
  else if decl.isOfKind ``Lean.Parser.Command.openScoped then
    for id in decl[1].getArgs do
      go id.getId false []
  else if decl.isOfKind ``Lean.Parser.Command.openHiding then
    go decl[0].getId true (decl[2].getArgs.map (·.getId)).toList
  -- `open A (x y)` and `open A renaming …` only change how names resolve.
where
  go (n : Name) (addDecl : Bool) (except : List Name) : Command.CommandElabM Unit := do
    if n.isAnonymous then
      return
    let scope ← Command.getScope
    let mut nss := ResolveName.resolveNamespace (← getEnv) scope.currNamespace scope.openDecls n
    if nss.isEmpty then
      modifyEnv (·.registerNamespace n)
      nss := [n]
    for ns in nss do
      activateScoped ns
      if addDecl then
        Command.modifyScope fun s =>
          { s with openDecls := OpenDecl.simple ns except :: s.openDecls }

def runCmdM (inputCtx : Parser.InputContext) (x : Command.CommandElabM Unit) (st : Command.State)
    : BaseIO Command.State := do
  let ctx : Command.Context := {
    fileName := inputCtx.fileName, fileMap := inputCtx.fileMap, snap? := none, cancelTk? := none
  }
  match ← (x.run ctx |>.run st).toBaseIO with
  | .ok (_, st') => return { st' with messages := {} }
  | .error _ => return st

/-- Elaborates every command of `path` on top of `env`: syntax the project shares across files. -/
def loadPrelude (env : Environment) (opts : Options) (path : String) : IO Environment := do
  let inputCtx := Parser.mkInputContext (← IO.FS.readFile path) path
  let mut st := Command.mkState env {} opts
  let mut ps : Parser.ModuleParserState := {}
  repeat
    let scope := st.scopes.head!
    let pmctx : Parser.ParserModuleContext := {
      env := st.env, options := scope.opts, currNamespace := scope.currNamespace,
      openDecls := scope.openDecls
    }
    let (cmd, ps', msgs) := Parser.parseCommand inputCtx pmctx ps {}
    ps := ps'
    if msgs.hasErrors then
      throw <| IO.userError s!"parse error in {path}"
    if Parser.isTerminalCommand cmd then
      break
    let ctx : Command.Context := {
      fileName := inputCtx.fileName, fileMap := inputCtx.fileMap, snap? := none, cancelTk? := none
    }
    match ← (Command.elabCommandTopLevel cmd |>.run ctx |>.run st).toBaseIO with
    | .ok (_, st') => st := st'
    | .error _ => throw <| IO.userError s!"exception while elaborating {path}"
  for msg in st.messages.toList do
    if msg.severity matches .error then
      throw <| IO.userError s!"error in {path}: {← msg.data.toString}"
  return st.env

structure Outcome where
  status : String
  detail : String := ""
  output : String := ""
  commands : Nat := 0
  keptRaw : Nat := 0

/-- Mirrors `renderCommand` of `Lean.Fmt.fileMain`; also reports whether the command was kept raw. -/
def renderCommand (ictx : Parser.InputContext) (ctx : Fmt.Context)
    (cmdData prev : Language.Lean.CommandData) : Except Fmt.Error (String × Bool) := do
  if cmdData.stx.isOfKind ``Parser.Command.eoi then
    return (← commandRaw ctx cmdData.stx, false)
  match Fmt.commandMain ctx cmdData.stx (fatal := true) with
  | .error _ => return (← commandRaw ctx cmdData.stx, true)
  | .ok rendering =>
    let some reparsed := Fmt.reparseRendering ictx cmdData prev rendering.rendering
      | return (rendering.rendering, false)
    if (Fmt.checkReparse reparsed rendering).isSome then
      return (← commandRaw ctx cmdData.stx, true)
    return (rendering.rendering, false)

def oneLine (s : String) : String :=
  (s.map fun c => if c == '\n' || c == '\t' then ' ' else c).take 300 |>.toString

def formatFile (baseEnv : Environment) (opts : Options) (file contents : String) : IO Outcome := do
  let inputCtx := Parser.mkInputContext contents file
  let (headerStx, ps0, msgs0) ← Parser.parseHeader inputCtx
  if msgs0.hasErrors then
    return { status := "REFUSED", detail := "parse error in the module header" }
  let st0 := Command.mkState baseEnv {} opts
  let mut st := st0
  let mut ps := ps0
  let mut all : Array Language.Lean.CommandData := #[⟨headerStx, ps0, st0⟩]
  repeat
    let scope := st.scopes.head!
    let pmctx : Parser.ParserModuleContext := {
      env := st.env, options := scope.opts, currNamespace := scope.currNamespace,
      openDecls := scope.openDecls
    }
    let (cmd, ps', msgs) := Parser.parseCommand inputCtx pmctx ps {}
    ps := ps'
    if msgs.hasErrors then
      let mut detail := "parse error"
      for msg in msgs.toList do
        if msg.severity matches .error then
          detail := s!"parse error at {msg.pos.line}:{msg.pos.column}: {← msg.data.toString}"
          break
      return { status := "REFUSED", detail := oneLine detail, commands := all.size - 1 }
    if cmd.isOfKind ``Lean.Parser.Command.open then
      st ← runCmdM inputCtx (openForParsing cmd) st
    else if affectsParsing cmd then
      st ← elabCmd inputCtx cmd (registerOpened cmd st)
    all := all.push ⟨cmd, ps, st⟩
    if Parser.isTerminalCommand cmd then
      break
  let text := inputCtx.fileMap
  let final : Command.State := st
  let rendered : Except Fmt.Error (String × Nat) := do
    let cmdStxs := (all.extract 1 all.size).map (·.stx)
    let modStx ← Fmt.mkModuleSyntax headerStx cmdStxs
    Fmt.validateSyntax text modStx
    let ctx : Fmt.Context := {
      env := final.env
      text
      resolveChoiceNode := fun _ => none
      opts := final.scopes.head!.opts
      lineInfos := Fmt.collectSyntaxLineInfos modStx
    }
    -- The module header is kept as written. The formatter would put every import longer than
    -- 100 columns on a line of its own below the `import` keyword.
    -- A file without `module` and imports has an empty header, which has no raw text.
    let mut out ←
      match commandRaw ctx headerStx with
      | .ok raw => pure raw
      | .error _ => (·.rendering) <$> Fmt.commandMain ctx headerStx (fatal := false)
    let mut keptRaw := 0
    for i in [1:all.size] do
      if let (some cur, some prev) := (all[i]?, all[i - 1]?) then
        let (s, raw) ← renderCommand inputCtx ctx cur prev
        out := out ++ s
        if raw then keptRaw := keptRaw + 1
    return (normalize out, keptRaw)
  match rendered with
  | .error e => return { status := "REFUSED", detail := oneLine (toString e), commands := all.size - 1 }
  | .ok (out, keptRaw) =>
    return {
      status := if out == contents then "SAME" else "OK"
      output := out, commands := all.size - 1, keptRaw
    }

end BatchFmt

open BatchFmt in
unsafe def main (args : List String) : IO UInt32 := do
  let listFile :: srcRoot :: outRoot :: logFile :: timeoutStr :: prelude :: mods := args
    | IO.eprintln "usage: lean --run BatchFmt.lean LIST SRC_ROOT OUT_ROOT LOG TIMEOUT_SECONDS PRELUDE MODULE..."
      return 2
  let timeoutMs := timeoutStr.toNat! * 1000
  let files := (← IO.FS.lines listFile).filter (!·.isEmpty)
  enableInitializersExecution
  let opts := Elab.inServer.set {} true
  let start ← IO.monoMsNow
  let env ← importModules (mods.toArray.map fun m => { module := m.toName }) opts (loadExts := true)
  let env := env.setMainModule .anonymous
  let env ← if prelude == "-" then pure env else loadPrelude env opts prelude
  let log ← IO.FS.Handle.mk logFile .append
  log.putStrLn s!"IMPORTED\t{(← IO.monoMsNow) - start}\t0\t0\t-\t{mods}"
  log.flush
  for rel in files do
    log.putStrLn s!"START\t0\t0\t0\t{rel}\t"
    log.flush
    let t0 ← IO.monoMsNow
    let task ← IO.asTask (prio := .dedicated) do
      let contents ← IO.FS.readFile (System.FilePath.mk srcRoot / rel)
      let outcome ← formatFile env opts rel contents
      if outcome.status == "OK" then
        let dest := System.FilePath.mk outRoot / rel
        if let some dir := dest.parent then IO.FS.createDirAll dir
        IO.FS.writeFile dest outcome.output
      return outcome
    while !(← IO.hasFinished task) do
      if (← IO.monoMsNow) - t0 > timeoutMs then
        log.putStrLn s!"TIMEOUT\t{(← IO.monoMsNow) - t0}\t0\t0\t{rel}\t"
        log.flush
        IO.Process.exit 3
      IO.sleep 2
    let ms := (← IO.monoMsNow) - t0
    match task.get with
    | .ok o => log.putStrLn s!"{o.status}\t{ms}\t{o.commands}\t{o.keptRaw}\t{rel}\t{o.detail}"
    | .error e => log.putStrLn s!"ERROR\t{ms}\t0\t0\t{rel}\t{oneLine (toString e)}"
    log.flush
  return 0
