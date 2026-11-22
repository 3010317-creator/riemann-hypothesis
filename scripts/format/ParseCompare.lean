import Lean

/-!
Checks that a reformatted Lean file still reads the same way under the toolchain it is meant for.

For every path in LIST it parses `ORIG_ROOT/path` and `FMT_ROOT/path` command by command, in the
environment of the given modules (imported once), and compares the two syntax trees: the same
node kinds, atoms and identifiers in the same order. Source positions and whitespace are ignored,
and so is the `;` separator, which the formatter may replace by a line break.

As in the formatter driver, only the commands that can change parsing are elaborated, and `open`
tolerates namespaces that only the project declares.

usage: lean --run ParseCompare.lean LIST ORIG_ROOT FMT_ROOT LOG PRELUDE MODULE...

LOG gets one tab-separated line per file: `STATUS  path  detail`, where STATUS is
`SAME`, `DIFF`, `ORIG_ERROR` (the original does not parse here) or `FMT_ERROR`.
-/

open Lean Elab

namespace ParseCompare

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

def cmdCtx (inputCtx : Parser.InputContext) : Command.Context :=
  { fileName := inputCtx.fileName, fileMap := inputCtx.fileMap, snap? := none, cancelTk? := none }

def runCmdM (inputCtx : Parser.InputContext) (x : Command.CommandElabM Unit) (st : Command.State)
    : BaseIO Command.State := do
  match ← (x.run (cmdCtx inputCtx) |>.run st).toBaseIO with
  | .ok (_, st') => return { st' with messages := {} }
  | .error _ => return st

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

def registerOpened (cmd : Syntax) (st : Command.State) : Command.State := Id.run do
  let scope := st.scopes.head!
  let mut env := st.env
  for n in openedNamespaces cmd do
    if !n.isAnonymous &&
        (ResolveName.resolveNamespace env scope.currNamespace scope.openDecls n).isEmpty then
      env := env.registerNamespace n
  return { st with env }

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

def pmctxOf (st : Command.State) : Parser.ParserModuleContext :=
  let scope := st.scopes.head!
  { env := st.env, options := scope.opts, currNamespace := scope.currNamespace,
    openDecls := scope.openDecls }

def loadPrelude (env : Environment) (opts : Options) (path : String) : IO Environment := do
  let inputCtx := Parser.mkInputContext (← IO.FS.readFile path) path
  let mut st := Command.mkState env {} opts
  let mut ps : Parser.ModuleParserState := {}
  repeat
    let (cmd, ps', msgs) := Parser.parseCommand inputCtx (pmctxOf st) ps {}
    ps := ps'
    if msgs.hasErrors then
      throw <| IO.userError s!"parse error in {path}"
    if Parser.isTerminalCommand cmd then
      break
    match ← (Command.elabCommandTopLevel cmd |>.run (cmdCtx inputCtx) |>.run st).toBaseIO with
    | .ok (_, st') => st := st'
    | .error _ => throw <| IO.userError s!"exception while elaborating {path}"
  for msg in st.messages.toList do
    if msg.severity matches .error then
      throw <| IO.userError s!"error in {path}: {← msg.data.toString}"
  return st.env

def oneLine (s : String) : String :=
  String.ofList <| (s.toList.map fun c => if c == '\n' || c == '\t' then ' ' else c).take 240

/-- The header and the commands of a file, or the first parse error. -/
def parseFile (baseEnv : Environment) (opts : Options) (file contents : String)
    : IO (Except String (Array Syntax)) := do
  let inputCtx := Parser.mkInputContext contents file
  let (headerStx, ps0, msgs0) ← Parser.parseHeader inputCtx
  if msgs0.hasErrors then
    return .error "parse error in the module header"
  let mut st := Command.mkState baseEnv {} opts
  let mut ps := ps0
  let mut cmds : Array Syntax := #[headerStx]
  repeat
    let (cmd, ps', msgs) := Parser.parseCommand inputCtx (pmctxOf st) ps {}
    ps := ps'
    if msgs.hasErrors then
      for msg in msgs.toList do
        if msg.severity matches .error then
          return .error (oneLine s!"{msg.pos.line}:{msg.pos.column}: {← msg.data.toString}")
      return .error "parse error"
    if cmd.isOfKind ``Lean.Parser.Command.open then
      st ← runCmdM inputCtx (openForParsing cmd) st
    else if affectsParsing cmd then
      st ← runCmdM inputCtx (Command.elabCommandTopLevel cmd) (registerOpened cmd st)
    cmds := cmds.push cmd
    if Parser.isTerminalCommand cmd then
      break
  return .ok cmds

/--
The node kinds, atoms and identifiers of a syntax tree in preorder. `null` nodes are left out, and
so are the two separators that the formatter may replace by a line break: the atom `;`, and the
`,` between the fields of a structure instance. A separator that is absent is an empty `null` node.
-/
partial def flatten (stx : Syntax) (acc : Array String) : Array String :=
  match stx with
  | .missing => acc.push "<missing>"
  | .atom _ val => if val == ";" then acc else acc.push ("a:" ++ val)
  | .ident _ _ val _ => acc.push ("i:" ++ toString val)
  | .node _ kind args =>
    let acc := if kind == nullKind then acc else acc.push ("k:" ++ toString kind)
    if kind == ``Lean.Parser.Term.structInstFields then
      -- The one child is the list of fields and separators.
      args.foldl (init := acc) fun acc list =>
        list.getArgs.foldl (init := acc) fun acc arg =>
          if arg.isAtom && arg.getAtomVal == "," then acc else flatten arg acc
    else
      args.foldl (init := acc) fun acc arg => flatten arg acc

def compare (orig fmt : Array Syntax) : Option String := Id.run do
  let a := orig.foldl (init := #[]) fun acc s => flatten s acc
  let b := fmt.foldl (init := #[]) fun acc s => flatten s acc
  if a == b then
    return none
  let n := min a.size b.size
  for i in [0:n] do
    if a[i]! != b[i]! then
      return some (oneLine s!"item {i} of {a.size}/{b.size}: {a[i]!} vs {b[i]!}")
  return some s!"same first {n} items, lengths {a.size} vs {b.size}"

end ParseCompare

open ParseCompare in
unsafe def main (args : List String) : IO UInt32 := do
  let listFile :: origRoot :: fmtRoot :: logFile :: prelude :: mods := args
    | IO.eprintln "usage: lean --run ParseCompare.lean LIST ORIG_ROOT FMT_ROOT LOG PRELUDE MODULE..."
      return 2
  let files := (← IO.FS.lines listFile).filter (!·.isEmpty)
  enableInitializersExecution
  let opts : Options := {}
  let env ← importModules (mods.toArray.map fun m => { module := m.toName }) opts (loadExts := true)
  let env := env.setMainModule .anonymous
  let env ← if prelude == "-" then pure env else loadPrelude env opts prelude
  let log ← IO.FS.Handle.mk logFile .append
  log.putStrLn s!"IMPORTED\t-\t{mods}"
  log.flush
  for rel in files do
    let line ← try
      let orig ← IO.FS.readFile (System.FilePath.mk origRoot / rel)
      let fmt ← IO.FS.readFile (System.FilePath.mk fmtRoot / rel)
      match ← parseFile env opts rel orig with
      | .error e => pure s!"ORIG_ERROR\t{rel}\t{e}"
      | .ok a =>
        match ← parseFile env opts rel fmt with
        | .error e => pure s!"FMT_ERROR\t{rel}\t{e}"
        | .ok b =>
          match compare a b with
          | none => pure s!"SAME\t{rel}\t"
          | some d => pure s!"DIFF\t{rel}\t{d}"
    catch e => pure s!"IO_ERROR\t{rel}\t{oneLine (toString e)}"
    log.putStrLn line
    log.flush
  return 0
