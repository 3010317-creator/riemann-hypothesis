module
import all Lake
import Lake.DSL
import all Lake.CLI.Main
import all Lake.Build.Run
import all Lake.Build.Index
import all Lake.Build.Module
import all Lake.Load.Workspace
open Lean Lake System

def perfStage (stage : String) : IO Unit := do
  let now ← IO.monoMsNow
  IO.eprintln s!"RH_PERF_STAGE {stage} {now}"

-- Project-owned client: CURRENT stock presetup/build/trace; minimal serialization only.
def minimalSetupBuild (mod : Lake.Module) : FetchM (Job ModuleOutputArtifacts) := do
  let preJob ← mod.presetup.fetch
  preJob.mapM fun pre => do
    if pre.postponeCompile then error "minimal setup requires complete native output mode"
    setTrace pre.trace
    buildAction (← getTrace) mod.traceFile do
      let setup : Lean.ModuleSetup := {
        name := mod.name
        isModule := pre.isModule
        package? := mod.pkg.id?
        imports? := none
        importArts := {}
        dynlibs := pre.dynlibs.map (·.path)
        plugins := pre.plugins.map (·.path)
        options := pre.leanOptions
      }
      let relSrcFile := relPathFrom mod.pkg.dir pre.srcFile
      let arts := mod.mkArtifacts pre.srcFile pre.isModule
      mod.clearOutputArtifacts
      compileLeanModule pre.srcFile relSrcFile setup mod.setupFile arts
        (mod.weakLeanArgs ++ mod.leanArgs) (← getLeanPath) (← getLean)
      unless pre.srcMTime == (← getMTime pre.srcFile) do
        error "source changed during compilation"
      mod.computeArtifacts setup.isModule false

-- Inspect the ACTUAL current source headers with stock Lake input facets.
-- Only project imports are walked; no dependency proof is built by this check.
def actualLeaseAntichain (ws : Workspace) (names : Array String) : FetchM Bool := do
  let mut wanted : Std.HashSet Name := {}
  let mut targets : Array Lake.Module := #[]
  for name in names do
    let moduleName := if name.startsWith "+" then (name.drop 1).toString else name
    let some mod := ws.findModule? moduleName.toName | return false
    if mod.pkg.name != `tree then return false
    wanted := wanted.insert mod.name
    targets := targets.push mod
  if wanted.size != names.size then return false
  let mut pending : Array Lake.Module := #[]
  for mod in targets do
    let imports ← (← mod.imports.fetch).await
    pending := pending ++ imports.filter (fun imp => imp.pkg.name == `tree)
  let mut visited : Std.HashSet Name := {}
  while !pending.isEmpty do
    let some mod := pending.back? | return false
    pending := pending.pop
    if wanted.contains mod.name then return false
    if !visited.contains mod.name then
      visited := visited.insert mod.name
      let imports ← (← mod.imports.fetch).await
      pending := pending ++ imports.filter (fun imp => imp.pkg.name == `tree)
  return true

def need [FromJson α] (j : Json) (key : String) : IO α := do
  match j.getObjValAs? α key with
  | .ok a => return a
  | .error e => throw (IO.userError e)

def writeJsonAtomic (path : FilePath) (j : Json) : IO Unit := do
  let tmp := path.addExtension "tmp"
  IO.FS.writeFile tmp (j.compress ++ "\n")
  IO.FS.rename tmp path

def verifySnapshot (snapshot : String) : IO Unit := do
  let r ← IO.Process.output {cmd := "python3", args := #["scripts/sharding/verify-snapshot.py",snapshot]}
  unless r.exitCode == 0 do throw (IO.userError ("frozen source verification failed: " ++ r.stderr))

def artifactTool (args : Array String) : IO Json := do
  let r ← IO.Process.output {cmd := "python3", args := #["scripts/sharding/artifact-manifest.py"] ++ args}
  unless r.exitCode == 0 do throw (IO.userError ("artifact helper failed: " ++ r.stderr))
  match Json.parse r.stdout with
  | .ok j => return j
  | .error e => throw (IO.userError e)

def runBatch (ws : Workspace) (bctx : BuildContext) (mctx : MonitorContext)
    (store : BuildStoreRef) (req : Json) (minimal : Bool) : IO Json := do
  let snapshot : String ← need req "snapshot"
  perfStage "source_before:start"
  verifySnapshot snapshot
  perfStage "source_before:end"
  let incoming := (req.getObjValAs? (Array String) "verify").toOption.getD #[]
  unless incoming.isEmpty do
    perfStage "dependency_sha:start"
    discard <| artifactTool (#["verify",".",snapshot] ++ incoming)
    perfStage "dependency_sha:end"
  let names : Array String ← need req "modules"
  if names.isEmpty then
    verifySnapshot snapshot
    return Json.mkObj [("ok",toJson true),("modules",toJson (#[] : Array Json))]
  perfStage "parse_targets:start"
  let specs ← (parseTargetSpecs ws names.toList).toIO fun e => IO.userError e.toString
  perfStage "parse_targets:end"
  let requested ← IO.mkRef (#[] : Array OpaqueJob)
  let build : FetchM (Job Unit) := do
    perfStage "register_jobs:start"
    let useMinimal ← if minimal then actualLeaseAntichain ws names else pure false
    IO.eprintln s!"RH_SETUP_MODE {if useMinimal then "minimal-antichain" else "stock-whole-batch"}"
    let jobs ← if useMinimal then names.mapM fun name => do
      let moduleName := if name.startsWith "+" then (name.drop 1).toString else name
      let some mod := ws.findModule? moduleName.toName | error s!"unknown project module {moduleName}"
      unless mod.pkg.name == `tree do error "minimal setup is restricted to project modules"
      let job ← withCurrPackage mod.pkg <| minimalSetupBuild mod
      pure job.toOpaque
    else specs.mapM (·.build)
    perfStage "register_jobs:end"
    requested.set jobs
    return Job.mixArray jobs
  let compute := Job.async build
  let job ← (compute.run none {} store bctx).run nilTrace
  perfStage "monitor_build:start"
  let result ← monitorBuild mctx job
  perfStage "monitor_build:end"
  perfStage "source_after:start"
  verifySnapshot snapshot
  perfStage "source_after:end"
  let jobs ← requested.get
  perfStage "requested_rows:start"
  let mut rows : Array Json := #[]
  for i in [:names.size] do
    let row ← if let some j := jobs[i]? then do
      let r := j.task.get
      let good := match r with | .ok .. => true | .error .. => false
      pure <| Json.mkObj [("module",toJson names[i]!), ("ok",toJson good),
        ("build_ms",toJson r.state.buildTime), ("action",toJson (repr r.state.action).pretty)]
    else
      pure <| Json.mkObj [("module",toJson names[i]!), ("ok",toJson false),
        ("error",toJson "no requested job returned")]
    rows := rows.push row
  perfStage "requested_rows:end"
  return Json.mkObj [("ok",toJson result.isOk), ("modules",toJson rows)]

public def main (args : List String) : IO UInt32 := do
  let [directory, snapshot, once] := args
    | throw (IO.userError "expected request-directory snapshot-id once-or-loop")
  let minimal := (← IO.getEnv "RH_MINIMAL_SETUP") == some "1"
  let dir : FilePath := directory
  IO.FS.createDirAll dir
  initSearchPath (← findSysroot)
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let opts : LakeOptions := {
    elanInstall? := elanInstall?
    leanInstall? := leanInstall?
    lakeInstall? := lakeInstall?
    rootDir := "."
    configFile := "lakefile.toml"
    updateToolchain := false
  }
  let loadCfg ← opts.mkLoadConfig.toIO fun e => IO.userError e.toString
  perfStage "workspace_load:start"
  let some ws ← (loadWorkspace loadCfg).toBaseIO
    | throw (IO.userError "workspace load failed")
  perfStage "workspace_load:end"
  let cfg : BuildConfig := {
    trustHash := false
    verbosity := .quiet
    outLv := .error
    outputsFile? := none
  }
  let jobs ← mkJobQueue
  let mctx ← mkMonitorContext cfg jobs
  let bctx ← mkBuildContext ws cfg jobs
  let store ← BuildStoreRef.new
  writeJsonAtomic (dir / "ready.json") <| Json.mkObj [ ("snapshot",toJson snapshot),
    ("lean_version",toJson Lean.versionString), ("worker",toJson (if minimal then "stockLakepersistent-minimal-setup-v1" else "stockLakepersistent" : String))]
  let mut index := 0
  while (← (dir / s!"response-{index}.json").pathExists) do
    index := index+1
  repeat
    if ← (dir / "stop").pathExists then break
    let reqPath := dir / s!"request-{index}.json"
    if !(← reqPath.pathExists) then
      IO.sleep 500
      continue
    let req ← match Json.parse (← IO.FS.readFile reqPath) with
      | .ok j => pure j
      | .error e => throw (IO.userError e)
    let gotSnapshot : String ← need req "snapshot"
    unless gotSnapshot == snapshot do throw (IO.userError "snapshot mismatch")
    IO.eprintln s!"RH_SHARD_BATCH_START {index}"
    let start ← IO.monoMsNow
    let response ← try runBatch ws bctx mctx store req minimal catch e =>
      pure <| Json.mkObj [("ok",toJson false),("error",toJson e.toString)]
    let stop ← IO.monoMsNow
    let rawPath := dir / s!"result-{index}.json"
    writeJsonAtomic rawPath response
    perfStage "outgoing_artifact_manifest:start"
    let artifactInfo ← artifactTool #["create",".",snapshot,rawPath.toString,(dir / s!"artifacts-{index}.json").toString]
    perfStage "outgoing_artifact_manifest:end"
    let response := Json.mkObj [("snapshot",toJson snapshot),("batch",toJson index),
      ("elapsed_ms",toJson (stop-start)),("result",response),("artifacts",artifactInfo)]
    writeJsonAtomic (dir / s!"response-{index}.json") response
    IO.eprintln s!"RH_SHARD_BATCH_END {index}"
    index := index+1
    if once == "once" then break
  return 0
