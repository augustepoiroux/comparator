/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean
import Comparator
import Export.Parse

namespace Comparator

structure Context where
  projectDir : System.FilePath
  challengeModule : Lean.Name
  solutionModule : Lean.Name
  theoremNames : Array Lean.Name
  definitionNames : Array Lean.Name
  legalAxioms : Array Lean.Name
  leanPrefix : System.FilePath
  gitLocation : System.FilePath
  allowDisproofs : Bool
  autoDiscover : Bool
  whichLandrun : String
  whichLean4Export : String
  externalKernels : Std.TreeMap String (Array String)
  mustResolveAllSorries : Bool
  jsonOutputPath : Option String

abbrev M := ReaderT Context IO

structure LandrunArgs where
  cmd : String
  args : Array String
  envPass : Array String
  envOverride : Array (String × Option String) := #[]
  readablePaths : Array System.FilePath
  writablePaths : Array System.FilePath
  executablePaths : Array System.FilePath

@[inline]
def getExternalKernels : M (Std.TreeMap String (Array String)) := do return (← read).externalKernels

@[inline]
def getTheoremNames : M (Array Lean.Name) := do return (← read).theoremNames

@[inline]
def getDefinitionNames : M (Array Lean.Name) := do return (← read).definitionNames

@[inline]
def getProjectDir : M System.FilePath := do return (← read).projectDir

@[inline]
def getChallengeModule : M Lean.Name := do return (← read).challengeModule

@[inline]
def getSolutionModule : M Lean.Name := do return (← read).solutionModule

@[inline]
def getLegalAxioms : M (Array Lean.Name) := do return (← read).legalAxioms

@[inline]
def getLeanPrefix : M System.FilePath := do return (← read).leanPrefix

@[inline]
def getGitLocation : M System.FilePath := do return (← read).gitLocation

@[inline]
def getAllowDisproofs : M Bool := do return (← read).allowDisproofs

@[inline]
def getAutoDiscover : M Bool := do return (← read).autoDiscover

def queryGitLocation : IO System.FilePath := do
  let out ← IO.Process.run {
    cmd := "which",
    args := #["git"],
    stdout := .piped,
  }
  return out.trimAscii.toString

def queryLeanPrefix (projectDir : System.FilePath) : IO System.FilePath := do
  let out ← IO.Process.run {
    cmd := "lean",
    args := #["--print-prefix"],
    stdout := .piped,
    cwd := projectDir
  }
  return out.trimAscii.toString

def buildLandrunArgs (spawnArgs : LandrunArgs) : Array String :=
  let args := #["--best-effort", "--ro", "/", "--rw", "/dev", "-ldd", "-add-exec"]
  let args := spawnArgs.envPass.foldl (init := args) (fun acc env => acc ++ #["--env", env])
  let args := spawnArgs.readablePaths.foldl (init := args) (fun acc path => acc ++ #["--ro", path.toString])
  let args := spawnArgs.writablePaths.foldl (init := args) (fun acc path => acc ++ #["--rwx", path.toString])
  let args := spawnArgs.executablePaths.foldl (init := args) (fun acc path => acc ++ #["--rox", path.toString])
  args ++ #["--", spawnArgs.cmd] ++ spawnArgs.args

def runSandBoxedWithStdout (spawnArgs : LandrunArgs) : M String := do
  let args := buildLandrunArgs spawnArgs
  let { stdout, stderr, exitCode } ← IO.Process.output {
    cmd := (← read).whichLandrun,
    args,
    env := spawnArgs.envOverride
    cwd := (← getProjectDir)
  }
  IO.eprint stderr
  if exitCode != 0 then
    throw <| .userError s!"Child exited with {exitCode}"
  return stdout


def runSandBoxed (spawnArgs : LandrunArgs) : M Unit := do
  let args := buildLandrunArgs spawnArgs
  let proc ← IO.Process.spawn {
    cmd := (← read).whichLandrun,
    args,
    env := spawnArgs.envOverride
    cwd := (← getProjectDir)
  }
  let ret ← proc.wait
  if ret != 0 then
    throw <| .userError s!"Child exited with {ret}"

def safeLakeBuild (target : Lean.Name) : M Unit := do
  IO.println s!"Building {target}"
  let leanPrefix ← getLeanPrefix
  let projectDir ← getProjectDir
  let dotLakeDir := projectDir / ".lake"
  let gitLocation ← getGitLocation

  if !(← System.FilePath.pathExists dotLakeDir) then
    IO.FS.createDir dotLakeDir

  runSandBoxed {
    cmd := "lake",
    args := #["build", target.toString],
    envPass := #["PATH", "HOME", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    readablePaths := #[projectDir]
    writablePaths := #[dotLakeDir]
    executablePaths := #[leanPrefix, gitLocation]
  }

def runExternalKernel (kernelName : String) (kernelCommand : Array String)
    (solutionExport : String) : M (Option String) := do
  IO.println s!"Running {kernelName} kernel on solution"
  -- just always put out a nanoda-like config file for now
  IO.FS.withTempFile fun configHandle configPath => do
  IO.FS.withTempFile fun solutionHandle solutionPath => do

    let legalAxioms ← getLegalAxioms
    configHandle.putStr <| Lean.Json.compress <| Lean.Json.mkObj [
      ("use_stdin", false),
      ("export_file_path", solutionPath.toString),
      ("permitted_axioms", .arr <| legalAxioms.map (.str ∘ Lean.Name.toString)),
      ("unpermitted_axiom_hard_error", true),
      ("num_threads", 4),
      ("nat_extension", true),
      ("string_extension", true),
    ]
    configHandle.flush

    solutionHandle.putStr solutionExport
    solutionHandle.flush

    let mut kernelArgs := kernelCommand[1...*].toArray
    if isNanodaKernel kernelName then
      kernelArgs := kernelArgs.push configPath.toString
    else
      kernelArgs := kernelArgs.push solutionPath.toString

    let spawnArgs := {
      cmd := kernelCommand[0]!,
      args := kernelArgs,
      envPass := #[]
      readablePaths := #[configPath.toString, solutionPath.toString]
      writablePaths := #[]
      executablePaths := #[]
    }
    let args := buildLandrunArgs spawnArgs

    try
      let proc ← IO.Process.spawn {
        cmd := (← read).whichLandrun,
        args,
        env := spawnArgs.envOverride
        cwd := (← getProjectDir)
      }

      let ret ← proc.wait
      if ret != 0 then
        IO.println s!"{kernelName} kernel rejected the solution"
        return some s!"{kernelName} exited with {ret}"
      else
        IO.println s!"{kernelName} kernel accepts the solution"
        return none
    catch e => do
      IO.println s!"Error while interacting with {kernelName} kernel"
      return some s!"Error while interacting with {kernelName} kernel: {e.toString}"
where
  isNanodaKernel (kernelName : String) : Bool :=
    -- TODO: get rid of this heuristic
    kernelName.contains "noda"

namespace Replay

/-- Why a declaration is missing from the replayed environment. -/
inductive Failure where
  /-- The kernel rejected the declaration itself. -/
  | kernel (message : String)
  /-- A dependency was rejected synchronously, so the declaration was never offered to the kernel. -/
  | dependency (of : Lean.Name)
  deriving Inhabited

structure State where
  env : Lean.Kernel.Environment
  remaining : Lean.NameSet := {}
  pending : Lean.NameSet := {}
  /-- Declarations that are not (validly) in `env`. Replay never aborts on a kernel error: it records
  it here and carries on with everything that does not depend on the rejected declaration, so that
  every target gets its own verdict. -/
  failed : Std.HashMap Lean.Name Failure := {}
  postponedConstructors : Lean.NameSet := {}
  postponedRecursors : Lean.NameSet := {}
  thmTasks : Array (Lean.Name × Task (Except Lean.Kernel.Exception Unit)) := #[]

abbrev M := ReaderT (Std.HashMap Lean.Name Lean.ConstantInfo) <| StateRefT State IO

def fail (name : Lean.Name) (failure : Failure) : M Unit :=
  modify fun s => { s with failed := s.failed.insert name failure, pending := s.pending.erase name }

def failKernel (name : Lean.Name) (ex : Lean.Kernel.Exception) : M Unit := do
  fail name (.kernel (← (ex.toMessageData {}).toString))

def addDecl (name : Lean.Name) (d : Lean.Declaration) : M Unit := do
  match (← get).env.addDeclCore 0 0 d none with
  | .ok env => modify ({ · with env })
  | .error ex => failKernel name ex

partial def replayConstant (name : Lean.Name) : M Unit := do
  if (← get).remaining.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    let some ci := (← read)[name]? | unreachable!
    let deps := ci.getUsedConstantsAsSet
    for n in deps do replayConstant n
    -- A synchronously rejected dependency is absent from `env`, so offering `name` to the kernel could
    -- only produce a misleading "unknown constant" error. Theorems rejected asynchronously are already
    -- in `env`; `runBuiltinKernel` attributes those through the dependency closure instead.
    let failed := (← get).failed
    if let some d := deps.toList.find? failed.contains then
      return ← fail name (.dependency d)
    if (← get).pending.contains name then
      match ci with
      | .defnInfo info => addDecl name (.defnDecl info)
      | .thmInfo info =>
        let snapEnv := (← get).env
        match snapEnv.addDeclCore 0 0 (.axiomDecl ⟨info.toConstantVal, false⟩) none with
        | .error ex => failKernel name ex
        | .ok _ =>
          match snapEnv.addDeclWithoutChecking (.thmDecl info) with
          | .error ex => failKernel name ex
          | .ok env =>
            let task := Task.spawn fun () =>
              snapEnv.addDeclCore 0 0 (.thmDecl info) none |>.map fun _ => ()
            modify fun s => { s with env, thmTasks := s.thmTasks.push (name, task) }
      | .axiomInfo info => addDecl name (.axiomDecl info)
      | .opaqueInfo info => addDecl name (.opaqueDecl info)
      | .inductInfo info =>
        let all ← info.all.mapM fun n => return (← read)[n]!
        for o in all do
          modify fun s => { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
        let ctorInfo ← all.mapM fun ci => return (ci, ← ci.inductiveVal!.ctors.mapM fun n => return (← read)[n]!)
        for (_, ctors) in ctorInfo do
          for ctor in ctors do
            for n in ctor.getUsedConstantsAsSet do replayConstant n
        addDecl name (.inductDecl info.levelParams info.numParams (ctorInfo.map fun ⟨ci, ctors⟩ =>
          { name := ci.name, type := ci.type, ctors := ctors.map fun c => { name := c.name, type := c.type } }) false)
        -- The whole block stands or falls together.
        if let some failure := (← get).failed[name]? then
          for o in all do fail o.name failure
      | .ctorInfo info => modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
      | .recInfo info => modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
      | .quotInfo _ => replayConstant `Eq; addDecl name .quotDecl
      modify fun s => { s with pending := s.pending.erase name }

/-- Replays `newConstants` into `env`. Returns the final environment together with every declaration
that is not validly in it and why. -/
def replay (newConstants : Std.HashMap Lean.Name Lean.ConstantInfo) (env : Lean.Kernel.Environment) :
    IO (Lean.Kernel.Environment × Std.HashMap Lean.Name Failure) := do
  let remaining := newConstants.fold (init := (∅ : Lean.NameSet)) fun acc n ci =>
    if !ci.isUnsafe && !ci.isPartial then acc.insert n else acc
  let (_, s) ← StateRefT'.run (s := { env, remaining }) <| ReaderT.run (r := newConstants) do
    for n in #[``Nat, ``Char.ofNat, ``String.ofList] do replayConstant n
    for n in remaining do replayConstant n
    for (name, task) in (← get).thmTasks do
      if let .error ex := task.get then failKernel name ex
    -- Constructors and recursors are generated by the kernel from the inductive declaration; they must
    -- agree with the export unless their inductive type was rejected.
    for ctor in (← get).postponedConstructors do
      let some (.ctorInfo i') := (← read)[ctor]? | unreachable!
      match (← get).env.find? ctor, (← get).failed[i'.induct]? with
      | _, some failure => fail ctor failure
      | some (.ctorInfo i), none => unless i == i' do fail ctor (.kernel s!"Invalid constructor {ctor}")
      | _, none => fail ctor (.kernel s!"No such constructor {ctor}")
    for rec in (← get).postponedRecursors do
      let some (.recInfo i') := (← read)[rec]? | unreachable!
      let failed := (← get).failed
      match (← get).env.find? rec, i'.all.findSome? (failed[·]?) with
      | _, some failure => fail rec failure
      | some (.recInfo i), none => unless i == i' do fail rec (.kernel s!"Invalid recursor {rec}")
      | _, none => fail rec (.kernel s!"No such recursor {rec}")
  return (s.env, s.failed)

end Replay

/-- Replays the solution into a fresh kernel environment. Returns a global error (nothing can be trusted)
or the declarations that are not validly in the final environment; see `kernelRejections`. -/
def runBuiltinKernel (solution : Export.ExportedEnv) (targets : Array Lean.Name := #[]) :
    M (Except String (Std.HashMap Lean.Name Replay.Failure)) := do
  IO.println "Running Lean default kernel on solution."
  let env ← Lean.mkEmptyEnvironment
  let origConstMap := solution.constMap
  -- Lean's kernel interprets just the addition of `Quot as adding all of these so adding them
  -- multiple times leads to errors.
  let quotTargets := [`Quot.mk, `Quot.lift, `Quot.ind]
  let kernelConstMap := quotTargets.foldl (init := origConstMap) (·.erase ·)
  let (kernelEnv, failed) ← Replay.replay kernelConstMap env.toKernelEnv

  -- Every exported constant must be either bit-identical in the final env or recorded as rejected;
  -- anything else means the replay did not do what we think it did, so nothing can be trusted.
  -- `Quot*` and `targets` come first only to keep the error message stable.
  let verifyTargets := #[`Quot] ++ quotTargets.toArray ++ targets ++ origConstMap.keysArray
  for name in verifyTargets.filter origConstMap.contains do
    if !failed.contains name && kernelEnv.find? name != origConstMap[name]? then
      IO.println "Lean default kernel post-check rejects the solution"
      return .error s!"Constant mismatch in final kernel env on: {name}"
  return .ok failed

def primitiveTargets : M (Array Lean.Name) := do
  -- The challenge needs to have all the built-in constants of the kernel, as the
  -- kernel makes no guarantees when fed other definitions here.
  -- List from `git grep new_persistent_expr_const src/kernel/`
  return #[
    -- ``Nat.zero,
    -- ``Nat.succ,
    ``Nat.add,
    ``Nat.sub,
    ``Nat.mul,
    ``Nat.pow,
    ``Nat.gcd,
    ``Nat.div,
    ``Nat.mod,
    ``Nat.beq,
    ``Nat.ble,
    ``Nat.land,
    ``Nat.lor,
    ``Nat.xor,
    ``Nat.shiftLeft,
    ``Nat.shiftRight,
    ``String.ofList,
    ``Char.ofNat,
    ``List,
    ``eagerReduce,
    ``Nat,
    ``String,
    ``String.mk,
    ``Char,
    ``optParam,
    ``autoParam,
    ``semiOutParam,
    ``outParam
  ]

def builtinTargets : M (Array Lean.Name) := do
  let mut additional := #[]
  if (← getLegalAxioms).contains ``Quot.sound then
    additional := additional ++ #[``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]
  if ← getAllowDisproofs then
    additional := additional ++ #[``False, ``Not]
  return additional

def nameToOleanPath (projectDir : System.FilePath) (name : Lean.Name) : System.FilePath :=
  let components := name.components.map (·.toString (escape := false))
  components.foldl (· / ·) (projectDir / ".lake" / "build" / "lib" / "lean") |>.withExtension "olean"

def getWhichQueryDecls : M String := do
  let queryDeclsPath := (← IO.appPath).parent.getD "" / "query_decls"
  match ← IO.getEnv "COMPARATOR_QUERY_DECLS" with
  | some path => pure path
  | none => try pure (← IO.FS.realPath queryDeclsPath).toString catch _ => pure "query_decls"

def runQueryDecls (module : Lean.Name) : M (Array Lean.Name × Array Lean.Name) := do
  let projectDir ← getProjectDir
  let oleanPath := nameToOleanPath projectDir module
  let whichQueryDecls ← getWhichQueryDecls

  let stdout ← runSandBoxedWithStdout {
    cmd := whichQueryDecls,
    args := #[oleanPath.toString],
    envPass := #["PATH", "HOME", "LEAN_PATH", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    readablePaths := #[projectDir, projectDir / ".lake", whichQueryDecls]
    writablePaths := #[]
    executablePaths := #[whichQueryDecls]
  }

  let json ← IO.ofExcept <| Lean.Json.parse stdout
  IO.ofExcept <| Lean.FromJson.fromJson? json

def exportLandrunArgs (module : Lean.Name) (decls : Array Lean.Name) (ignoreMissing : Bool := true)
    (omitThmProofs : Bool := false) : M LandrunArgs := do
  IO.println s!"Exporting {decls} from {module}"

  let flagArgs := if ignoreMissing then #["--ignore-missing", module.toString] else #[module.toString]
  let args :=
    if decls.isEmpty then
      flagArgs
    else
      decls.foldl (·.push <| ·.toString) (flagArgs.push "--")

  let leanPrefix ← getLeanPrefix
  let projectDir ← getProjectDir
  let dotLakeDir := projectDir / ".lake"
  if omitThmProofs then
    let whichQueryDecls ← getWhichQueryDecls
    let omitArgs := if decls.isEmpty then #[module.toString] else decls.foldl (·.push <| ·.toString) #[module.toString, "--"]
    return {
      cmd := whichQueryDecls
      args := #["export-omit-proofs"] ++ omitArgs,
      envPass := #["PATH", "HOME", "LEAN_PATH", "LEAN_ABORT_ON_PANIC"]
      envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
      readablePaths := #[projectDir, dotLakeDir, whichQueryDecls]
      writablePaths := #[]
      executablePaths := #[leanPrefix, whichQueryDecls]
    }
  else
    return {
      cmd := (← read).whichLean4Export
      args := args,
      envPass := #["PATH", "HOME", "LEAN_PATH", "LEAN_ABORT_ON_PANIC"]
      envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
      readablePaths := #[projectDir, dotLakeDir]
      writablePaths := #[]
      executablePaths := #[leanPrefix]
    }

def safeExport (module : Lean.Name) (decls : Array Lean.Name) (ignoreMissing : Bool := true)
    (omitThmProofs : Bool := false) : M String := do
  runSandBoxedWithStdout (← exportLandrunArgs module decls ignoreMissing omitThmProofs)

def drainHandle (h : IO.FS.Handle) : IO Unit := do
  try while !(← h.read 65536).isEmpty do pure () catch _ => pure ()

def safeExportAndParse (module : Lean.Name) (decls : Array Lean.Name) : M Export.ExportedEnv := do
  let spawnArgs ← exportLandrunArgs module decls
  let proc ← IO.Process.spawn {
    cmd := (← read).whichLandrun,
    args := buildLandrunArgs spawnArgs,
    env := spawnArgs.envOverride,
    cwd := (← getProjectDir),
    stdout := .piped,
    stderr := .piped
  }
  let stderrTask ← IO.asTask proc.stderr.readToEnd Task.Priority.dedicated
  let res ← try
    let env ← Comparator.Parse.parseStream (IO.FS.Stream.ofHandle proc.stdout)
    drainHandle proc.stdout
    pure (.ok env)
  catch e =>
    drainHandle proc.stdout
    pure (.error e)
  IO.eprint (← IO.ofExcept stderrTask.get)
  let exitCode ← proc.wait
  if exitCode != 0 then
    throw <| .userError s!"Child exited with {exitCode}"
  IO.ofExcept res

def exportSolution (module : Lean.Name) (decls : Array Lean.Name) : M (String × Export.ExportedEnv) := do
  if (← getExternalKernels).isEmpty then
    return ("", ← safeExportAndParse module decls)
  else
    let exp ← safeExport module decls
    return (exp, ← Comparator.Parse.parse exp)

def parseChallenge (challengeExport : String) (theoremNames definitionNames : Array Lean.Name) :
    IO Export.ExportedEnv := do
  let challenge ← Comparator.Parse.parse challengeExport
  for t in theoremNames do
    unless challenge.constMap.contains t do
      throw <| IO.userError s!"Challenge does not contain the configured theorem target '{t}'"
  for d in definitionNames do
    unless challenge.constMap.contains d do
      throw <| IO.userError s!"Challenge does not contain the configured definition target '{d}'"
  return challenge

@[inline]
def getMustResolveAllSorries : M Bool := do return (← read).mustResolveAllSorries

@[inline]
def getJsonOutputPath : M (Option String) := do return (← read).jsonOutputPath

def constKind : Lean.ConstantInfo → String
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

instance : Lean.ToJson Lean.ConstantInfo where
  toJson ci := Lean.Json.mkObj [("kind", constKind ci)]

inductive TheoremMode where
  | direct
  | disproof
  deriving BEq, Inhabited, Lean.ToJson, Repr

inductive CheckFailure where
  | kind (kind1 kind2 : String)
  | thmType
  | disproofType
  | defnCheck
  | axioms
  | notFound
  /-- The target passed the statement and axiom checks, but `kernel` (`lean`, or an entry of
  `external_kernels`) rejected it. For `lean` this is per target and `message` names the rejected
  declaration, which may be a dependency shared with other targets; external kernels only report a
  verdict for the whole solution, so a rejection marks every target that was still accepted. -/
  | kernel (kernel message : String)
  /-- The re-export restricted to the accepted targets disagreed with the checked export. Marks every
  target that was still accepted. -/
  | reexport (message : String)
  deriving Lean.ToJson, Inhabited, Repr

structure Info where
  constInfo : Lean.ConstantInfo
  axioms : Array Lean.Name
  deriving Lean.ToJson, Inhabited

structure VerificationOutcome where
  targetInfo : Info
  solutionInfo : Option Info
  failureMode : Option CheckFailure
  mode : Option TheoremMode := none
  solutionName : Option Lean.Name := none
  deriving Inhabited

/-- Like the derived instance, plus `verified`: the attempt passed every phase, including the kernel
replay. Reports are only written after that phase (or with every clean attempt marked), so this is exactly
`failureMode == none`. -/
instance : Lean.ToJson VerificationOutcome where
  toJson o := Lean.Json.mkObj [
    ("verified", o.failureMode.isNone), ("targetInfo", Lean.toJson o.targetInfo),
    ("solutionInfo", Lean.toJson o.solutionInfo), ("failureMode", Lean.toJson o.failureMode),
    ("mode", Lean.toJson o.mode), ("solutionName", Lean.toJson o.solutionName)]

/-- The JSON verification report written to `json_output_path`. `accepted` is `true` if and only if the
run succeeded; it is the only success signal, since with `must_resolve_all_sorries: false` an accepted
run may contain failed targets and a rejected run may contain verified ones. `error` is the message the
run was rejected with. -/
structure Report where
  accepted : Bool
  error : Option String := none
  outcomes : Array (Lean.Name × VerificationOutcome) := #[]
  deriving Lean.ToJson

def writeReport (report : Report) : M Unit := do
  let some path ← getJsonOutputPath | return
  -- Atomic, so a consumer can never observe a partially written report.
  let tmp := path ++ ".tmp"
  IO.FS.writeFile tmp (Lean.Json.compress (Lean.ToJson.toJson report))
  IO.FS.rename tmp path

def disproofName (n : Lean.Name) : Lean.Name := n ++ `disproof

abbrev DepM := StateM (Std.HashSet Lean.Name)

partial def collectDeps (env : Export.ExportedEnv) (n : Lean.Name) : DepM Unit := do
  if (← get).contains n then
    return
  modify (·.insert n)
  if let some info := env.constMap[n]? then
    runForUsedConsts info (collectDeps env)

def getAxioms (env : Export.ExportedEnv) (n : Lean.Name) : Array Lean.Name :=
  let (_, deps) := (collectDeps env n).run {}
  deps.toArray.filter fun dep => match env.constMap[dep]? with | some (.axiomInfo _) => true | _ => false

def getInfo (env : Export.ExportedEnv) (n : Lean.Name) : M (Option Info) := do
  let withAxioms := (← getJsonOutputPath).isSome
  return env.constMap[n]?.map fun ci => ⟨ci, if withAxioms then getAxioms env n else #[]⟩

structure VerifyState where
  compareChecked : Std.HashSet Lean.Name := {}
  axiomChecked : Std.HashSet Lean.Name := {}

abbrev VerifyM := StateRefT VerifyState M

def verifyOneTheoremAttempt (challenge solution : Export.ExportedEnv) (t : Lean.Name)
    (solutionName : Lean.Name) (mode : TheoremMode) (targetInfo : Info) (definitionNames : Array Lean.Name) :
    VerifyM VerificationOutcome := do
  let legalAxioms ← getLegalAxioms
  let sInfo := (← getInfo solution solutionName).get!
  let defsToCompare := if definitionNames.isEmpty then #[] else
    let (_, deps) := (collectDeps solution solutionName).run {}
    definitionNames.filter deps.contains

  let typeFailureMode : CheckFailure := match mode with | .direct => .thmType | .disproof => .disproofType

  let fail ←
    match Comparator.compareAt challenge solution #[t] defsToCompare #[] (mode == .disproof) (← get).compareChecked with
    | .error e =>
      IO.println s!"Verification failed for {solutionName}: {e}"
      pure (some typeFailureMode)
    | .ok compareChecked =>
      modify ({ · with compareChecked })
      match Comparator.checkAxioms solution #[solutionName] defsToCompare legalAxioms (← get).axiomChecked with
      | .error e => IO.println s!"Axiom check failed for {solutionName}: {e}"; pure (some .axioms)
      | .ok axiomChecked =>
        modify ({ · with axiomChecked })
        pure none

  return ⟨targetInfo, some sInfo, fail, some mode, some solutionName⟩

def verifyTheorem (challenge solution : Export.ExportedEnv) (t : Lean.Name) (definitionNames : Array Lean.Name) :
    VerifyM (Array (Lean.Name × VerificationOutcome)) := do
  let allowDisproofs ← getAllowDisproofs
  let targetInfo := (← getInfo challenge t).getD ⟨.axiomInfo ⟨⟨t, [], .sort .zero⟩, false⟩, #[]⟩
  let directInfo := solution.constMap[t]?
  let dname := disproofName t
  let disproofInfo := if allowDisproofs then solution.constMap[dname]? else none

  let mut outcomes := #[]

  if let some _ := directInfo then
    outcomes := outcomes.push (t, ← verifyOneTheoremAttempt challenge solution t t .direct targetInfo definitionNames)

  if let some _ := disproofInfo then
    outcomes := outcomes.push (t, ← verifyOneTheoremAttempt challenge solution t dname .disproof targetInfo definitionNames)

  if directInfo.isNone && disproofInfo.isNone then
    outcomes := outcomes.push (t, ⟨targetInfo, none, some .notFound, none, none⟩)

  return outcomes

def verifyDefinition (challenge solution : Export.ExportedEnv) (d : Lean.Name) (definitionNames : Array Lean.Name) :
    VerifyM VerificationOutcome := do
  let legalAxioms ← getLegalAxioms
  let targetInfo := (← getInfo challenge d).getD ⟨.axiomInfo ⟨⟨d, [], .sort .zero⟩, false⟩, #[]⟩
  let some sInfo ← getInfo solution d
    | return ⟨targetInfo, none, some .notFound, none, none⟩

  let tKind := constKind targetInfo.constInfo
  let sKind := constKind sInfo.constInfo
  if tKind != sKind then
    return ⟨targetInfo, some sInfo, some (.kind tKind sKind), none, some d⟩

  let (_, deps) := (collectDeps solution d).run {}
  let defsToCompare := (definitionNames.filter deps.contains).push d

  let fail ←
    match Comparator.compareAt challenge solution #[] defsToCompare #[] (checked := (← get).compareChecked) with
    | .error e =>
      IO.println s!"Definition check failed for {d}: {e}"
      pure <| some .defnCheck
    | .ok compareChecked =>
      modify ({ · with compareChecked })
      match Comparator.checkAxioms solution #[] defsToCompare legalAxioms (← get).axiomChecked with
      | .error e => IO.println s!"Axiom check failed for definition {d}: {e}"; pure <| some .axioms
      | .ok axiomChecked =>
        modify ({ · with axiomChecked })
        pure none

  return ⟨targetInfo, some sInfo, fail, none, some d⟩

/-!
The verdict is derived from `outcomes` alone, so that the same rules apply before and after the kernel
phase. Theorem attempts carry `mode := some _`; definition outcomes carry `mode := none`.
-/

/-- Solution names (`t` or `t.disproof`) of the theorem attempts that have not failed. -/
def acceptedTheoremNames (outcomes : Array (Lean.Name × VerificationOutcome)) : Array Lean.Name :=
  outcomes.filterMap fun (_, o) => if o.mode.isSome && o.failureMode.isNone then o.solutionName else none

/-- Theorem targets without an accepted attempt, with all of their attempts. -/
def theoremFailures (outcomes : Array (Lean.Name × VerificationOutcome)) (theoremNames : Array Lean.Name) :
    Array (Lean.Name × VerificationOutcome) :=
  theoremNames.flatMap fun t =>
    let attempts := outcomes.filter (·.1 == t)
    if attempts.any (·.2.failureMode.isNone) then #[] else attempts

def definitionFailures (outcomes : Array (Lean.Name × VerificationOutcome)) (definitionNames : Array Lean.Name) :
    Array (Lean.Name × VerificationOutcome) :=
  outcomes.filter fun (d, o) => definitionNames.contains d && o.failureMode.isSome

/-- The acceptance rules: definition targets are mandatory, at least one theorem target must be accepted,
and with `must_resolve_all_sorries` all of them must be. Returns the message to reject with, if any. -/
def rejection (outcomes : Array (Lean.Name × VerificationOutcome)) (theoremNames definitionNames : Array Lean.Name)
    (mustResolveAllSorries : Bool) : Option String :=
  let fmt (header : String) (failures : Array (Lean.Name × VerificationOutcome)) : String :=
    failures.foldl (init := header) fun msg (n, outcome) => msg ++ s!"- {n}: {outcome.failureMode.map repr}\n"
  let defFailures := definitionFailures outcomes definitionNames
  let thmFailures := theoremFailures outcomes theoremNames
  if !defFailures.isEmpty then
    some <| fmt "Some definition targets failed:\n" defFailures
  else if (acceptedTheoremNames outcomes).isEmpty && !theoremNames.isEmpty then
    some <| fmt "All verification targets failed:\n" thmFailures
  else if !thmFailures.isEmpty && mustResolveAllSorries then
    some <| fmt "Some verification targets failed:\n" thmFailures
  else
    none

/-- Marks every outcome that has not failed yet and for which `failure` gives a mode. -/
def mark (outcomes : Array (Lean.Name × VerificationOutcome)) (failure : VerificationOutcome → Option CheckFailure) :
    Array (Lean.Name × VerificationOutcome) :=
  outcomes.map fun (n, o) => (n, if o.failureMode.isNone then { o with failureMode := failure o } else o)

/-- The per-target verdicts of the Lean kernel: a target is rejected if any declaration in its dependency
closure is not validly in the replayed environment, with the kernel's message for the first rejected one
in export order (the target itself, or a dependency it may share with other targets). -/
def kernelRejections (solution : Export.ExportedEnv) (failed : Std.HashMap Lean.Name Replay.Failure)
    (targets : Array Lean.Name) : M (Std.HashMap Lean.Name String) := do
  let mut rejected := {}
  for t in targets do
    let (_, closure) := (collectDeps solution t).run {}
    let inClosure := solution.constOrder.filter fun c => closure.contains c && failed.contains c
    let root := inClosure.find? (failed[·]? matches some (.kernel _)) <|> inClosure[0]?
    if let some r := root then
      let msg := match failed[r]! with
        | .kernel msg => msg
        | .dependency d => s!"was not checked because '{d}' was rejected"
      let msg := if r == t then msg else s!"depends on '{r}', which the kernel rejected:\n{msg}"
      IO.println s!"Lean default kernel rejects '{t}':\n{msg}"
      rejected := rejected.insert t msg
  IO.println s!"Lean default kernel {if rejected.isEmpty then "accepts" else "rejects"} the solution"
  return rejected

def reject (outcomes : Array (Lean.Name × VerificationOutcome)) (error : String) : M α := do
  writeReport { accepted := false, error, outcomes }
  throw <| .userError error

def accept (outcomes : Array (Lean.Name × VerificationOutcome)) (theoremNames : Array Lean.Name) : M Unit := do
  writeReport { accepted := true, outcomes }
  let thmFailures := theoremFailures outcomes theoremNames
  if !thmFailures.isEmpty then
    IO.println "Warnings/Diagnostics for unsolved/failed theorems:"
    for (t, outcome) in thmFailures do
      IO.println s!"WARNING: Theorem '{t}' remained unsolved: {outcome.failureMode.map repr}"
  IO.println "Your solution is okay!"

/-- Statement and axiom checks for every target. The kernel has not been consulted yet. -/
def verifyMatch (challenge solution : Export.ExportedEnv) (theoremNames : Array Lean.Name)
    (definitionNames : Array Lean.Name) : M (Array (Lean.Name × VerificationOutcome)) := (StateRefT'.run' · {}) do
  let primTargets ← primitiveTargets
  let legalAxioms ← getLegalAxioms
  let quotTargets := if legalAxioms.contains ``Quot.sound then #[``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] else #[]
  let compareChecked ← IO.ofExcept <| Comparator.compareAt challenge solution legalAxioms #[] (primTargets ++ quotTargets)
  modify ({ · with compareChecked })

  let mut outcomes : Array (Lean.Name × VerificationOutcome) := #[]
  for t in theoremNames do
    outcomes := outcomes ++ (← verifyTheorem challenge solution t definitionNames)
  for d in definitionNames do
    outcomes := outcomes.push (d, ← verifyDefinition challenge solution d definitionNames)
  return outcomes


def getTargets (theorems : Array Lean.Name) (definitions : Array Lean.Name) : M (Array Lean.Name) := do
  return (← builtinTargets) ++ theorems ++ (← getLegalAxioms) ++ (← primitiveTargets) ++ definitions

def compareIt (exportPath importPath : Option String := none) : M Unit := do
  let challengeModule ← getChallengeModule

  -- Replace any stale report first: whatever happens from here on, a report that exists is either the
  -- final verdict or marks an incomplete run.
  if exportPath.isNone then
    writeReport { accepted := false, error := some "Verification did not complete" }

  if importPath.isNone then
    safeLakeBuild challengeModule

  let (challengeExport, theoremNames, definitionNames) ← do
    if let some path := importPath then
      let h ← IO.FS.Handle.mk path .read
      let thms : Array String ← IO.ofExcept (Lean.Json.parse (← h.getLine) >>= Lean.FromJson.fromJson?)
      let defs : Array String ← IO.ofExcept (Lean.Json.parse (← h.getLine) >>= Lean.FromJson.fromJson?)
      if thms.isEmpty && defs.isEmpty then
        throw <| .userError "No verification targets selected or found."
      let exp ← h.readToEnd
      pure (exp, thms.map String.toName, defs.map String.toName)
    else
      let configTheoremNames ← getTheoremNames
      let configDefinitionNames ← getDefinitionNames
      let autoDiscover ← getAutoDiscover

      let (theoremNames, definitionNames) ←
        if autoDiscover then
          runQueryDecls challengeModule
        else
          pure (configTheoremNames, configDefinitionNames)

      if theoremNames.isEmpty && definitionNames.isEmpty then
        throw <| .userError "No verification targets selected or found."

      -- A missing target is rejected below, and a missing axiom, primitive or `Quot*` is rejected
      -- by `verifyMatch`; a missing `False`/`Not` (see `builtinTargets`) only makes disproofs fail.
      let challengeExport ← safeExport challengeModule (← getTargets theoremNames definitionNames) (ignoreMissing := true) (omitThmProofs := true)
      pure (challengeExport, theoremNames, definitionNames)

  -- The challenge export ignores missing roots, and `--verify` reads it from a snapshot.
  let challenge ← parseChallenge challengeExport theoremNames definitionNames
  if let some path := exportPath then
    let h ← IO.FS.Handle.mk path .write
    h.putStrLn <| Lean.Json.compress <| Lean.ToJson.toJson (theoremNames.map (·.toString))
    h.putStrLn <| Lean.Json.compress <| Lean.ToJson.toJson (definitionNames.map (·.toString))
    h.putStr challengeExport
    IO.println s!"Challenge snapshot pack successfully exported to {path}."
    return

  let solutionModule ← getSolutionModule
  let allowDisproofs ← getAllowDisproofs
  let initialSolutionExportTargets := (← getTargets theoremNames definitionNames) ++ (if allowDisproofs then theoremNames.map disproofName else #[])
  safeLakeBuild solutionModule
  let (solutionExport, initialSolution) ← exportSolution solutionModule initialSolutionExportTargets

  let mustResolveAllSorries ← getMustResolveAllSorries
  let mut outcomes ← verifyMatch challenge initialSolution theoremNames definitionNames
  -- Every target that passed the statement and axiom checks is replayed, even if the run is already bound
  -- to be rejected, so that an outcome without a failure always means "verified by the kernel".
  let acceptedTheorems := acceptedTheoremNames outcomes
  let acceptedDefinitions := definitionNames.filter fun d => outcomes.any fun (n, o) => n == d && o.failureMode.isNone
  let acceptedTargets := acceptedTheorems ++ acceptedDefinitions
  if !acceptedTargets.isEmpty then
    let presentInitialTargets := initialSolutionExportTargets.filter (initialSolution.constMap.contains ·)
    let verifiedTargets ← getTargets acceptedTheorems acceptedDefinitions
    let presentVerifiedTargets := verifiedTargets.filter (initialSolution.constMap.contains ·)
    let (verifiedSolutionExport, verifiedSolution) ← try
        let verified ←
          if Std.HashSet.ofArray presentInitialTargets == Std.HashSet.ofArray presentVerifiedTargets then
            pure (solutionExport, initialSolution)
          else
            let (vExport, vSol) ← exportSolution solutionModule verifiedTargets
            for (k, v) in vSol.constMap do
              if initialSolution.constMap[k]? != some v then
                throw <| IO.userError s!"Verified solution export differs from the checked export on '{k}'"
            pure (vExport, vSol)
        for t in acceptedTargets do
          if !verified.2.constMap.contains t then
            throw <| IO.userError s!"Verified solution export is missing accepted target '{t}'"
        pure verified
      catch e => reject (mark outcomes fun _ => some (.reexport e.toString)) e.toString

    -- External kernels only give a verdict for the whole solution; all of them run, the first rejection wins.
    let mut externalFailure : Option (String × String) := none
    for (kernelName, kernelCommand) in ← getExternalKernels do
      if let some error ← runExternalKernel kernelName kernelCommand verifiedSolutionExport then
        externalFailure := externalFailure <|> some (kernelName, error)

    let failed ← match ← runBuiltinKernel verifiedSolution acceptedTargets with
      | .error error => reject (mark outcomes fun _ => some (.kernel "lean" error)) error
      | .ok failed => pure failed
    let rejected ← kernelRejections verifiedSolution failed acceptedTargets
    outcomes := mark outcomes fun o => o.solutionName >>= (rejected[·]?) |>.map (.kernel "lean" ·)

    if let some (kernelName, error) := externalFailure then
      reject (mark outcomes fun _ => some (.kernel kernelName error)) error

  if let some error := rejection outcomes theoremNames definitionNames mustResolveAllSorries then
    reject outcomes error
  accept outcomes theoremNames

structure Config where
  challenge_module : String
  solution_module : String
  theorem_names : Option (Array String) := none
  definition_names : Option (Array String) := none
  permitted_axioms : Array String
  external_kernels : Option (Std.TreeMap String (Array String)) := none
  allow_disproofs : Option Bool := none
  must_resolve_all_sorries : Option Bool := none
  json_output_path : Option String := none
  deriving Lean.FromJson, Lean.ToJson, Repr

def M.run (x : M α) (cfg : Config) : IO α := do
  let cwd ← IO.Process.getCurrentDir
  let leanPrefix ← queryLeanPrefix cwd
  let gitLocation ← queryGitLocation
  let whichLean4Export := (← IO.getEnv "COMPARATOR_LEAN4EXPORT").getD "lean4export"
  let whichLandrun := (← IO.getEnv "COMPARATOR_LANDRUN").getD "landrun"
  let mut externalKernels := cfg.external_kernels.getD {}
  let nanodaOverride? ← IO.getEnv "COMPARATOR_NANODA"

  for (kernelName, kernelCommand) in externalKernels do
    if kernelCommand.isEmpty then
      throw <| .userError s!"{kernelName} has an empty command"

  if let some nanodaOverride := nanodaOverride? then
    if externalKernels.contains "nanoda" then
      externalKernels := externalKernels.modify "nanoda" fun cmd => cmd.set! 0 nanodaOverride

  ReaderT.run x {
    projectDir := cwd
    challengeModule := cfg.challenge_module.toName,
    solutionModule := cfg.solution_module.toName,
    theoremNames := cfg.theorem_names.getD #[] |>.map String.toName,
    definitionNames := cfg.definition_names.getD #[] |>.map String.toName,
    legalAxioms := cfg.permitted_axioms.map String.toName,
    leanPrefix := leanPrefix,
    gitLocation := gitLocation,
    allowDisproofs := cfg.allow_disproofs.getD false,
    autoDiscover := cfg.theorem_names.isNone && cfg.definition_names.isNone,
    whichLean4Export := whichLean4Export,
    whichLandrun := whichLandrun,
    externalKernels := externalKernels,
    mustResolveAllSorries := cfg.must_resolve_all_sorries.getD true,
    jsonOutputPath := cfg.json_output_path
  }

end Comparator

def main (args : List String) : IO Unit := do
  let (exportPath, importPath, configPath) ← match args with
    | ["--snapshot", snapshotPath, configPath] => pure (some snapshotPath, none, configPath)
    | ["--verify", snapshotPath, configPath] => pure (none, some snapshotPath, configPath)
    | [configPath] => pure (none, none, configPath)
    | _ => throw <| .userError "Expected arguments: [--snapshot snapshot_path | --verify snapshot_path] config_file_path"
  let content ← IO.FS.readFile configPath
  let config ← IO.ofExcept <| Lean.FromJson.fromJson? <| ← IO.ofExcept <| Lean.Json.parse content
  Comparator.M.run (Comparator.compareIt exportPath importPath) config
