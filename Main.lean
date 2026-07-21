/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean
import Comparator
import Lean4Checker.Replay
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
  enableNanoda : Bool
  allowDisproofs : Bool
  autoDiscover : Bool
  whichLandrun : String
  whichLean4Export : String
  whichNanoda : String
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
def getNanodaEnabled : M Bool := do return (← read).enableNanoda

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
  args ++ #[spawnArgs.cmd] ++ spawnArgs.args

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

def runNanoda (solutionExport : String) : M Unit := do
  IO.println "Running nanoda kernel on solution"
  IO.FS.withTempFile fun config configPath => do
    let legalAxioms ← getLegalAxioms
    config.putStr <| Lean.Json.compress <| Lean.Json.mkObj [
      ("use_stdin", true),
      ("permitted_axioms", .arr <| legalAxioms.map (.str ∘ Lean.Name.toString)),
      ("unpermitted_axiom_hard_error", true),
      ("nat_extension", true),
      ("string_extension", true),
    ]
    config.flush

    let spawnArgs := {
      cmd := (← read).whichNanoda
      args := #[configPath.toString],
      envPass := #[]
      readablePaths := #[configPath.toString]
      writablePaths := #[]
      executablePaths := #[]
    }

    let args := buildLandrunArgs spawnArgs
    let proc ← IO.Process.spawn {
      cmd := (← read).whichLandrun,
      args,
      stdin := .piped
      env := spawnArgs.envOverride
      cwd := (← getProjectDir)
    }

    let (nanodaStdin, proc) ← proc.takeStdin
    nanodaStdin.putStr solutionExport
    nanodaStdin.flush
    let ret ← proc.wait
    if ret != 0 then
      throw <| .userError s!"Child exited with {ret}"

    IO.println "Nanoda kernel accepts the solution"

def runKernel (solution : Export.ExportedEnv) : M Unit := do
  IO.println "Running Lean default kernel on solution."
  let mut env ← Lean.mkEmptyEnvironment
  let mut constMap := solution.constMap
  -- Lean's kernel interprets just the addition of `Quot as adding all of these so adding them
  -- multiple times leads to errors.
  constMap := constMap.erase `Quot.mk |>.erase `Quot.lift |>.erase `Quot.ind
  discard <| env.replay' constMap
  IO.println "Lean default kernel accepts the solution"

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
  ]

def builtinTargets : M (Array Lean.Name) := do
  if ← getNanodaEnabled then
    -- TODO: fix when nanoda fixes its string handling
    let mut additional := #[``Nat, ``String, ``String.mk, ``Char, ``Char.ofNat, ``List]
    if (← getLegalAxioms).contains ``Quot.sound then
      additional := additional ++ #[``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]
    return additional
  else
    return #[]

def nameToOleanPath (projectDir : System.FilePath) (name : Lean.Name) : System.FilePath :=
  let components := name.components.map (·.toString (escape := false))
  components.foldl (· / ·) (projectDir / ".lake" / "build" / "lib" / "lean") |>.withExtension "olean"

def runQueryDecls (mode : String) (module : Lean.Name) : M (Array Lean.Name) := do
  let projectDir ← getProjectDir
  let oleanPath := nameToOleanPath projectDir module
  let queryDeclsPath := (← IO.appPath).parent.getD "" / "query_decls"
  let whichQueryDecls ←
    match ← IO.getEnv "COMPARATOR_QUERY_DECLS" with
    | some path => pure path
    | none => try pure (← IO.FS.realPath queryDeclsPath).toString catch _ => pure "query_decls"

  let stdout ← runSandBoxedWithStdout {
    cmd := whichQueryDecls,
    args := #[mode, oleanPath.toString],
    envPass := #["PATH", "HOME", "LEAN_PATH", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    readablePaths := #[projectDir, projectDir / ".lake", whichQueryDecls]
    writablePaths := #[]
    executablePaths := #[whichQueryDecls]
  }

  return (stdout.splitOn "\n" |>.filter (!·.isEmpty) |>.map String.toName).toArray

def filterExportTargets (module : Lean.Name) (decls : Array Lean.Name) : M (Array Lean.Name) := do
  let localDecls ← runQueryDecls "list-decls" module
  let localConsts := Std.HashSet.ofArray localDecls
  let coreConsts := Std.HashSet.ofArray ((← primitiveTargets) ++ (← builtinTargets) ++ (← getLegalAxioms))
  return decls.filter fun t => coreConsts.contains t || localConsts.contains t

def safeExport (module : Lean.Name) (decls : Array Lean.Name) : M String := do
  let decls ← filterExportTargets module decls
  IO.println s!"Exporting {decls} from {module}"

  let args :=
    if decls.isEmpty then
      #[module.toString]
    else
      let baseArgs := #[module.toString, "--"]
      decls.foldl (·.push <| ·.toString) baseArgs

  let leanPrefix ← getLeanPrefix
  let projectDir ← getProjectDir
  let dotLakeDir := projectDir / ".lake"
  runSandBoxedWithStdout {
    cmd := (← read).whichLean4Export
    args := args,
    envPass := #["PATH", "HOME", "LEAN_PATH", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    readablePaths := #[projectDir, dotLakeDir]
    writablePaths := #[]
    executablePaths := #[leanPrefix]
  }


def stringStream (s : String) : BaseIO IO.FS.Stream := do
  let ref ← IO.mkRef {
    data := s.toByteArray
  }
  return IO.FS.Stream.ofBuffer ref

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
  deriving Lean.ToJson, Inhabited

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

def getInfo (env : Export.ExportedEnv) (n : Lean.Name) : Option Info := do
  some ⟨← env.constMap[n]?, getAxioms env n⟩

def verifyOneTheoremAttempt (challenge solution : Export.ExportedEnv) (t : Lean.Name)
    (solutionName : Lean.Name) (mode : TheoremMode) (targetInfo : Info) (definitionNames : Array Lean.Name) :
    M (Bool × VerificationOutcome) := do
  let legalAxioms ← getLegalAxioms
  let sInfo := (getInfo solution solutionName).get!
  let (_, deps) := (collectDeps solution solutionName).run {}
  let defsToCompare := definitionNames.filter deps.contains

  let typeFailureMode : CheckFailure := match mode with | .direct => .thmType | .disproof => .disproofType

  let (accepted, fail) ←
    match Comparator.compareAt challenge solution #[t] defsToCompare #[] (mode == .disproof) with
    | .error e =>
      IO.println s!"Verification failed for {solutionName}: {e}"
      pure (false, some typeFailureMode)
    | .ok () =>
      match Comparator.checkAxioms solution #[solutionName] defsToCompare legalAxioms with
      | .error e => IO.println s!"Axiom check failed for {solutionName}: {e}"; pure (false, some .axioms)
      | .ok () => pure (true, none)

  let outcome := ⟨targetInfo, some sInfo, fail, some mode, some solutionName⟩
  return (accepted, outcome)

def verifyTheorem (challenge solution : Export.ExportedEnv) (t : Lean.Name) (definitionNames : Array Lean.Name) :
    M (Array Lean.Name × Array (Lean.Name × VerificationOutcome)) := do
  let allowDisproofs ← getAllowDisproofs
  let targetInfo := getInfo challenge t |>.getD ⟨.axiomInfo ⟨⟨t, [], .sort .zero⟩, false⟩, #[]⟩
  let directInfo := solution.constMap[t]?
  let dname := disproofName t
  let disproofInfo := if allowDisproofs then solution.constMap[dname]? else none

  let mut acceptedNames := #[]
  let mut outcomes := #[]

  if let some _ := directInfo then
    let (accepted, outcome) ← verifyOneTheoremAttempt challenge solution t t .direct targetInfo definitionNames
    if accepted then
      acceptedNames := acceptedNames.push t
    outcomes := outcomes.push (t, outcome)

  if let some _ := disproofInfo then
    let (accepted, outcome) ← verifyOneTheoremAttempt challenge solution t dname .disproof targetInfo definitionNames
    if accepted then
      acceptedNames := acceptedNames.push dname
    outcomes := outcomes.push (t, outcome)

  if directInfo.isNone && disproofInfo.isNone then
    outcomes := outcomes.push (t, ⟨targetInfo, none, some .notFound, none, none⟩)

  return (acceptedNames, outcomes)

def verifyDefinition (challenge solution : Export.ExportedEnv) (d : Lean.Name) :
    M VerificationOutcome := do
  let legalAxioms ← getLegalAxioms
  let targetInfo := getInfo challenge d |>.getD ⟨.axiomInfo ⟨⟨d, [], .sort .zero⟩, false⟩, #[]⟩
  let some sInfo := getInfo solution d
    | return ⟨targetInfo, none, some .notFound, none, none⟩

  let tKind := constKind targetInfo.constInfo
  let sKind := constKind sInfo.constInfo
  if tKind != sKind then
    return ⟨targetInfo, some sInfo, some (.kind tKind sKind), none, some d⟩

  let fail ←
    match Comparator.compareAt challenge solution #[] #[d] #[] with
    | .error e =>
      IO.println s!"Definition check failed for {d}: {e}"
      pure <| some .defnCheck
    | .ok () =>
      match Comparator.checkAxioms solution #[] #[d] legalAxioms with
      | .error e => IO.println s!"Axiom check failed for definition {d}: {e}"; pure <| some .axioms
      | .ok () => pure none

  return ⟨targetInfo, some sInfo, fail, none, some d⟩

def throwFailures (header : String) (failures : Array (Lean.Name × VerificationOutcome)) : M α := do
  let mut msg := header
  for (n, outcome) in failures do
    msg := msg ++ s!"- {n}: {outcome.failureMode.map repr}\n"
  throw <| .userError msg

def verifyMatch (challengeExport : String) (solutionExport : String) (theoremNames : Array Lean.Name)
    (definitionNames : Array Lean.Name) (allowPartialTheoremFailures : Bool) : M (Array Lean.Name) := do
  let challenge ← Export.parseStream (← stringStream challengeExport)
  let solution ← Export.parseStream (← stringStream solutionExport)
  let primTargets ← primitiveTargets
  let legalAxioms ← getLegalAxioms
  let mustResolveAllSorries ← getMustResolveAllSorries

  IO.ofExcept <| Comparator.compareAt challenge solution legalAxioms #[] primTargets

  let mut outcomes : Array (Lean.Name × VerificationOutcome) := #[]
  let mut acceptedTheorems := #[]
  let mut theoremFailures := #[]
  let mut definitionFailures := #[]

  for t in theoremNames do
    let (acceptedActualNames, theoremOutcomes) ← verifyTheorem challenge solution t definitionNames
    outcomes := outcomes ++ theoremOutcomes
    for actual in acceptedActualNames do
      acceptedTheorems := acceptedTheorems.push actual
    if acceptedActualNames.isEmpty then
      for (_, outcome) in theoremOutcomes do
        theoremFailures := theoremFailures.push (t, outcome)

  for d in definitionNames do
    let outcome ← verifyDefinition challenge solution d
    outcomes := outcomes.push (d, outcome)
    if outcome.failureMode.isSome then
      definitionFailures := definitionFailures.push (d, outcome)

  if let some jsonPath ← getJsonOutputPath then
    let jsonOutput := Lean.ToJson.toJson outcomes
    IO.FS.writeFile jsonPath (Lean.Json.compress jsonOutput)

  if !definitionFailures.isEmpty then
    throwFailures "Some definition targets failed:\n" definitionFailures

  if acceptedTheorems.isEmpty && !theoremNames.isEmpty then
    throwFailures "All verification targets failed:\n" theoremFailures

  if !theoremFailures.isEmpty then
    if mustResolveAllSorries || !allowPartialTheoremFailures then
      throwFailures "Some verification targets failed:\n" theoremFailures
    else
      IO.println "Warnings/Diagnostics for unsolved/failed theorems:"
      for (t, outcome) in theoremFailures do
        IO.println s!"WARNING: Theorem '{t}' remained unsolved: {outcome.failureMode.map repr}"

  return acceptedTheorems


def getTargets (theorems : Array Lean.Name) (definitions : Array Lean.Name) : M (Array Lean.Name) := do
  return (← builtinTargets) ++ theorems ++ (← getLegalAxioms) ++ (← primitiveTargets) ++ definitions

def compareIt (exportPath importPath : Option String := none) : M Unit := do
  let challengeModule ← getChallengeModule

  if importPath.isNone then
    safeLakeBuild challengeModule

  let (challengeExport, theoremNames, definitionNames) ← do
    if let some path := importPath then
      let h ← IO.FS.Handle.mk path .read
      let thms : Array String ← IO.ofExcept (Lean.Json.parse (← h.getLine) >>= Lean.FromJson.fromJson?)
      let defs : Array String ← IO.ofExcept (Lean.Json.parse (← h.getLine) >>= Lean.FromJson.fromJson?)
      let exp ← h.readToEnd
      pure (exp, thms.map String.toName, defs.map String.toName)
    else
      let configTheoremNames ← getTheoremNames
      let configDefinitionNames ← getDefinitionNames
      let autoDiscover ← getAutoDiscover

      let (theoremNames, definitionNames) ←
        if autoDiscover then
          let thms ← runQueryDecls "find-sorry-theorems" challengeModule
          let defs ← runQueryDecls "find-sorry-defs" challengeModule
          pure (thms, defs)
        else
          pure (configTheoremNames, configDefinitionNames)

      if theoremNames.isEmpty && definitionNames.isEmpty then
        throw <| .userError "No verification targets selected or found."

      let challengeExport ← safeExport challengeModule (← getTargets theoremNames definitionNames)
      pure (challengeExport, theoremNames, definitionNames)

  if let some path := exportPath then
    let h ← IO.FS.Handle.mk path .write
    h.putStrLn <| Lean.Json.compress <| Lean.ToJson.toJson (theoremNames.map (·.toString))
    h.putStrLn <| Lean.Json.compress <| Lean.ToJson.toJson (definitionNames.map (·.toString))
    h.putStr challengeExport
    IO.println s!"Challenge snapshot pack successfully exported to {path}."
    return

  let solutionModule ← getSolutionModule
  safeLakeBuild solutionModule

  let allowDisproofs ← getAllowDisproofs
  let initialSolutionExportTargets := (← getTargets theoremNames definitionNames) ++ (if allowDisproofs then theoremNames.map disproofName else #[])
  let solutionExport ← safeExport solutionModule initialSolutionExportTargets

  let allowPartialTheoremFailures := !(← getMustResolveAllSorries)
  let acceptedTheorems ← verifyMatch challengeExport solutionExport theoremNames definitionNames allowPartialTheoremFailures

  let verifiedSolutionExport ← safeExport solutionModule (← getTargets acceptedTheorems definitionNames)

  if ← getNanodaEnabled then
    runNanoda verifiedSolutionExport

  let verifiedSolution ← Export.parseStream (← stringStream verifiedSolutionExport)
  runKernel verifiedSolution

  IO.println "Your solution is okay!"

structure Config where
  challenge_module : String
  solution_module : String
  theorem_names : Option (Array String) := none
  definition_names : Option (Array String) := none
  permitted_axioms : Array String
  enable_nanoda : Bool
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
  let whichNanoda := (← IO.getEnv "COMPARATOR_NANODA").getD "nanoda_bin"
  ReaderT.run x {
    projectDir := cwd
    challengeModule := cfg.challenge_module.toName,
    solutionModule := cfg.solution_module.toName,
    theoremNames := cfg.theorem_names.getD #[] |>.map String.toName,
    definitionNames := cfg.definition_names.getD #[] |>.map String.toName,
    legalAxioms := cfg.permitted_axioms.map String.toName,
    leanPrefix := leanPrefix,
    gitLocation := gitLocation,
    enableNanoda := cfg.enable_nanoda,
    allowDisproofs := cfg.allow_disproofs.getD false,
    autoDiscover := cfg.theorem_names.isNone && cfg.definition_names.isNone,
    whichLean4Export,
    whichLandrun,
    whichNanoda,
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
