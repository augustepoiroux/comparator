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

def safeLakeBuild (target : Lean.Name) : M (Except String Unit) := do
  IO.println s!"Building {target}"
  let leanPrefix ← getLeanPrefix
  let projectDir ← getProjectDir
  let dotLakeDir := projectDir / ".lake"
  let gitLocation ← getGitLocation

  if !(← System.FilePath.pathExists dotLakeDir) then
    IO.FS.createDir dotLakeDir

  let args := buildLandrunArgs {
    cmd := "lake",
    args := #["build", target.toString (escape := false)],
    envPass := #["PATH", "HOME", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    readablePaths := #[projectDir]
    writablePaths := #[dotLakeDir]
    executablePaths := #[leanPrefix, gitLocation]
  }
  
  let proc ← IO.Process.spawn {
    cmd := (← read).whichLandrun,
    args,
    env := #[("LEAN_ABORT_ON_PANIC", some "1")]
    cwd := projectDir
  }
  let ret ← proc.wait
  if ret != 0 then
    return .error s!"Building {target} failed."
  return .ok ()

def safeExport (module : Lean.Name) (decls : Array Lean.Name) : M String := do
  IO.println s!"Exporting {decls} from {module}"
  let args :=
    if decls.isEmpty then
      #[module.toString (escape := false)]
    else
      let baseArgs := #[module.toString (escape := false), "--"]
      decls.foldl (·.push <| ·.toString (escape := false)) baseArgs

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

def stringStream (s : String) : BaseIO IO.FS.Stream := do
  let ref ← IO.mkRef {
    data := s.toByteArray
  }
  return IO.FS.Stream.ofBuffer ref

@[inline]
def getMustResolveAllSorries : M Bool := do return (← read).mustResolveAllSorries

@[inline]
def getJsonOutputPath : M (Option String) := do return (← read).jsonOutputPath

def disproofExportRoots : Array Lean.Name :=
  #[``Not, ``Nonempty]

def disproofName (n : Lean.Name) : Lean.Name :=
  n ++ `disproof

instance : Lean.ToJson Lean.ConstantInfo where
  toJson
    | .defnInfo _v    => Lean.Json.mkObj [("kind", "definition")]
    | .thmInfo _v     => Lean.Json.mkObj [("kind", "theorem")]
    | .axiomInfo _v   => Lean.Json.mkObj [("kind", "axiom")]
    | .opaqueInfo _v  => Lean.Json.mkObj [("kind", "opaque")]
    | .quotInfo _v    => Lean.Json.mkObj [("kind", "quotient")]
    | .inductInfo _v  => Lean.Json.mkObj [("kind", "inductive")]
    | .ctorInfo _v    => Lean.Json.mkObj [("kind", "constructor")]
    | .recInfo _v     => Lean.Json.mkObj [("kind", "recursor")]

-- JSON schemas matching SafeVerify
inductive CheckFailure where
  | kind (kind1 kind2 : String)
  | thmType
  | disproofType
  | defnCheck
  | opaqueCheck
  | inductCheck
  | ctorCheck
  | axioms
  | notFound
  | ambiguous
  deriving Lean.ToJson, Inhabited, Repr

structure Info where
  constInfo : Lean.ConstantInfo
  axioms : Array Lean.Name
  deriving Lean.ToJson, Inhabited

structure SafeVerifyOutcome where
  targetInfo : Option Info
  solutionInfo : Option Info
  targetKind : String
  origin : String
  mode : Option TheoremMode
  actualName : Option Lean.Name
  accepted : Bool
  failureMode : Option CheckFailure
  deriving Lean.ToJson, Inhabited

structure VerifyResult where
  acceptedTheorems : Array Lean.Name
  outcomes : Array (Lean.Name × SafeVerifyOutcome)

abbrev DepM := StateM (Std.HashSet Lean.Name)

partial def collectDeps (env : Export.ExportedEnv) (n : Lean.Name) : DepM Unit := do
  if (← get).contains n then
    return
  modify (·.insert n)
  if let some info := env.constMap[n]? then
    info.type.getUsedConstants.forM (collectDeps env)
    if let some val := info.value? (allowOpaque := true) then
      val.getUsedConstants.forM (collectDeps env)
    match info with
    | .axiomInfo .. | .quotInfo .. | .defnInfo .. | .thmInfo .. | .opaqueInfo .. => pure ()
    | .inductInfo info =>
      info.ctors.forM (collectDeps env)
      info.all.forM (collectDeps env)
    | .ctorInfo info =>
      collectDeps env info.induct
    | .recInfo info =>
      info.rules.forM fun rule => do
        collectDeps env rule.ctor
        rule.rhs.getUsedConstants.forM (collectDeps env)

partial def getAxioms (env : Export.ExportedEnv) (n : Lean.Name) : Array Lean.Name := Id.run do
  let (_, deps) := (collectDeps env n).run {}
  let mut axioms := #[]
  for dep in deps do
    if let some (.axiomInfo _) := env.constMap[dep]? then
      axioms := axioms.push dep
  return axioms

def getInfo (env : Export.ExportedEnv) (n : Lean.Name) : Option Info := do
  let ci ← env.constMap[n]?
  let axioms := getAxioms env n
  some { constInfo := ci, axioms := axioms }

def constKind : Lean.ConstantInfo → String
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def directTarget (n : Lean.Name) : TheoremTarget :=
  { challengeName := n, solutionName := n, mode := .direct }

def failedOutcome (targetInfo : Option Info) (solutionInfo : Option Info)
    (targetKind origin : String) (mode : Option TheoremMode) (actualName : Option Lean.Name)
    (failure : CheckFailure) : SafeVerifyOutcome :=
  { targetInfo, solutionInfo, targetKind, origin, mode, actualName,
    accepted := false, failureMode := some failure }

def passedOutcome (targetInfo solutionInfo : Info) (targetKind origin : String)
    (mode : Option TheoremMode) (actualName : Lean.Name) : SafeVerifyOutcome :=
  { targetInfo := some targetInfo, solutionInfo := some solutionInfo, targetKind, origin, mode,
    actualName := some actualName, accepted := true, failureMode := none }

def failedTheoremOutcome (targetInfo : Option Info) (solutionInfo : Option Info)
    (origin : String) (mode : Option TheoremMode) (actualName : Option Lean.Name)
    (failure : CheckFailure) : SafeVerifyOutcome :=
  failedOutcome targetInfo solutionInfo "theorem" origin mode actualName failure

def passedTheoremOutcome (targetInfo solutionInfo : Info) (origin : String)
    (mode : TheoremMode) (actualName : Lean.Name) :
    SafeVerifyOutcome :=
  passedOutcome targetInfo solutionInfo "theorem" origin (some mode) actualName

def verifyTheorem (challenge solution : Export.ExportedEnv) (t : Lean.Name)
    (definitionNames : Array Lean.Name) (legalAxioms : Array Lean.Name)
    (allowDisproofs : Bool) (origin : String) : IO (Option Lean.Name × SafeVerifyOutcome) := do
  let targetInfo := getInfo challenge t
  let some targetInfo' := targetInfo
    | return (none, failedTheoremOutcome none none origin none none .notFound)

  let directInfo := getInfo solution t
  let dname := disproofName t
  let disproofInfo := if allowDisproofs then getInfo solution dname else none
  let (actualName, mode, solutionInfo) ←
    match directInfo, disproofInfo with
    | some direct, some _ =>
      return (none, failedTheoremOutcome (some targetInfo') (some direct) origin none none .ambiguous)
    | some direct, none => pure (t, TheoremMode.direct, direct)
    | none, some disproof => pure (dname, TheoremMode.disproof, disproof)
    | none, none =>
      return (none, failedTheoremOutcome (some targetInfo') none origin none none .notFound)

  let (_, deps) := (collectDeps solution actualName).run {}
  let defsToCompare := definitionNames.filter deps.contains
  let target := { challengeName := t, solutionName := actualName, mode := mode }

  match ← Comparator.compareAt challenge solution #[target] defsToCompare #[] with
  | .error e =>
    IO.println s!"Verification failed for {t}: {e}"
    let failure := if mode == .disproof then .disproofType else .thmType
    return (none, failedTheoremOutcome (some targetInfo') (some solutionInfo) origin (some mode) (some actualName) failure)
  | .ok () =>
    match Comparator.checkAxioms solution #[actualName] defsToCompare legalAxioms with
    | .error e =>
      IO.println s!"Axiom check failed for {t}: {e}"
      return (none, failedTheoremOutcome (some targetInfo') (some solutionInfo) origin (some mode) (some actualName) .axioms)
    | .ok () =>
      return (some actualName, passedTheoremOutcome targetInfo' solutionInfo origin mode actualName)

def verifyDefinition (challenge solution : Export.ExportedEnv) (d : Lean.Name)
    (legalAxioms : Array Lean.Name) : IO SafeVerifyOutcome := do
  let targetInfo := getInfo challenge d
  let solutionInfo := getInfo solution d
  let some targetInfo' := targetInfo
    | return failedOutcome none solutionInfo "definition" "configured" none (some d) .notFound
  let some solutionInfo' := solutionInfo
    | return failedOutcome (some targetInfo') none "definition" "configured" none (some d) .notFound

  let targetKind := constKind targetInfo'.constInfo
  let solutionKind := constKind solutionInfo'.constInfo
  if targetKind != solutionKind then
    return failedOutcome (some targetInfo') (some solutionInfo') "definition" "configured" none (some d) (.kind targetKind solutionKind)

  match ← Comparator.compareAt challenge solution #[] #[d] #[] with
  | .error e =>
    IO.println s!"Definition check failed for {d}: {e}"
    return failedOutcome (some targetInfo') (some solutionInfo') "definition" "configured" none (some d) .defnCheck
  | .ok () =>
    match Comparator.checkAxioms solution #[] #[d] legalAxioms with
    | .error e =>
      IO.println s!"Axiom check failed for definition {d}: {e}"
      return failedOutcome (some targetInfo') (some solutionInfo') "definition" "configured" none (some d) .axioms
    | .ok () =>
      let outcome : SafeVerifyOutcome :=
        passedOutcome targetInfo' solutionInfo' "definition" "configured" none d
      return outcome

def verifyMatch (challengeExport : String) (solutionExport : String) (theoremNames : Array Lean.Name)
    (allowPartialTheoremFailures : Bool) (theoremOrigin : String) : M VerifyResult := do
  let challenge ← Export.parseStream (← stringStream challengeExport)
  let solution ← Export.parseStream (← stringStream solutionExport)
  let definitionNames ← getDefinitionNames
  let allowDisproofs ← getAllowDisproofs
  let primTargets ← primitiveTargets
  let legalAxioms ← getLegalAxioms
  let mustResolveAllSorries ← getMustResolveAllSorries

  IO.ofExcept <| ← Comparator.compareAt challenge solution (legalAxioms.map directTarget) #[] primTargets

  let mut outcomes : Array (Lean.Name × SafeVerifyOutcome) := #[]
  let mut acceptedTheorems := #[]
  let mut theoremFailures := #[]
  let mut definitionFailures := #[]

  for t in theoremNames do
    let (accepted, outcome) ← verifyTheorem challenge solution t definitionNames legalAxioms allowDisproofs theoremOrigin
    outcomes := outcomes.push (t, outcome)
    match accepted with
    | some actual => acceptedTheorems := acceptedTheorems.push actual
    | none => theoremFailures := theoremFailures.push (t, outcome)

  for d in definitionNames do
    let outcome ← verifyDefinition challenge solution d legalAxioms
    outcomes := outcomes.push (d, outcome)
    if outcome.failureMode.isSome then
      definitionFailures := definitionFailures.push (d, outcome)

  if let some jsonPath ← getJsonOutputPath then
    let jsonOutput := Lean.ToJson.toJson outcomes
    IO.FS.writeFile jsonPath (Lean.Json.compress jsonOutput)

  if !definitionFailures.isEmpty then
    let mut errMsg := "Some definition targets failed:\n"
    for (d, outcome) in definitionFailures do
      errMsg := errMsg ++ s!"- {d}: {outcome.failureMode.map repr}\n"
    throw <| .userError errMsg

  if acceptedTheorems.isEmpty && !theoremNames.isEmpty then
    let mut errMsg := "All verification targets failed:\n"
    for (t, outcome) in theoremFailures do
      errMsg := errMsg ++ s!"- {t}: {outcome.failureMode.map repr}\n"
    throw <| .userError errMsg

  if !theoremFailures.isEmpty then
    if mustResolveAllSorries || !allowPartialTheoremFailures then
      let mut errMsg := "Some verification targets failed:\n"
      for (t, outcome) in theoremFailures do
        errMsg := errMsg ++ s!"- {t}: {outcome.failureMode.map repr}\n"
      throw <| .userError errMsg
    else
      IO.println "Warnings/Diagnostics for unsolved/failed theorems:"
      for (t, outcome) in theoremFailures do
        IO.println s!"WARNING: Theorem '{t}' remained unsolved: {outcome.failureMode.map repr}"

  return { acceptedTheorems, outcomes }

def nameToOleanPath (projectDir : System.FilePath) (name : Lean.Name) : System.FilePath :=
  let components := name.components.map (·.toString (escape := false))
  components.foldl (· / ·) (projectDir / ".lake" / "build" / "lib" / "lean") |>.withExtension "olean"

def compareIt : M Unit := do
  let challengeModule ← getChallengeModule
  IO.ofExcept <| ← safeLakeBuild challengeModule

  let configTheoremNames ← getTheoremNames
  let discoveredMode := configTheoremNames.isEmpty
  let allowDisproofs ← getAllowDisproofs
  let extraExportRoots := if allowDisproofs then disproofExportRoots else #[]
  let (theoremNames, challengeExport) ← do
    if discoveredMode then
      let projectDir ← getProjectDir
      let oleanPath := nameToOleanPath projectDir challengeModule
      let (modData, _) ← Lean.readModuleData oleanPath
      let mut discovered := #[]
      for ci in modData.constants do
        if let .thmInfo val := ci then
          if val.value.getUsedConstants.contains `sorryAx then
            discovered := discovered.push val.name
      let discoveredTheoremNames := discovered
      let challengeExportTargets := (← builtinTargets) ++ discoveredTheoremNames ++ (← getLegalAxioms)
        ++ (← primitiveTargets) ++ (← getDefinitionNames) ++ extraExportRoots
      let challengeExport ← safeExport challengeModule challengeExportTargets
      pure (discoveredTheoremNames, challengeExport)
    else
      let challengeExportTargets := (← builtinTargets) ++ configTheoremNames ++ (← getLegalAxioms)
        ++ (← primitiveTargets) ++ (← getDefinitionNames) ++ extraExportRoots
      let challengeExport ← safeExport challengeModule challengeExportTargets
      pure (configTheoremNames, challengeExport)

  let solutionModule ← getSolutionModule
  IO.ofExcept <| ← safeLakeBuild solutionModule

  let mut initialSolutionExportTargets := (← builtinTargets) ++ theoremNames ++ (← getLegalAxioms)
    ++ (← primitiveTargets) ++ (← getDefinitionNames) ++ extraExportRoots
  if allowDisproofs then
    initialSolutionExportTargets := initialSolutionExportTargets ++ theoremNames.map disproofName

  let solutionExport ← safeExport solutionModule initialSolutionExportTargets

  let allowPartialTheoremFailures := discoveredMode && !(← getMustResolveAllSorries)
  let theoremOrigin := if discoveredMode then "discovered" else "configured"
  let result ← verifyMatch challengeExport solutionExport theoremNames allowPartialTheoremFailures theoremOrigin

  let verifiedSolutionExportTargets := (← builtinTargets) ++ result.acceptedTheorems ++ (← getLegalAxioms)
    ++ (← primitiveTargets) ++ (← getDefinitionNames) ++ extraExportRoots
  let verifiedSolutionExport ← safeExport solutionModule verifiedSolutionExportTargets

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
    whichLean4Export,
    whichLandrun,
    whichNanoda,
    mustResolveAllSorries := cfg.must_resolve_all_sorries.getD true,
    jsonOutputPath := cfg.json_output_path
  }

end Comparator

def main (args : List String) : IO Unit := do
  let some (configPath : String) := args[0]?
    | throw <| .userError "Expected config file path as first argument."
  let content ← IO.FS.readFile configPath
  let config ← IO.ofExcept <| Lean.FromJson.fromJson? <| ← IO.ofExcept <| Lean.Json.parse content
  Comparator.M.run Comparator.compareIt config
