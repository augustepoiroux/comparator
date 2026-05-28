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
  | defnCheck
  | opaqueCheck
  | inductCheck
  | ctorCheck
  | axioms
  | notFound
  deriving Lean.ToJson, Inhabited, Repr

structure Info where
  constInfo : Lean.ConstantInfo
  axioms : Array Lean.Name
  deriving Lean.ToJson, Inhabited

structure SafeVerifyOutcome where
  targetInfo : Info
  solutionInfo : Option Info
  failureMode : Option CheckFailure
  deriving Lean.ToJson, Inhabited

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

def verifySingleTheoremOutcome (challenge solution : Export.ExportedEnv) (t : Lean.Name)
    (definitionNames : Array Lean.Name) (primTargets : Array Lean.Name) (legalAxioms : Array Lean.Name)
    (allowDisproofs : Bool) : IO SafeVerifyOutcome := do
  let targetInfo := getInfo challenge t |>.getD ⟨.axiomInfo { name := t, levelParams := [], type := .sort .zero, isUnsafe := false }, #[]⟩
  let isDisproof := allowDisproofs && solution.constMap.contains (t ++ `disproof)
  let actualTarget := if isDisproof then t ++ `disproof else t
  let solutionInfo := getInfo solution actualTarget

  if solutionInfo.isNone then
    return ⟨targetInfo, none, some .notFound⟩

  let sInfo := solutionInfo.get!
  let tKind := match targetInfo.constInfo with
    | .defnInfo _ => "def"
    | .thmInfo _ => "theorem"
    | .axiomInfo _ => "axiom"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .inductInfo _ => "inductive"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
  let sKind := match sInfo.constInfo with
    | .defnInfo _ => "def"
    | .thmInfo _ => "theorem"
    | .axiomInfo _ => "axiom"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .inductInfo _ => "inductive"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"

  if tKind ≠ sKind then
    return ⟨targetInfo, some sInfo, some <| .kind tKind sKind⟩

  let (_, deps) := (collectDeps solution actualTarget).run {}
  let filteredDefinitionNames := definitionNames.filter deps.contains
  
  -- Handle matching depending on whether it is a theorem or definition
  let isTheorem := match targetInfo.constInfo with | .thmInfo _ => true | _ => false
  let targets := if isTheorem then #[t] ++ legalAxioms else legalAxioms
  let defsToCompare := if isTheorem then filteredDefinitionNames else
    (if filteredDefinitionNames.contains t then filteredDefinitionNames else filteredDefinitionNames.push t)

  match Comparator.compareAt challenge solution targets defsToCompare primTargets allowDisproofs with
  | .error e =>
    IO.println s!"Verification failed for {t}: {e}"
    let failureMode := match targetInfo.constInfo with
      | .thmInfo _ => .thmType
      | .defnInfo _ => .defnCheck
      | .opaqueInfo _ => .opaqueCheck
      | .inductInfo _ => .inductCheck
      | .ctorInfo _ => .ctorCheck
      | _ => .defnCheck
    return ⟨targetInfo, some sInfo, some failureMode⟩
  | .ok () =>
    match Comparator.checkAxioms solution #[t] defsToCompare legalAxioms allowDisproofs with
    | .error _ =>
      return ⟨targetInfo, some sInfo, some .axioms⟩
    | .ok () =>
      return ⟨targetInfo, some sInfo, none⟩

def verifyMatch (challengeExport : String) (solutionExport : String) (theoremNames : Array Lean.Name) :
    M (Array Lean.Name × Array (Lean.Name × SafeVerifyOutcome)) := do
  let challenge ← Export.parseStream (← stringStream challengeExport)
  let solution ← Export.parseStream (← stringStream solutionExport)
  let definitionNames ← getDefinitionNames
  let allowDisproofs ← getAllowDisproofs
  let primTargets ← primitiveTargets
  let legalAxioms ← getLegalAxioms
  let mustResolveAllSorries ← getMustResolveAllSorries

  let mut outcomes : Array (Lean.Name × SafeVerifyOutcome) := #[]
  let mut passedTheorems := #[]
  let mut failedTheorems := #[]

  for t in theoremNames do
    let outcome ← verifySingleTheoremOutcome challenge solution t definitionNames primTargets legalAxioms allowDisproofs
    outcomes := outcomes.push (t, outcome)
    if outcome.failureMode.isNone then
      passedTheorems := passedTheorems.push t
    else
      failedTheorems := failedTheorems.push (t, outcome)

  for d in definitionNames do
    let outcome ← verifySingleTheoremOutcome challenge solution d definitionNames primTargets legalAxioms allowDisproofs
    outcomes := outcomes.push (d, outcome)

  -- JSON output if requested
  if let some jsonPath ← getJsonOutputPath then
    let jsonOutput := Lean.ToJson.toJson outcomes
    IO.FS.writeFile jsonPath (Lean.Json.compress jsonOutput)

  -- Evaluate checks
  if passedTheorems.isEmpty && !theoremNames.isEmpty then
    let mut errMsg := "All verification targets failed:\n"
    for (t, outcome) in failedTheorems do
      errMsg := errMsg ++ s!"- {t}: {outcome.failureMode.map repr}\n"
    throw <| .userError errMsg

  if !failedTheorems.isEmpty then
    if mustResolveAllSorries then
      let mut errMsg := "Some verification targets failed:\n"
      for (t, outcome) in failedTheorems do
        errMsg := errMsg ++ s!"- {t}: {outcome.failureMode.map repr}\n"
      throw <| .userError errMsg
    else
      IO.println "Warnings/Diagnostics for unsolved/failed theorems:"
      for (t, outcome) in failedTheorems do
        IO.println s!"WARNING: Theorem '{t}' remained unsolved: {outcome.failureMode.map repr}"

  return (passedTheorems, outcomes)

def nameToOleanPath (projectDir : System.FilePath) (name : Lean.Name) : System.FilePath :=
  let components := name.components.map (·.toString (escape := false))
  components.foldl (· / ·) (projectDir / ".lake" / "build" / "lib" / "lean") |>.withExtension "olean"

def compareIt : M Unit := do
  let challengeModule ← getChallengeModule
  IO.ofExcept <| ← safeLakeBuild challengeModule

  let configTheoremNames ← getTheoremNames
  let (theoremNames, challengeExport) ← do
    if configTheoremNames.isEmpty then
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
        ++ (← primitiveTargets) ++ (← getDefinitionNames)
      let challengeExport ← safeExport challengeModule challengeExportTargets
      pure (discoveredTheoremNames, challengeExport)
    else
      let challengeExportTargets := (← builtinTargets) ++ configTheoremNames ++ (← getLegalAxioms)
        ++ (← primitiveTargets) ++ (← getDefinitionNames)
      let challengeExport ← safeExport challengeModule challengeExportTargets
      pure (configTheoremNames, challengeExport)

  let solutionModule ← getSolutionModule
  IO.ofExcept <| ← safeLakeBuild solutionModule

  -- First export of the solution containing all target theorems
  let initialSolutionExportTargets := (← builtinTargets) ++ theoremNames ++ (← getLegalAxioms)
    ++ (← primitiveTargets) ++ (← getDefinitionNames)
  let mut initialSolutionExportTargets := initialSolutionExportTargets
  if ← getAllowDisproofs then
    initialSolutionExportTargets := initialSolutionExportTargets ++ theoremNames.map (· ++ `disproof)

  let solutionExport ← safeExport solutionModule initialSolutionExportTargets

  let (passedTheorems, outcomes) ← verifyMatch challengeExport solutionExport theoremNames

  -- Secondary validation: export only passed theorems for nanoda & kernel checks
  let verifiedSolutionExport ← do
    if outcomes.any (fun (_, outcome) => outcome.failureMode.isSome) then
      -- If we had any failures, re-export only the passed ones to avoid sorryAx in kernel checks
      let solutionExportTargets := (← builtinTargets) ++ passedTheorems ++ (← getLegalAxioms)
        ++ (← primitiveTargets) ++ (← getDefinitionNames)
      let mut solutionExportTargets := solutionExportTargets
      if ← getAllowDisproofs then
        solutionExportTargets := solutionExportTargets ++ passedTheorems.map (· ++ `disproof)
      safeExport solutionModule solutionExportTargets
    else
      pure solutionExport

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
