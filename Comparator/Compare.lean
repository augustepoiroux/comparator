/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Comparator.Axioms
import Export.Parse

open Lean

namespace Comparator

def predLevel? (rigid : Bool) : Level → Option Level
  | .succ l => some l
  | .max a b => match predLevel? rigid a, predLevel? rigid b with
    | some a', some b' => some (mkLevelMax' a' b')
    | some x, none | none, some x => if rigid then none else some x
    | _, _ => none
  | _ => none

partial def matchLevel (rigid sm : Bool) (ps : List Name) (rsub : List (Name × Level))
    (l1 l2 : Level) (s : List (Name × Level)) : List (Name × Level) :=
  let inst (d l : Level) := l.instantiateParams ps (ps.map fun n => (rsub.lookup n).getD d)
  match rigid, l1 with
  | _, .param n =>
    if !ps.contains n || (rsub.lookup n).isSome then s else match s.lookup n with
    | none => (n, l2) :: s
    | some p => if !rigid && Level.geq p l2 then (n, l2) :: s.filter (·.1 != n) else s
  | _, .succ n1 => (predLevel? rigid l2).elim s (matchLevel rigid sm ps rsub n1 · s)
  | false, .imax n1 n2 =>
    if !rsub.isEmpty && Level.isEquiv (inst (.succ .zero) n2) .zero then s
    else if l2 == .zero || Level.geq (inst .zero n1) (.succ l2) then matchLevel false sm ps rsub n2 .zero s
    else if let (true, .imax m1 m2) := (sm, l2) then
      matchLevel false true ps rsub n2 m2 (matchLevel false true ps rsub n1 m1 s)
    else matchLevel false sm ps rsub n2 l2 (matchLevel false sm ps rsub n1 l2 s)
  | false, .max n1 n2 =>
    if let (true, .max m1 m2) := (sm, l2) then
      matchLevel false true ps rsub n2 m2 (matchLevel false true ps rsub n1 m1 s)
    else matchLevel false sm ps rsub n2 l2 (matchLevel false sm ps rsub n1 l2 s)
  | _, _ => s

def isAuxName (defTargets : Std.HashSet Name) (n : Name) : Bool :=
  let rec go : Name → Bool
    | .str p s => (Name.mkSimple s).isInternalDetail || go p
    | .num .. => true
    | _ => false
  !defTargets.contains n && go n

def auxThmApp? (defTargets : Std.HashSet Name) (env : Export.ExportedEnv) (e : Expr) :
    Option (TheoremVal × List Level × Array Expr) := do
  let rec head : Expr → Expr | .app f _ | .mdata _ f => head f | e => e
  let .const n ls := head e | none
  guard (isAuxName defTargets n)
  let .thmInfo c ← env.constMap[n]? | none
  guard (ls.length == c.levelParams.length && !c.type.hasLooseBVars)
  let rec collect : Expr → Array Expr → Array Expr
    | .mdata _ f, acc => collect f acc | .app f a, acc => collect f (acc.push a) | _, acc => acc.reverse
  return (c, ls, collect e #[])

abbrev Ctx := List (Expr × Option (Expr × Expr))
abbrev PairKey := Bool × (Name × List Level) × (Name × List Level)
abbrev ExprKey := Bool × Bool × Ctx × Expr × Expr

structure MatchState where
  pairs : Std.HashMap PairKey Bool := {}
  seen : Std.HashSet ExprKey := {}
  levelPairs : Array (Level × Level) := #[]
  nonAux : Std.HashSet Name := {}

abbrev MatchM := OptionT (StateM MatchState)

@[inline] def addNonAux (sc : Bool) (n : Name) : MatchM Unit := do
  unless sc do modify fun s => { s with nonAux := s.nonAux.insert n }

@[inline] def checkLevels (sc freeLevels : Bool) (ls1 ls2 : List Level) : MatchM Unit := do
  guard (ls1.length == ls2.length)
  for l1 in ls1, l2 in ls2 do
    if !sc && freeLevels && l1.hasParam then modify fun s => { s with levelPairs := s.levelPairs.push (l1, l2) }
    else guard (Level.isEquiv l1 l2)

def runSpec (subSc : Bool) (act : MatchM Unit) : MatchM Bool := do
  let s0 ← get
  let (res, s1) := act.run s0
  if res.isSome && !subSc then set s1; return true
  let pairs := if subSc then s1.pairs else s1.pairs.fold (fun m k v => if v then m else m.insert k false) s0.pairs
  set { s0 with pairs, seen := if subSc && res.isSome then s1.seen else s0.seen }
  return res.isSome

def checkPair (pKey : PairKey) (act : MatchM Unit) : MatchM Unit := do
  match (← get).pairs[pKey]? with
  | some true => pure ()
  | some false => failure
  | none =>
    modify fun s => { s with pairs := s.pairs.insert pKey false }
    act
    modify fun s => { s with pairs := s.pairs.insert pKey true }

partial def matchExpr (defTargets : Std.HashSet Name) (chal sol : Export.ExportedEnv)
    (e1 e2 : Expr) (freeLevels : Bool := false) (ctx : Ctx := [])
    (inApp : Bool := false) (sc : Bool := false) : MatchM Unit := do
  let (a1, a2) := (e1.consumeMData, e2.consumeMData)
  if let (.sort l1, .sort l2) := (a1, a2) then return ← checkLevels sc freeLevels [l1] [l2]
  let cache := a1.approxDepth > 2 || a2.approxDepth > 2
  if cache && (← get).seen.contains (sc, inApp, if a1.hasLooseBVars || a2.hasLooseBVars then ctx else [], a1, a2) then
    return ()
  let letVal? (isSol : Bool) : Expr → Option Expr
    | .bvar i => ctx[i]?.bind (·.2.map fun (v1, v2) => (if isSol then v2 else v1).liftLooseBVars 0 (i + 1))
    | _ => none
  if ((letVal? false a1).isSome || (letVal? true a2).isSome) && a1 != a2 then
    let (a1', a2') := match a1, a2, letVal? false a1, letVal? true a2 with
      | .bvar i1, .bvar i2, some v1, some v2 => if i1 < i2 then (v1, a2) else (a1, v2)
      | _, _, some v1, _ => (v1, a2)
      | _, _, _, some v2 => (a1, v2)
      | _, _, _, _ => unreachable!
    matchExpr defTargets chal sol a1' a2' freeLevels ctx false sc
  else match if inApp then (none, none) else (auxThmApp? defTargets chal a1, auxThmApp? defTargets sol a2) with
    | (some (c1, ls1, args1), some (c2, ls2, args2)) =>
      -- Aux theorems are Prop-valued, so by proof irrelevance matching their result types suffices.
      -- When definition holes exist, peeled bvars must also match their challenge binder domain so
      -- a hole cannot make the context uninhabited while changing the peeled domain.
      let t1 := c1.type.instantiateLevelParams c1.levelParams ls1
      let t2 := c2.type.instantiateLevelParams c2.levelParams ls2
      let chalCtx := if sc || defTargets.isEmpty then ctx else ctx.map fun (t, v) => (t, v.map fun (x, _) => (x, x))
      let mut curr1 := t1; let mut k1 := 0
      while k1 < args1.size do
        let .forallE _ dom body _ := curr1.consumeMData | break
        let .bvar idx := args1[k1]!.consumeMData | break
        let some (bty, _) := ctx[idx]? | break
        if !defTargets.isEmpty then
          let bvarType := bty.liftLooseBVars 0 (idx + 1)
          let domInst := dom.instantiateRev (args1.extract 0 k1)
          if bvarType != domInst then
            if !(← runSpec true (matchExpr defTargets chal chal domInst bvarType false chalCtx false true)) then
              break
        curr1 := body; k1 := k1 + 1
      let r := args1.size - k1
      guard (args2.size >= r)
      let k2 := args2.size - r
      for i in [:r] do matchExpr defTargets chal sol args1[k1 + i]! args2[k2 + i]! freeLevels ctx false sc
      let direct := checkPair (sc, (c1.name, ls1.map Level.normalize), (c2.name, ls2.map Level.normalize))
        (matchExpr defTargets chal sol t1 t2 freeLevels [] false sc)
      let ok ← if k1 == 0 && k2 == 0 then direct; pure true
        else if !freeLevels && r == 0 && args2.all (·.consumeMData.isBVar) && args1 == args2 then runSpec sc direct
        else pure false
      unless ok do
        let mut curr2 := t2
        for _ in [:k2] do
          let .forallE _ _ body _ := curr2.consumeMData | failure
          curr2 := body
        matchExpr defTargets chal sol (curr1.instantiateRev (args1.extract 0 k1))
          (curr2.instantiateRev (args2.extract 0 k2)) freeLevels ctx false sc
    | (some _, none) | (none, some _) => failure
    | (none, none) => match a1, a2 with
      | .app f1 x1, .app f2 x2 =>
        matchExpr defTargets chal sol f1 f2 freeLevels ctx true sc
        matchExpr defTargets chal sol x1 x2 freeLevels ctx false sc
      | .lam _ t1 b1 _, .lam _ t2 b2 _ | .forallE _ t1 b1 _, .forallE _ t2 b2 _ =>
        matchExpr defTargets chal sol t1 t2 freeLevels ctx false sc
        matchExpr defTargets chal sol b1 b2 freeLevels ((t1, none) :: ctx) false sc
      | .letE _ t1 v1 b1 _, .letE _ t2 v2 b2 _ =>
        matchExpr defTargets chal sol t1 t2 freeLevels ctx false sc
        matchExpr defTargets chal sol v1 v2 freeLevels ctx false sc
        matchExpr defTargets chal sol b1 b2 freeLevels ((t1, some (v1, v2)) :: ctx) false sc
      | .proj s1 i1 b1, .proj s2 i2 b2 =>
        guard (s1 == s2 && i1 == i2); addNonAux sc s1; matchExpr defTargets chal sol b1 b2 freeLevels ctx false sc
      | .const n1 ls1, .const n2 ls2 =>
        match if isAuxName defTargets n1 && isAuxName defTargets n2 then (chal.constMap[n1]?, sol.constMap[n2]?) else (none, none) with
        | (some (.defnInfo d1), some (.defnInfo d2)) =>
          if d1.safety == .safe && d2.safety == .safe then
            guard (ls1.length == d1.levelParams.length && ls2.length == d2.levelParams.length &&
              !d1.type.hasLooseBVars && !d2.type.hasLooseBVars && !d1.value.hasLooseBVars && !d2.value.hasLooseBVars)
            checkPair (sc, (n1, ls1.map Level.normalize), (n2, ls2.map Level.normalize)) do
              matchExpr defTargets chal sol (d1.type.instantiateLevelParams d1.levelParams ls1)
                (d2.type.instantiateLevelParams d2.levelParams ls2) freeLevels [] false sc
              matchExpr defTargets chal sol (d1.value.instantiateLevelParams d1.levelParams ls1)
                (d2.value.instantiateLevelParams d2.levelParams ls2) freeLevels [] false sc
          else guard (n1 == n2 && d1.safety == d2.safety); checkLevels sc freeLevels ls1 ls2; addNonAux sc n1
        | (some (.thmInfo _), _) | (_, some (.thmInfo _)) | (some (.defnInfo _), _) | (_, some (.defnInfo _)) => failure
        | _ => guard (n1 == n2); checkLevels sc freeLevels ls1 ls2; addNonAux sc n1
      | .bvar .., .bvar .. | .fvar .., .fvar .. | .mvar .., .mvar .. | .lit .., .lit .. => guard (a1 == a2)
      | _, _ => failure
  if cache then
    let keyCtx := if a1.hasLooseBVars || a2.hasLooseBVars then ctx else []
    modify fun s => { s with seen := s.seen.insert (sc, inApp, keyCtx, a1, a2) }

def runMatch (defTargets : Std.HashSet Name) (chal sol : Export.ExportedEnv)
    (es : Array (Expr × Expr)) (freeLevels : Bool := false) : Option MatchState :=
  let (r, s) := (es.forM fun (a, b) => matchExpr defTargets chal sol a b freeLevels).run {}
  r.map fun _ => s

-- Pass 1 (`freeLevels = true`) heuristically proposes challenge universe instantiations;
-- pass 2 (`freeLevels = false`) performs the authoritative structural check.
def checkDisproof (defTargets : Std.HashSet Name) (chal sol : Export.ExportedEnv)
    (chalType : Expr) (chalLevels : List Name) (solType : Expr) (solLevels : List Name) : Option (Array Name) := do
  let (outer, exp) ← match solType.consumeMData with
    | .forallE _ exp c _ => if c.consumeMData == .const ``False [] then some (``False, exp) else none
    | .app c exp => if c.consumeMData == .const ``Not [] then some (``Not, exp) else none
    | _ => none
  let chalType ← if chalLevels.isEmpty then pure chalType else do
    let st ← runMatch defTargets chal sol #[(chalType, exp)] true
    let npairs := st.levelPairs.map fun (l1, l2) => (l1.normalize, l2.normalize)
    let rigid := npairs.foldl (fun s (a, b) => matchLevel true false chalLevels [] a b s) []
    let solve (sm : Bool) :=
      let sub := npairs.foldl (fun s (a, b) => matchLevel false sm chalLevels rigid a b s) rigid
      chalLevels.map fun n => (sub.lookup n).getD .zero
    let cands :=
      (if chalLevels.all solLevels.contains then [chalLevels.map .param] else []) ++
      (if chalLevels.length == solLevels.length then [solLevels.map .param] else []) ++
      [solve false, solve true]
    let ls ← cands.find? fun ls => npairs.all fun (l1, l2) => Level.isEquiv (l1.instantiateParams chalLevels ls) l2
    pure (chalType.instantiateLevelParams chalLevels ls)
  return (← runMatch defTargets chal sol #[(chalType, exp)]).nonAux.insert outer |>.toArray

namespace Compare

structure Context where
  challenge : Export.ExportedEnv
  solution : Export.ExportedEnv
  definitionTargets : Std.HashSet Lean.Name

structure State where
  worklist : Array Lean.Name
  checked : Std.HashSet Lean.Name

abbrev CompareM := ReaderT Context <| StateT State <| Except String

deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.ConstantInfo

def addWorklist (n : Lean.Name) : CompareM Unit := do
  if !(← get).checked.contains n then
    modify fun s => { worklist := s.worklist.push n, checked := s.checked.insert n }

def stripConstExprs (isDefTarget : Bool) (ci : ConstantInfo) : ConstantInfo × Array Expr :=
  let d := Expr.bvar 0
  match ci with
  | .axiomInfo v  => (.axiomInfo { v with type := d }, #[v.type])
  | .defnInfo v   => (.defnInfo { v with type := d, value := d, hints := .opaque, all := [] },
                      if isDefTarget then #[v.type] else #[v.type, v.value])
  | .thmInfo v    => (.thmInfo { v with type := d, value := d, all := [] }, #[v.type])
  | .opaqueInfo v => (.opaqueInfo { v with type := d, value := d }, #[v.type, v.value])
  | .quotInfo v   => (.quotInfo { v with type := d }, #[v.type])
  | .inductInfo v => (.inductInfo { v with type := d }, #[v.type])
  | .ctorInfo v   => (.ctorInfo { v with type := d }, #[v.type])
  | .recInfo v    => (.recInfo { v with type := d, rules := v.rules.map ({ · with rhs := d }) },
                      #[v.type] ++ v.rules.toArray.map (·.rhs))

-- Fast path: identical expressions with no aux constants match structurally (`getUsedConstants` includes `.proj`).
def matchConst (defTargets : Std.HashSet Name) (chal sol : Export.ExportedEnv)
    (isDefTarget : Bool) (c1 c2 : ConstantInfo) : Option (ConstantInfo × Array Name) := do
  let (m1, es1) := stripConstExprs isDefTarget c1
  let (m2, es2) := stripConstExprs isDefTarget c2
  guard ((!isDefTarget || c1 matches .defnInfo _) && m1 == m2)
  if es1 == es2 then
    let cs := es1.flatMap Expr.getUsedConstants
    if !cs.any (isAuxName defTargets) then return (m1, cs)
  return (m1, (← runMatch defTargets chal sol (es1.zip es2)).nonAux.toArray)

partial def loop : CompareM Unit := do
  if (← get).worklist.isEmpty then
    return ()

  let target ← modifyGet fun s => (s.worklist.back!, { s with worklist := s.worklist.pop })
  let some challengeConst := (← read).challenge.constMap[target]?
    | throw s!"Const not found in challenge '{target}'"
  let some solutionConst := (← read).solution.constMap[target]?
    | throw s!"Const not found in solution '{target}'"

  let ctx ← read
  let some (ccMeta, nonAux) := matchConst ctx.definitionTargets ctx.challenge ctx.solution
      (ctx.definitionTargets.contains target) challengeConst solutionConst
    | throw s!"Const does not match between challenge and target '{target}'"
  nonAux.forM addWorklist
  runForUsedConsts ccMeta addWorklist

  loop

end Compare

def compareAt (challenge solution : Export.ExportedEnv) (theoremTargets : Array Lean.Name)
    (definitionTargets : Array Lean.Name) (primitive : Array Lean.Name) (allowDisproofs : Bool := false)
    (checked : Std.HashSet Lean.Name := {}) (allDefinitionTargets : Array Lean.Name := definitionTargets) :
    Except String (Std.HashSet Lean.Name) := do
  let defTargetSet := Std.HashSet.ofArray (allDefinitionTargets ++ definitionTargets)
  let mut worklist := primitive

  for target in theoremTargets do
    let some challengeConst := challenge.constMap[target]?
      | throw s!"Const not found in challenge: '{target}'"

    let dname := target ++ `disproof
    if allowDisproofs && solution.constMap[dname]?.isSome then
      let some solutionConst := solution.constMap[dname]?
        | unreachable!
      let .thmInfo cc := challengeConst
        | throw s!"Challenge target is not a theorem: '{target}'"
      let .thmInfo sc := solutionConst
        | throw s!"Solution disproof target is not a theorem: '{dname}'"

      let some nonAux := checkDisproof defTargetSet challenge solution cc.type cc.levelParams sc.type sc.levelParams
        | throw s!"Solution disproof statement does not match accepted disproof interface: '{dname}'"

      worklist := worklist ++ nonAux
    else
      let some solutionConst := solution.constMap[target]?
        | throw s!"Const not found in solution: '{target}'"
      unless (challengeConst, solutionConst) matches (.thmInfo _, .thmInfo _) | (.axiomInfo _, .axiomInfo _) do
        throw s!"Challenge and solution constant kind don't match: '{target}'"

      let some (_, nonAux) := Compare.matchConst defTargetSet challenge solution false challengeConst solutionConst
        | throw s!"Challenge and solution theorem statement do not match: '{target}'"

      worklist := worklist ++ nonAux

  for target in definitionTargets do
    let some challengeConst := challenge.constMap[target]?
      | throw s!"Const not found in challenge: '{target}'"

    let some solutionConst := solution.constMap[target]?
      | throw s!"Const not found in solution: '{target}'"

    let .defnInfo challengeConst := challengeConst
      | throw s!"Challenge constant is not a definition: '{target}'"
    let .defnInfo solutionConst := solutionConst
      | throw s!"Solution constant is not a definition: '{target}'"

    let some (_, nonAux) := Compare.matchConst defTargetSet challenge solution true
        (.defnInfo challengeConst) (.defnInfo solutionConst)
      | throw s!"Const does not match between challenge and target '{target}'"

    worklist := (worklist.push solutionConst.name) ++ nonAux

  let (_, s) ← (do worklist.forM Compare.addWorklist; Compare.loop).run
    { challenge, solution, definitionTargets := defTargetSet } |>.run { worklist := #[], checked }
  return s.checked

end Comparator
