/-
  Comparator.Disproof: Static Exact Negation & Stateful Universe level Unifier

  This module implements static exact logical negation and structural signature-matching
  for the comparator disproof-validation framework.

  DESIGN CHOICES & ARCHITECTURE:
  1. Purely Static: Bypasses the need for an active `Lean.Environment` or `MetaM`
     context during signature matching, performing all expression transformations entirely
     in a pure static pass.
  2. Context-Stack Type/Universe Inference: Tracks binder types under a context stack (`ctx`)
     to dynamically lookup variable types,
     statically infer domain universe levels (`inferUniverse`), and lift bound variables.
  3. Dynamic One-Way Universe level Unification (`isEquivInst`): Maps expected polymorphic
     universe parameters statefully to concrete levels or variables in the solution.
-/
import Lean
import Export.Parse

namespace Comparator

namespace Disproof

open Lean

def mkAnd (p q : Expr) : Expr :=
  mkApp2 (mkConst ``And) p q

def mkOr (p q : Expr) : Expr :=
  mkApp2 (mkConst ``Or) p q

def mkNot (p : Expr) : Expr :=
  mkApp (mkConst ``Not) p

/--
Recursively pre-processes and canonicalizes all occurrences of type inequality `Ne`
to standard negated equality `Not (Eq ...)` throughout the expression tree, ensuring
a clean and robust structural comparison.
-/
partial def preprocessExpr (e : Expr) : Expr :=
  match e.cleanupAnnotations with
  | .app (.app (.app (.const ``Ne lvls) α) p) q =>
    let α' := preprocessExpr α
    let p' := preprocessExpr p
    let q' := preprocessExpr q
    .app (.const ``Not []) (.app (.app (.app (.const ``Eq lvls) α') p') q')
  | .app f a => .app (preprocessExpr f) (preprocessExpr a)
  | .lam name ty body binfo => .lam name (preprocessExpr ty) (preprocessExpr body) binfo
  | .forallE name ty body binfo => .forallE name (preprocessExpr ty) (preprocessExpr body) binfo
  | .letE name ty val body nondep => .letE name (preprocessExpr ty) (preprocessExpr val) (preprocessExpr body) nondep
  | .mdata m e' => .mdata m (preprocessExpr e')
  | .proj s i e' => .proj s i (preprocessExpr e')
  | _ => e

mutual

/--
Statically infer the type of a well-formed closed/quantified expression `e`
under the context stack `ctx` using the exported constant definitions map `constMap`.
Since the inputs are compiled type-correct theorem signatures, this static inference
is highly simple, robust, and safe.
-/
partial def inferType (ctx : List Expr) (constMap : Std.HashMap Name ConstantInfo) (e : Expr) : Expr :=
  match e with
  | .bvar i =>
    if h : i < ctx.length then
      (ctx.get ⟨i, h⟩).liftLooseBVars 0 (i + 1)
    else
      .sort Level.zero
  | .sort l =>
    .sort (Level.succ l)
  | .const n ls =>
    match constMap[n]? with
    | some ci => ci.type.instantiateLevelParams ci.levelParams ls
    | none => .sort Level.zero
  | .app f a =>
    let fTy := (inferType ctx constMap f).cleanupAnnotations
    match fTy with
    | .forallE _ _ body _ => body.instantiate1 a
    | _ => .sort Level.zero
  | .lam name ty body binfo =>
    .forallE name ty (inferType (ty :: ctx) constMap body) binfo
  | .forallE _ ty body _ =>
    let u := inferUniverse ctx constMap ty
    let v := inferUniverse (ty :: ctx) constMap body
    .sort (Level.imax u v)
  | .letE _ ty val body _ =>
    (inferType (ty :: ctx) constMap body).instantiate1 val
  | .lit (.natVal _) =>
    .const ``Nat []
  | .lit (.strVal _) =>
    .const ``String []
  | .mdata _ e =>
    inferType ctx constMap e
  | _ =>
    .sort Level.zero

/--
Statically infer the universe level `u` (where `e : Sort u`) of a well-formed type `e`.
-/
partial def inferUniverse (ctx : List Expr) (constMap : Std.HashMap Name ConstantInfo) (e : Expr) : Level :=
  let t := (inferType ctx constMap e).cleanupAnnotations
  match t with
  | .sort l => l
  | _ => Level.zero

end

/--
Negates a closed expression statically.
Keeps track of binder types in context stack `ctx` to dynamically infer domain universe levels
and parameterize the `Exists` type constructor correctly.
-/
partial def negateExpr (e : Expr) (constMap : Std.HashMap Name ConstantInfo) : Expr :=
  negateExprAux [] (preprocessExpr e)
where
  negateExprAux (ctx : List Expr) (e : Expr) : Expr :=
    let e := e.cleanupAnnotations
    match e with
    | .app (.app (.const ``And _) p) q =>
      .forallE `_ p (negateExprAux (p :: ctx) q) .default
    | .forallE name ty body binfo =>
      let body' := .lam name ty (negateExprAux (ty :: ctx) body) binfo
      let u := inferUniverse ctx constMap ty
      mkApp2 (mkConst ``Exists [u]) ty body'
    | .app (.app (.const ``Or _) p) q =>
      mkAnd (negateExprAux ctx p) (negateExprAux ctx q)
    | .app (.app (.const ``Exists _) _) (.lam name btype body binfo) =>
      .forallE name btype (negateExprAux (btype :: ctx) body) binfo
    | .lam name btype body binfo =>
      .lam name btype (negateExprAux (btype :: ctx) body) binfo
    | .app (.const ``Not _) p =>
      p
    | _ =>
      mkNot e

/--
Statically instantiates parameter level variables in `l` with their computed mapped levels.
-/
partial def instantiateLevel (map : Std.HashMap Name Level) (l : Level) : Level :=
  match l with
  | .succ l' => .succ (instantiateLevel map l')
  | .max la lb => .max (instantiateLevel map la) (instantiateLevel map lb)
  | .imax la lb => .imax (instantiateLevel map la) (instantiateLevel map lb)
  | .param n => match map[n]? with | some l' => l' | none => .param n
  | _ => l

mutual

/--
Match and unify compound and parametric universe levels, mapping target variables
to concrete levels or parameters in the solution dynamically, with static normalisation.
-/
partial def matchLevel (map : Std.HashMap Name Level) (l1 l2 : Level) : Option (Std.HashMap Name Level) :=
  let l1' := (instantiateLevel map l1).normalize
  let l2' := (instantiateLevel map l2).normalize
  go map l1' l2'
where
  go (map : Std.HashMap Name Level) (l1 l2 : Level) : Option (Std.HashMap Name Level) :=
    match l1, l2 with
    | .zero, .zero => some map
    | .succ l1', .succ l2' => matchLevel map l1' l2'
    | .max l1a l1b, .max l2a l2b =>
      match matchLevel map l1a l2a with
      | some map' => matchLevel map' l1b l2b
      | none => none
    | .imax l1a l1b, .imax l2a l2b =>
      match matchLevel map l1a l2a with
      | some map' => matchLevel map' l1b l2b
      | none => none
    | .param n, l2 =>
      match map[n]? with
      | some l1' => if l1' == l2 then some map else none
      | none => some (map.insert n l2)
    | _, _ => none

partial def matchLevels (map : Std.HashMap Name Level) (ls1 ls2 : List Level) : Option (Std.HashMap Name Level) :=
  match ls1, ls2 with
  | [], [] => some map
  | l1 :: tail1, l2 :: tail2 =>
    match matchLevel map l1 l2 with
    | some map' => matchLevels map' tail1 tail2
    | none => none
  | _, _ => none

/--
One-Way structural unifier with dynamic universe level mapping. Used strictly for disproofs
to enable specialized type/universe assignments in disproof signatures while maintaining strict logic.
-/
partial def isEquivInst (map : Std.HashMap Name Level) (a b : Expr) : Option (Std.HashMap Name Level) :=
  match a, b with
  | .bvar i, .bvar j => if i == j then some map else none
  | .fvar i, .fvar j => if i == j then some map else none
  | .mvar i, .mvar j => if i == j then some map else none
  | .sort l1, .sort l2 => matchLevel map l1 l2
  | .const n1 l1, .const n2 l2 =>
    if n1 == n2 then matchLevels map l1 l2 else none
  | .app f1 a1, .app f2 a2 =>
    match isEquivInst map f1 f2 with
    | some map' => isEquivInst map' a1 a2
    | none => none
  | .lam _ t1 b1 _, .lam _ t2 b2 _ =>
    match isEquivInst map t1 t2 with
    | some map' => isEquivInst map' b1 b2
    | none => none
  | .forallE _ t1 b1 _, .forallE _ t2 b2 _ =>
    match isEquivInst map t1 t2 with
    | some map' => isEquivInst map' b1 b2
    | none => none
  | .letE _ t1 v1 b1 _, .letE _ t2 v2 b2 _ =>
    match isEquivInst map t1 t2 with
    | some map' =>
      match isEquivInst map' v1 v2 with
      | some map'' => isEquivInst map'' b1 b2
      | none => none
    | none => none
  | .lit v1, .lit v2 => if v1 == v2 then some map else none
  | .mdata _ e1, .mdata _ e2 => isEquivInst map e1 e2
  | .proj n1 i1 e1, .proj n2 i2 e2 =>
    if n1 == n2 && i1 == i2 then isEquivInst map e1 e2 else none
  | _, _ => none

end

end Disproof
end Comparator
