/-!
MWE regression suite for auxiliary-constant matching false negatives (all fail on unpatched nightly):
1. `nested_proof`: nested tactic proof (`by omega`) in theorem binders (`_proof_1` vs `.disproof._proof_1`).
2. `let_matcher`: destructuring `let` in a theorem statement (`match_1` vs `.disproof.match_1`).
3. `helper_cached_matcher` & `direct_proof_helper_matcher`: `match` / destructuring `let` cached under
   an earlier `private` helper in `Solution.lean` (both `.disproof` and direct proof).
4. `poly_matcher` & `ulift_matcher_collapse`: universe-polymorphic matcher specialization and collapse.
5. `omega_diff_hyps`: `Challenge` minting two `_proof_N` auxiliaries with different captured hypotheses
   matched against a single `.disproof._proof_1` in `Solution` (`instantiated` branch).
6. `non_bvar_thm_aux`: theorem statement calling a `private` auxiliary theorem on non-`.bvar` `n + 1`.
7. `struct_ctor_matcher`: `structure` field with a `match` expression whose constructor `PairZero.mk`
   reuses a `private` helper's matcher in `Solution` (`stripConstExprs`).
8. `max_before_param`, `check_copy_paste`, `comm_max`: polymorphic disproof universe edge cases.
9. `def_hole_let`: auto-discovered definition hole (`hole`) combined with `let` and nested `by omega`.
10. `reused_sol_aux`: `Solution` reusing one cached auxiliary proof across same-arg and extra-hyp calls.
11. `mixed_bvar_nonbvar`: auxiliary theorem taking both leading `.bvar` and trailing non-`.bvar` (`n + 1`).
12. `have_vs_let_hole`: `let` vs `have` binding across a definition hole (`hole`) with nested `by omega`.
13. `poly_max_narrow`, `poly_imax_fn`, `poly_unused`: polymorphic disproof universe narrowing, `imax`
    before rigid params, and peeled universe-dependent unused binder domain (`!freeLevels` direct guard).
-/

universe u v w

-- 1. Nested proof in statement (`nested_proof._proof_1`)
theorem nested_proof (l : Nat) (t : Fin (l + 1) → Int) (h0 : t ⟨0, by omega⟩ = -1) :
    t ⟨0, by omega⟩ = 1 := by
  sorry

-- 2. Destructuring `let` in statement (`let_matcher.match_1`)
def runWitness (n : Nat) : Nat × Nat := (n, n + 1)

theorem let_matcher (n : Nat) :
    let (a, b) := runWitness n
    a = b := by
  sorry

-- 3. `match` expression cached under an earlier `private` helper in `Solution` (disproof + direct)
def pairFn (k : Nat) : Int × Int := (Int.ofNat k, -Int.ofNat k)

theorem helper_cached_matcher (k : Nat) :
    (match pairFn k with | (a, b) => a + b) = 1 := by
  sorry

theorem direct_proof_helper_matcher (p : Bool × Bool) :
    (let (a, b) := p; a == b) = (p.1 == p.2) := by
  sorry

-- 4. Universe-polymorphic destructuring `let` & collapsing `ULift` matchers
theorem poly_matcher (α : Type u) (p : α × α) (β : Type v) (x y : β) :
    (let (a, b) := p; a = b) ∧ x = y := by
  sorry

theorem ulift_matcher_collapse (p : ULift.{u} Nat × Nat) (q : ULift.{0} Nat × Nat) :
    (let (a, b) := p; a.down + b) + (let (c, d) := q; c.down + d) = 1 := by
  sorry

-- 5. Different captured hypotheses across nested `omega` proofs (`instantiated` branch)
theorem omega_diff_hyps (l m : Nat) (hl : 0 < l) (hm : 0 < m) (t : Fin (l + m) → Int)
    (h0 : t ⟨0, by clear hm; omega⟩ = -1) :
    t ⟨0, by clear h0 hl; omega⟩ = 1 := by
  sorry

-- 6. Non-`.bvar` argument to `private` auxiliary theorem in statement (`k1 = k2 = 0, r = 1`)
private theorem _posSucc (k : Nat) : 0 < k + 1 := Nat.zero_lt_succ k

theorem non_bvar_thm_aux (n : Nat) : (⟨0, _posSucc (n + 1)⟩ : Fin ((n + 1) + 1)).val = 0 := by
  sorry

-- 7. Structure constructor containing a `match` expression (`stripConstExprs`)
structure PairZero (p : Int × Bool) : Prop where
  ok : (match p with | (a, _) => a) = 0

theorem struct_ctor_matcher (p : Int × Bool) (h : PairZero p) : p.1 = 0 := by
  sorry

-- 8. Polymorphic disproof universe solver edge cases
theorem max_before_param (x : ULift.{max u v} Nat) (α : Type u) (β : Type v) : False := by
  sorry

theorem check_copy_paste (α : Type u) (β : Type v) (γ : Sort (max (u + 1) (v + 1))) : False := by
  sorry

theorem comm_max (α : Type u) (β : Type v) (γ : Type (max u v)) : γ = γ → False := by
  sorry

-- 9. Auto-discovered definition hole (`hole`) combined with `let` binding and nested `by omega`
def hole : Nat := sorry

theorem def_hole_let (l : Nat) (ha : l < 10) :
    let m : Nat := l + 1
    ∀ (t : Fin (m + hole * 0) → Int), t ⟨0, by omega⟩ = -1 → t ⟨0, by omega⟩ = Int.ofNat hole + 1 := by
  sorry

-- 10. `Solution` reuses one cached auxiliary proof across same-arg and extra-hyp call sites
theorem reused_sol_aux (l : Nat) (t : Fin (l + 1) → Int)
    (h1 : t ⟨0, by omega⟩ = -1)
    (h2 : ∀ (m : Nat), m = m → t ⟨0, by omega⟩ = -1) :
    t ⟨0, by omega⟩ = 1 := by
  sorry

-- 11. Auxiliary theorem taking both leading `.bvar` and trailing non-`.bvar` (`n + 1`)
private theorem _boundChal (l k : Nat) : 0 < l + k + 1 := by omega

def mkFinMixed (u l n : Nat) : Fin (l + (n + 1) + 1) := ⟨u * 0, _boundChal l (n + 1)⟩

theorem mixed_bvar_nonbvar (u l n : Nat) : (mkFinMixed u l n).val = u * 0 := by
  sorry

-- 12. `let` vs `have` binding across a definition hole (`hole`) with nested `by omega`
theorem have_vs_let_hole (n : Nat) :
    let d : Nat := 0
    ∀ (t : Fin ((n + 1) + d + hole * 0) → Int), t ⟨0, by omega⟩ = -1 → t ⟨0, by omega⟩ = 1 := by
  sorry

-- 13. Polymorphic disproof universe narrowing & `imax` before rigid params
theorem poly_max_narrow (α : Type (max u v)) (β : Type (max u w)) :
    α = α ∧ β = β → False := by
  sorry

theorem poly_imax_fn (γ : Sort (imax u v)) (α : Sort u) (β : Sort v) : False := by
  sorry

private theorem _uaux (_α : Type u) : 0 < 1 := by decide

theorem poly_unused (α : Type u) : (⟨0, _uaux α⟩ : Fin 1).val = 1 := by
  sorry

-- 14. User-named `private def` helper and lazy `let` unfolding in `.disproof`
private def privStep (n : Nat) : Nat := n + 1

theorem thm_priv (n : Nat) : privStep n = n + 2 := by
  sorry

theorem let_unfold_body (n : Nat) :
    let m : Nat := n + 1
    m = 0 := by
  sorry

-- 15. Mutual safe `.defnInfo` (`d.all != [d.name]`), `partial def` (`.opaqueInfo`), and depth-24 polymorphic DAG
mutual
  def dualAux.match_1 : Nat → Nat
    | 0 => 0
    | n + 1 => dualAux.match_2 n
  def dualAux.match_2 : Nat → Nat
    | 0 => 1
    | n + 1 => dualAux.match_1 n
end

def useDualAux (n : Nat) : Nat := dualAux.match_1 n

theorem mutual_all_aux_disproof (n : Nat) : useDualAux n = 1 := by
  sorry

structure PairSumZero where
  p : Nat × Nat
  ok : (let (a, b) := p; a + b) = 0

partial def loopPair (q : Nat × Nat) : Nat :=
  let (a, b) := q
  if a == 0 then b else loopPair (a - 1, b + 1)

theorem struct_and_opaque_aux_disproof (x : PairSumZero) :
    x.p = (1, 0) ∧ loopPair x.p = 99 := by
  sorry

def _s0 (α : Type u) (x : Nat) : Nat := x
def _s1 (α : Type u) (x : Nat) : Nat := _s0 α x + _s0 α x
def _s2 (α : Type u) (x : Nat) : Nat := _s1 α x + _s1 α x
def _s3 (α : Type u) (x : Nat) : Nat := _s2 α x + _s2 α x
def _s4 (α : Type u) (x : Nat) : Nat := _s3 α x + _s3 α x
def _s5 (α : Type u) (x : Nat) : Nat := _s4 α x + _s4 α x
def _s6 (α : Type u) (x : Nat) : Nat := _s5 α x + _s5 α x
def _s7 (α : Type u) (x : Nat) : Nat := _s6 α x + _s6 α x
def _s8 (α : Type u) (x : Nat) : Nat := _s7 α x + _s7 α x
def _s9 (α : Type u) (x : Nat) : Nat := _s8 α x + _s8 α x
def _s10 (α : Type u) (x : Nat) : Nat := _s9 α x + _s9 α x
def _s11 (α : Type u) (x : Nat) : Nat := _s10 α x + _s10 α x
def _s12 (α : Type u) (x : Nat) : Nat := _s11 α x + _s11 α x
def _s13 (α : Type u) (x : Nat) : Nat := _s12 α x + _s12 α x
def _s14 (α : Type u) (x : Nat) : Nat := _s13 α x + _s13 α x
def _s15 (α : Type u) (x : Nat) : Nat := _s14 α x + _s14 α x
def _s16 (α : Type u) (x : Nat) : Nat := _s15 α x + _s15 α x
def _s17 (α : Type u) (x : Nat) : Nat := _s16 α x + _s16 α x
def _s18 (α : Type u) (x : Nat) : Nat := _s17 α x + _s17 α x
def _s19 (α : Type u) (x : Nat) : Nat := _s18 α x + _s18 α x
def _s20 (α : Type u) (x : Nat) : Nat := _s19 α x + _s19 α x
def _s21 (α : Type u) (x : Nat) : Nat := _s20 α x + _s20 α x
def _s22 (α : Type u) (x : Nat) : Nat := _s21 α x + _s21 α x
def _s23 (α : Type u) (x : Nat) : Nat := _s22 α x + _s22 α x
def _s24 (α : Type u) (x : Nat) : Nat := _s23 α x + _s23 α x

theorem poly_dag_aux_disproof (α : Type u) : _s24 α 0 = 1 := by
  sorry
