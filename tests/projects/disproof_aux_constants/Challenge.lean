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
set_option linter.checkUnivs false in
theorem poly_max_narrow (α : Type (max u v)) (β : Type (max u w)) :
    α = α ∧ β = β → False := by
  sorry

theorem poly_imax_fn (γ : Sort (imax u v)) (α : Sort u) (β : Sort v) : False := by
  sorry

private theorem _uaux (_α : Type u) : 0 < 1 := by decide

theorem poly_unused (α : Type u) : (⟨0, _uaux α⟩ : Fin 1).val = 1 := by
  sorry
