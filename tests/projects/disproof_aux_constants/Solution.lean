universe u v w

-- 1. Disproof of `nested_proof`: mints `nested_proof.disproof._proof_1`
theorem nested_proof.disproof
    (h : ∀ (l : Nat) (t : Fin (l + 1) → Int), t ⟨0, by omega⟩ = -1 → t ⟨0, by omega⟩ = 1) : False := by
  exact absurd (h 0 (fun _ => -1) rfl) (by decide)

-- 2. Disproof of `let_matcher`: mints `let_matcher.disproof.match_1`
def runWitness (n : Nat) : Nat × Nat := (n, n + 1)

theorem let_matcher.disproof
    (h : ∀ (n : Nat), let (a, b) := runWitness n; a = b) : False := by
  have := h 0
  dsimp [runWitness] at this
  omega

-- 3. Earlier `private` helpers cache `.match_1` first
def pairFn (k : Nat) : Int × Int := (Int.ofNat k, -Int.ofNat k)

private theorem myHelper (p : Int × Int) : (match p with | (a, b) => a + b) = p.1 + p.2 := rfl

theorem helper_cached_matcher.disproof
    (h : ∀ (k : Nat), (match pairFn k with | (a, b) => a + b) = 1) : False := by
  have := h 0
  rw [myHelper] at this
  dsimp [pairFn] at this
  omega

private theorem directHelper (p : Bool × Bool) : (let (a, b) := p; a && b) = (p.1 && p.2) := rfl

theorem direct_proof_helper_matcher (p : Bool × Bool) :
    (let (a, b) := p; a == b) = (p.1 == p.2) := by
  cases p
  rfl

-- 4. Polymorphic matcher specialization & collapse
theorem poly_matcher.disproof
    (h : ∀ (α : Type 0) (p : α × α) (β : Type 1) (x y : β),
      (let (a, b) := p; a = b) ∧ x = y) : False := by
  have ⟨h1, _⟩ := h Bool (true, false) PUnit.{2} PUnit.unit.{2} PUnit.unit.{2}
  cases h1

theorem ulift_matcher_collapse.disproof
    (h : ∀ (p : ULift.{0} Nat × Nat) (q : ULift.{0} Nat × Nat),
      (let (a, b) := p; a.down + b) + (let (c, d) := q; c.down + d) = 1) : False := by
  have := h (⟨0⟩, 0) (⟨0⟩, 0)
  omega

-- 5. Single reused `.disproof._proof_1` matching `Challenge`'s `_proof_1` and `_proof_2`
theorem omega_diff_hyps.disproof
    (h : ∀ (l m : Nat) (hl : 0 < l) (hm : 0 < m) (t : Fin (l + m) → Int),
      t ⟨0, by omega⟩ = -1 → t ⟨0, by omega⟩ = 1) : False := by
  exact absurd (h 1 1 (by omega) (by omega) (fun _ => -1) rfl) (by decide)

-- 6. Renamed `private` auxiliary theorem applied to non-`.bvar` `n + 1` in theorem statement
private theorem _posSuccSol (k : Nat) : 0 < k + 1 := Nat.zero_lt_succ k

theorem non_bvar_thm_aux (n : Nat) : (⟨0, _posSuccSol (n + 1)⟩ : Fin ((n + 1) + 1)).val = 0 := rfl

-- 7. `pairFirst` caches `_private.Solution.0.pairFirst.match_1` before `structure PairZero`
private theorem pairFirst (p : Int × Bool) : (match p with | (a, _) => a) = p.1 := rfl

structure PairZero (p : Int × Bool) : Prop where
  ok : (match p with | (a, _) => a) = 0

theorem struct_ctor_matcher (p : Int × Bool) (h : PairZero p) : p.1 = 0 := by
  have := h.ok
  rw [pairFirst] at this
  exact this

-- 8. Polymorphic disproof universe solver edge cases
theorem max_before_param.disproof
    (h : ∀ (_x : ULift.{1} Nat) (_α : Type 0) (_β : Type 1), False) : False :=
  h ⟨0⟩ PUnit Type

theorem check_copy_paste.disproof
    (h : ∀ (_α : Type u) (_β : Type v) (_γ : Type (max u v)), False) : False :=
  h PUnit PUnit PUnit

theorem comm_max.disproof
    (h : ∀ (_α : Type u) (_β : Type v) (γ : Type (max v u)), γ = γ → False) : False :=
  h PUnit PUnit PUnit rfl

-- 9. Filling `hole` + disproof of `def_hole_let` (`letVal?` + `allDefinitionTargets`)
def hole : Nat := 0

theorem def_hole_let.disproof
    (h : ∀ (l : Nat), l < 10 →
      (let m : Nat := l + 1
       ∀ (t : Fin (m + hole * 0) → Int), t ⟨0, by omega⟩ = -1 → t ⟨0, by omega⟩ = Int.ofNat hole + 1)) : False :=
  absurd (h 0 (by omega) (fun _ => -1) rfl) (by decide)

-- 10. `clear` causes `Solution` to reuse `.disproof._proof_1` across same-arg and extra-hyp calls
theorem reused_sol_aux.disproof
    (h : ∀ (l : Nat) (t : Fin (l + 1) → Int) (h1 : t ⟨0, by omega⟩ = -1)
      (_h2 : ∀ (m : Nat) (hm : m = m), t ⟨0, by clear h1 m hm; omega⟩ = -1),
      t ⟨0, by clear h1 _h2; omega⟩ = 1) : False :=
  absurd (h 0 (fun _ => -1) rfl (fun _ _ => rfl)) (by decide)

-- 11. Auxiliary theorem taking 2 leading `.bvar`s + trailing non-`.bvar` `n + 1`
private theorem _boundSol (_u l k : Nat) : 0 < l + k + 1 := by omega

def mkFinMixed (u l n : Nat) : Fin (l + (n + 1) + 1) := ⟨u * 0, _boundSol u l (n + 1)⟩

theorem mixed_bvar_nonbvar (u l n : Nat) : (mkFinMixed u l n).val = u * 0 := rfl

-- 12. `have` (`nonDep := true`) vs `let` (`nonDep := false`) across `hole`
theorem have_vs_let_hole.disproof
    (h : ∀ (n : Nat),
      have d : Nat := 0
      ∀ (t : Fin ((n + 1) + d + hole * 0) → Int), t ⟨0, by omega⟩ = -1 → t ⟨0, by omega⟩ = 1) : False :=
  absurd (h 0 (fun _ => -1) rfl) (by decide)

-- 13. Polymorphic disproof universe narrowing `(u, v, w) = (u, max u 1, u)` & `imax u v` before rigid `(1, 0)`
theorem poly_max_narrow.disproof
    (h : ∀ (α : Type (max u 1)) (β : Type u), α = α ∧ β = β → False) : False :=
  h PUnit PUnit ⟨rfl, rfl⟩

theorem poly_imax_fn.disproof
    (h : Prop → Type 0 → Prop → False) : False :=
  h True PUnit True

private theorem _saux (_x : Type 2) : 0 < 1 := by decide

theorem poly_unused.disproof
    (h : ∀ (_α : Type 0), (⟨0, _saux (Nat → Type 1)⟩ : Fin 1).val = 1) : False :=
  absurd (h Nat) (by decide)

-- 14. User-named `private def` helper and lazy `let` unfolding in `.disproof`
private def privStep (n : Nat) : Nat := n + 1

theorem thm_priv.disproof (h : ∀ (n : Nat), privStep n = n + 2) : False := by
  have := h 0
  dsimp [privStep] at this
  omega

theorem let_unfold_body.disproof
    (h : ∀ (n : Nat), let _m : Nat := n + 1; n + 1 = 0) : False :=
  absurd (h 0) (by decide)

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

theorem mutual_all_aux_disproof.disproof
    (h : ∀ (n : Nat), useDualAux n = 1) : False := by
  have := h 0
  contradiction

private def cachePairProp (q : Nat × Nat) : Nat :=
  let (a, b) := q
  a + b

structure PairSumZero where
  p : Nat × Nat
  ok : (let (a, b) := p; a + b) = 0

partial def loopPair (q : Nat × Nat) : Nat :=
  let (a, b) := q
  if a == 0 then b else loopPair (a - 1, b + 1)

theorem struct_and_opaque_aux_disproof.disproof
    (h : ∀ (x : PairSumZero), x.p = (1, 0) ∧ loopPair x.p = 99) : False := by
  have ⟨h0, _⟩ := h ⟨(0, 0), rfl⟩
  injection h0 with h1 _
  contradiction

def _t0 (α : Type 0) (x : Nat) : Nat := x
def _t1 (α : Type 0) (x : Nat) : Nat := _t0 α x + _t0 α x
def _t2 (α : Type 0) (x : Nat) : Nat := _t1 α x + _t1 α x
def _t3 (α : Type 0) (x : Nat) : Nat := _t2 α x + _t2 α x
def _t4 (α : Type 0) (x : Nat) : Nat := _t3 α x + _t3 α x
def _t5 (α : Type 0) (x : Nat) : Nat := _t4 α x + _t4 α x
def _t6 (α : Type 0) (x : Nat) : Nat := _t5 α x + _t5 α x
def _t7 (α : Type 0) (x : Nat) : Nat := _t6 α x + _t6 α x
def _t8 (α : Type 0) (x : Nat) : Nat := _t7 α x + _t7 α x
def _t9 (α : Type 0) (x : Nat) : Nat := _t8 α x + _t8 α x
def _t10 (α : Type 0) (x : Nat) : Nat := _t9 α x + _t9 α x
def _t11 (α : Type 0) (x : Nat) : Nat := _t10 α x + _t10 α x
def _t12 (α : Type 0) (x : Nat) : Nat := _t11 α x + _t11 α x
def _t13 (α : Type 0) (x : Nat) : Nat := _t12 α x + _t12 α x
def _t14 (α : Type 0) (x : Nat) : Nat := _t13 α x + _t13 α x
def _t15 (α : Type 0) (x : Nat) : Nat := _t14 α x + _t14 α x
def _t16 (α : Type 0) (x : Nat) : Nat := _t15 α x + _t15 α x
def _t17 (α : Type 0) (x : Nat) : Nat := _t16 α x + _t16 α x
def _t18 (α : Type 0) (x : Nat) : Nat := _t17 α x + _t17 α x
def _t19 (α : Type 0) (x : Nat) : Nat := _t18 α x + _t18 α x
def _t20 (α : Type 0) (x : Nat) : Nat := _t19 α x + _t19 α x
def _t21 (α : Type 0) (x : Nat) : Nat := _t20 α x + _t20 α x
def _t22 (α : Type 0) (x : Nat) : Nat := _t21 α x + _t21 α x
def _t23 (α : Type 0) (x : Nat) : Nat := _t22 α x + _t22 α x
def _t24 (α : Type 0) (x : Nat) : Nat := _t23 α x + _t23 α x

theorem poly_dag_aux_disproof.disproof (h : ∀ (α : Type 0), _t24 α 0 = 1) : False := by
  cases h Nat
