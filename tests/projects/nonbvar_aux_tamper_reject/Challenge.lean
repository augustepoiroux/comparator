-- Soundness regression test: replacing a private aux-theorem application (`_ignore rfl`)
-- with an inline non-aux proof term (`by decide` / `of_decide_eq_true`) must be rejected.
def secret : Nat := 42
private theorem _ignore (_ : secret = 42) : 0 < 1 := Nat.zero_lt_one

theorem thm_tamper : (⟨0, _ignore rfl⟩ : Fin 1).val = 1 := by
  sorry
