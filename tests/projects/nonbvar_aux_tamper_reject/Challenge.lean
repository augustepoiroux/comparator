-- Soundness regression test: when peeling a non-`.bvar` auxiliary-theorem argument (`rfl`),
-- `collectChal` must still record all non-aux constants (`secret`) from the eliminated domain/arg.
def secret : Nat := 42
private theorem _ignore (_ : secret = 42) : 0 < 1 := Nat.zero_lt_one

theorem thm_tamper : (⟨0, _ignore rfl⟩ : Fin 1).val = 1 := by
  sorry
