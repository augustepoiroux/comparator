private theorem _posSucc (k : Nat) : 0 < k + 1 := Nat.zero_lt_succ k

theorem thm_nonbvar (n : Nat) : (⟨0, _posSucc (n + 1)⟩ : Fin ((n + 1) + 1)).val = 1 := by
  sorry

theorem thm_nonbvar_direct (n : Nat) : (⟨0, _posSucc (n + 1)⟩ : Fin ((n + 1) + 1)).val = 0 := by
  sorry
