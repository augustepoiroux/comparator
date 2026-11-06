theorem thm_nonbvar.disproof
    (h : ∀ (n : Nat), (⟨0, by grind⟩ : Fin ((n + 1) + 1)).val = 1) : False := by
  exact absurd (h 0) (by decide)

theorem thm_nonbvar_direct (n : Nat) : (⟨0, by grind⟩ : Fin ((n + 1) + 1)).val = 0 := rfl
