def secret : Nat := 999

theorem thm_tamper.disproof
    (h : (⟨0, by decide⟩ : Fin 1).val = 1) : False := by
  exact absurd h (by decide)
