/-
  SOLUTION DISPROOF: Specialized Type Equality

  What we are testing:
  This positive test verifies that a student is able to successfully disprove
  a polymorphic theorem that is only false under specialized assignments
  (u = v = 0 and α = β = PUnit).
-/
theorem weird.disproof : ∃ (α : Type 0), ∃ (β : Type 0), ULift.{0} α = ULift.{0} β := ⟨PUnit, PUnit, rfl⟩
