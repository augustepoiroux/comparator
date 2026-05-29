structure MyStruct.{u} (α : Type u) where
  A : α

theorem foo.disproof : ∃ (s : MyStruct.{1} Type), ∃ (x : s.A), ¬ False :=
  ⟨⟨PUnit.{1}⟩, PUnit.unit.{1}, fun h => h⟩
