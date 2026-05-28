/- Proves disproof under a structure target with varying field universe levels. -/
structure MyStruct.{u} where
  A : Type u
  B : Prop

theorem foo.disproof : ∃ (s : MyStruct.{1}), ∃ (h : s.B), ¬ False :=
  ⟨⟨PUnit.{2}, True⟩, True.intro, fun h => h⟩
