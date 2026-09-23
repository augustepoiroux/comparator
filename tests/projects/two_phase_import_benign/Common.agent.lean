def TargetProp : Prop := 1 + 1 = 2

theorem helper : 1 + 1 = 2 := by rfl
theorem shared_target : 2 + 2 = 4 := rfl
