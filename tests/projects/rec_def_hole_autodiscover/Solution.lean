def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

def wfSumTo (n : Nat) : Nat :=
  if _ : n = 0 then 0 else wfSumTo (n - 1) + n
termination_by n

theorem sumTo_two : sumTo 2 = 3 := rfl
theorem wfSumTo_two : wfSumTo 2 = 3 := by simp [wfSumTo]
