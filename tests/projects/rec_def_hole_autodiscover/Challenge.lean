def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + sorry

def wfSumTo (n : Nat) : Nat :=
  if _ : n = 0 then 0 else wfSumTo (n - 1) + sorry
termination_by n

theorem sumTo_two : sumTo 2 = 3 := sorry
theorem wfSumTo_two : wfSumTo 2 = 3 := sorry
