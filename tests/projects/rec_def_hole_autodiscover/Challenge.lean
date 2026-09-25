def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + sorry

theorem sumTo_two : sumTo 2 = 3 := sorry
