import Mathlib.Data.Nat.Factorial.Basic

theorem challenge_factorial (n : Nat) : Nat.factorial n > 0 :=
  Nat.factorial_pos n
