module

private theorem priv_helper (n : Nat) : n + 0 = n := rfl

public theorem comm (n m : Nat) : n + m = m + n := by
  grind

public theorem «comm\nwith_newline» (n : Nat) : n + 0 = n :=
  priv_helper n
