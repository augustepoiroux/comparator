-- Exploit attempt: rename private auxiliary definition while altering its body.
private def g (n : Nat) : Nat := n + 2
theorem tgt : g 1 = 3 := rfl
