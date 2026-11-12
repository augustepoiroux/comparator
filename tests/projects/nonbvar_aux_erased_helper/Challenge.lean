-- Regression test:
-- 1) A challenge-only helper (`limit_pos`) used solely inside an erased non-bvar argument
--    of an auxiliary proof (`_ofPos limit_pos`) is proof-irrelevant even when unrelated
--    definition holes (`hole`) exist.
-- 2) Closed aux applications inside and outside binders mentioning `hole` must verify
--    independently of conjunct order.
def hole : Nat := sorry
def limit : Nat := 10
theorem limit_pos : 0 < limit := by decide
private theorem _ofPos {n : Nat} (h : 0 < n) : 0 < n * 2 := Nat.mul_pos h (by decide)

theorem tgt : (⟨0, _ofPos limit_pos⟩ : Fin (limit * 2)).val = 1 := sorry
theorem tgt_direct : (⟨0, _ofPos limit_pos⟩ : Fin (limit * 2)).val = 0 := sorry
theorem tgt_order_a : (⟨0, _ofPos limit_pos⟩ : Fin (limit * 2)).val = 0 ∧
    ∀ (h : hole = 5), (⟨0, _ofPos limit_pos⟩ : Fin (limit * 2)).val = 0 ∧ h = h := sorry
theorem tgt_order_b : (∀ (h : hole = 5), (⟨0, _ofPos limit_pos⟩ : Fin (limit * 2)).val = 0 ∧ h = h) ∧
    (⟨0, _ofPos limit_pos⟩ : Fin (limit * 2)).val = 0 := sorry
