def hole : Nat := 5
def limit : Nat := 10
private theorem _mine : 0 < limit * 2 := by decide

theorem tgt.disproof : ¬ (⟨0, _mine⟩ : Fin (limit * 2)).val = 1 := by decide
theorem tgt_direct : (⟨0, _mine⟩ : Fin (limit * 2)).val = 0 := rfl
theorem tgt_order_a : (⟨0, _mine⟩ : Fin (limit * 2)).val = 0 ∧
    ∀ (h : hole = 5), (⟨0, _mine⟩ : Fin (limit * 2)).val = 0 ∧ h = h := ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
theorem tgt_order_b : (∀ (h : hole = 5), (⟨0, _mine⟩ : Fin (limit * 2)).val = 0 ∧ h = h) ∧
    (⟨0, _mine⟩ : Fin (limit * 2)).val = 0 := ⟨fun _ => ⟨rfl, rfl⟩, rfl⟩
