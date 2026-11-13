import VIRL2.Store
open VIRL1 VIRL2
theorem opStep_load_inv {vs : List Atom₂} {σ σ' : Store} {v : Atom₂} (h : opStep .load vs σ = some (v, σ')) :
    ∃ p i w, Store.load p i σ = some w ∧ v = .const (.int w) ∧ σ' = σ := by
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp [opStep] at h
  · simp [opStep] at h
  · cases a <;> cases b <;> simp [opStep] at h
    all_goals first
      | (rename_i c₁ c₂; cases c₁ <;> cases c₂ <;> simp [opStep] at h <;>
          (obtain ⟨w, hw, rfl, rfl⟩ := h; exact ⟨_, _, w, hw, rfl, rfl⟩))
      | (rename_i c₁; cases c₁ <;> simp [opStep] at h)
  · simp [opStep] at h
theorem opStep_store_inv {vs : List Atom₂} {σ σ' : Store} {v : Atom₂} (h : opStep .store vs σ = some (v, σ')) :
    ∃ p i w, vs = [.const (.cap p), .const (.int i), .const (.int w)] ∧ Store.store p i w σ = some σ' ∧ v = .const (.cap p) := by
  match vs, h with
  | [.const (.cap p), .const (.int i), .const (.int w)], h => by
      simp only [opStep, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨s, hs, rfl, rfl⟩ := h
      exact ⟨p, i, w, rfl, hs, rfl⟩
  | [], h => by simp [opStep] at h
  | _, h => by sorry
