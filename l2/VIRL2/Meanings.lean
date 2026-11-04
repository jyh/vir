/-
  O95 layer L2, Lean arm. The meanings inputs/L2-programs.md names for M1–M4, from runs and soundness₂ (OBJECT-L2 §6):
  ⟦M1⟧₂ σ₀ = (7, σ₀) · ⟦M2⟧₂ σ₀ = (5, σ₀) · ⟦M3⟧₂ σ₀ = ⊥ (a fault) · ⟦M4⟧₂ σ₀ = (0, σ₁) with σ₁'s R ≠ ∅.
-/
import VIRL2.Denot2
import VIRL2.Triples

namespace VIRL2
open VIRL1

theorem M1_meaning : den₂ (M1, Store.empty) = Part.some (ci 7, Store.empty) := by
  have h := run₂_steps 20 (M1, Store.empty)
  have he : run₂ 20 (M1, Store.empty) = (.ret (ci 7), Store.empty) := rfl
  rw [he] at h; exact den₂_of_steps h rfl

theorem M2_meaning : den₂ (M2, Store.empty) = Part.some (ci 5, Store.empty) := by
  have h := run₂_steps 20 (M2, Store.empty)
  have he : run₂ 20 (M2, Store.empty) = (.ret (ci 5), Store.empty) := rfl
  rw [he] at h; exact den₂_of_steps h rfl

theorem M3_meaning : den₂ (M3, Store.empty) = Part.none := by
  rw [soundness₂_steps (run₂_steps 20 (M3, Store.empty))]
  have he : run₂ 20 (M3, Store.empty) = ((run₂ 20 (M3, Store.empty)).1, (run₂ 20 (M3, Store.empty)).2) := rfl
  rw [he, M3_stuck]
  exact den₂_fault rfl rfl

theorem M4_meaning : ∃ σ₁ : Store, den₂ (M4, Store.empty) = Part.some (ci 0, σ₁) ∧ σ₁.R.lookup 0 = some 1 := by
  refine ⟨(run₂ 20 (M4, Store.empty)).2, ?_, rfl⟩
  have h := run₂_steps 20 (M4, Store.empty)
  have he : run₂ 20 (M4, Store.empty) = (.ret (ci 0), (run₂ 20 (M4, Store.empty)).2) := by rw [← M4_run]
  rw [he] at h; exact den₂_of_steps h rfl

end VIRL2
