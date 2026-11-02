import VIRP
open VIRP
-- MUTANT (must be RED): the frame theorem WITHOUT the disjointness premise — every location unchanged. The emit path
-- decrements the sender's cell, so this is false; the same proof script stops where `hd` was used.
theorem frame_bad {σ σ' : Store} {ℓ : Label} (h : denote F env0 σ = Part.some (σ', ℓ))
    (hf : Frag) : ∀ l, hf l ≠ none → σ'.read l = σ.read l := by
  intro l hl
  rcases F_effect h with rfl | rfl
  · rfl
  · cases l with
    | wire i => rfl
    | bucket q => simp [Store.read, Store.dec]
