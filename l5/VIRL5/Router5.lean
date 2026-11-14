/-
  O95 layer L5, Lean arm (STATUS 319, LV8 (b); LV8-MAP Addendum 9). The L3 router re-expressed over the library. F walks no region,
  so no routine replaces any of it (LV9's router cell is 0, declared before this file): F₅ is F's embedding. R4₅ is R4
  (OBJECT-L3 §3.3) over ⊢₅, with the same precondition and the same `postF`. It is carried by the generic `triple_ι`, citing no
  routine's triple and no routine's body: LV8's count is 0, and VACUOUSLY so.
-/
import VIRL5.EmbedTriple5
import VIRL3.RouterTriple

namespace VIRL5
open VIRL1 VIRL2 VIRL3

/-- The router over L5: F embedded (no sub-term of F is a routine's loop). -/
def F₅ : Tm₅ := ιE F

/-- Closing F₅ at the world p is embedding F closed at p (ιE commutes with substitution). -/
theorem F₅_closeAt (p : Int) : F₅.subst 0 (.const (.cap p)) = ιE (closeAt p F) := by
  rw [closeAt, ιE_subst]; rfl

/-- **R4₅.** R4 for the re-expressed router: from the world alone, F₅ returns the world p, hands nothing back, and leaves the
contents `postF f p`. -/
theorem R4₅ {p : Int} {f : Int → Int} (hs0 : 0 ≤ SvA f p) (hs4 : SvA f p < 4) (ht0 : 0 ≤ TvA f p) (ht4 : TvA f p < 4) :
    Triple₅ (RegionAt p 87 f) (F₅.subst 0 (.const (.cap p)))
      (fun v qs σ => v = .const (.cap p) ∧ qs = [] ∧ RegionAt p 87 (postF f p) σ) := by
  rw [F₅_closeAt]
  refine conseq₅ (fun _ h => h) (fun v qs σ h => ?_) (triple_ι (R4 hs0 hs4 ht0 ht4))
  obtain ⟨w, rfl, rfl, rfl, hR⟩ := h
  exact ⟨rfl, rfl, hR⟩

/-- R5's caller half over ⊢₅: R4₅ beside any frame the caller owns, by one application of frame₅. -/
theorem R5_frame₅ {p : Int} {f : Int → Int} (R : Assn) (hs0 : 0 ≤ SvA f p) (hs4 : SvA f p < 4) (ht0 : 0 ≤ TvA f p)
    (ht4 : TvA f p < 4) :
    Triple₅ (RegionAt p 87 f ∗ R) (F₅.subst 0 (.const (.cap p)))
      (fun v qs => (fun σ => v = .const (.cap p) ∧ qs = [] ∧ RegionAt p 87 (postF f p) σ) ∗ R) :=
  frame₅ R (R4₅ hs0 hs4 ht0 ht4)

end VIRL5
