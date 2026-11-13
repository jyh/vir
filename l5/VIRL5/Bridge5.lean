/-
  O95 layer L5, Lean arm (STATUS 318, LV8 Deflate5, BRIDGE (i) of BANK-72): the routines' triples speak `RegionAt p n f` (EXACT
  ownership, ABSOLUTE addresses: cell a holds f a, and σ holds nothing else); DEFLATE's lemmas speak `World σ p L f` (lookup-based,
  RELATIVE addresses: cell p + i holds f i, and nothing is said of other cells). The two agree on a store that owns the one region
  and nothing else (`Sole`), which DEFLATE's `initStore` does. One lemma each way, plus `initStore_sole`.
-/
import VIRL5.Run5
import VIRDeflate.Statements

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- σ owns the one region at p of length L and no other cell. -/
def Sole (σ : Store) (p : Int) (L : Nat) : Prop :=
  σ.R = Finmap.singleton p L ∧ ∀ a, ¬ Store.InRegion a p L → σ.H.lookup a = none

/-- RegionAt (absolute) gives World (relative), and the store is Sole. -/
theorem RegionAt.world {p : Int} {L : Nat} {g : Int → Int} {σ : Store} (h : RegionAt p L g σ) :
    World σ p L (fun i => g (p + i)) ∧ Sole σ p L := by
  refine ⟨⟨?_, fun i h0 hL => ?_⟩, h.1, fun a ha => ?_⟩
  · rw [h.1]; simp
  · rw [h.2 (p + i), if_pos (by simp [Store.InRegion]; omega)]
  · rw [h.2 a, if_neg ha]

/-- World (relative) on a Sole store gives RegionAt (absolute). -/
theorem World.regionAt {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hs : Sole σ p L) :
    RegionAt p L (fun a => f (a - p)) σ := by
  refine ⟨hs.1, fun a => ?_⟩
  by_cases ha : Store.InRegion a p L
  · rw [if_pos ha]
    have e := hw.cell (a - p) (by simp [Store.InRegion] at ha; omega) (by simp [Store.InRegion] at ha; omega)
    rw [show p + (a - p) = a by omega] at e
    exact e
  · rw [if_neg ha]; exact hs.2 a ha

/-- DEFLATE's initial store owns its one region and nothing else. -/
theorem initStore_sole (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) :
    Sole (initStore b om lit p) p (L0 b.size om) := by
  refine ⟨rfl, fun a ha => ?_⟩
  simp only [initStore, lookup_fillF]
  rw [if_neg (by simpa [Store.InRegion] using ha)]
  simp

end VIRL5
