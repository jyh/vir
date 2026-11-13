/-
  O95, row 298 (compiler/DECLARATIONS-K5.md Addendum 7): a loader that discharges S2's layout premise. GENERIC: no DEFLATE constant.
  L-1 `loader_ok`: the scaled loader (cell i of the region based at p sits at byte 8·(p + i)) satisfies `Layout` and `MemRel` for any
  WF store whose regions lie in [0, 2⁶⁰) and whose live cells hold in-range ints.
-/
import VIRC.NoOvfSrc

namespace K5
open VIRL1 VIRL2 VIRC

/-- The scaled loader: region p at byte address 8·p. -/
def scaleLay (p : Int) : W := BitVec.ofInt 64 (8 * p)

/-- Its memory: the word at byte address a is the cell a / 8 (0 where no cell is live). -/
def scaleMem (σ : Store) : WMem := fun a => BitVec.ofInt 64 ((σ.H.lookup ((a.toNat / 8 : Nat) : Int)).getD 0)

/-- Every live region lies in [0, 2⁶⁰). -/
def Placed (σ : Store) : Prop := ∀ p n, σ.R.lookup p = some n → 0 ≤ p ∧ p + n ≤ 2 ^ 60

/-- Every live cell holds an in-range int. -/
def CellsInR (σ : Store) : Prop := ∀ a v, σ.H.lookup a = some v → inRange v = true

theorem scaleLay_toNat {p : Int} (h0 : 0 ≤ p) (h1 : p ≤ 2 ^ 60) : (scaleLay p).toNat = (8 * p).toNat := by
  unfold scaleLay
  rw [BitVec.toNat_ofInt]
  have h64 : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := by decide
  rw [h64, Int.emod_eq_of_lt (by omega) (by omega)]

theorem region_disj {σ : Store} (hw : σ.WF) {p q : Int} {n m : Nat} (hp : σ.R.lookup p = some n)
    (hq : σ.R.lookup q = some m) (hne : p ≠ q) : p + n ≤ q ∨ q + m ≤ p := by
  have hn := hw.pos p n hp
  have hm := hw.pos q m hq
  have h1 := hw.disj p q n m hp hq hne p ⟨le_refl _, by omega⟩
  have h2 := hw.disj p q n m hp hq hne q
  simp only [Store.InRegion, not_and, not_lt] at h1 h2
  by_cases hpq : p < q
  · left
    by_contra hc
    exact absurd (h2 ⟨by omega, by omega⟩) (by simp; omega)
  · right
    by_contra hc
    have := h1 (by omega)
    omega

theorem cell_mem {σ : Store} (hw : σ.WF) {p : Int} {n : Nat} (hp : σ.R.lookup p = some n) {i : Nat} (hi : i < n) :
    ∃ v, σ.H.lookup (p + i) = some v := by
  have hmem : (p + i) ∈ σ.H := (hw.domH (p + i)).mpr ⟨p, n, hp, by simp [Store.InRegion]; omega⟩
  exact Option.isSome_iff_exists.mp (Finmap.lookup_isSome.mpr hmem)

/-- **L-1.** -/
theorem loader_ok {σ : Store} (hw : σ.WF) (hpl : Placed σ) (hc : CellsInR σ) :
    Layout σ scaleLay ∧ MemRel scaleLay σ (scaleMem σ) := by
  refine ⟨⟨hw, ?_, ?_, ?_⟩, ?_⟩
  · intro p n hp
    obtain ⟨h0, h1⟩ := hpl p n hp
    rw [scaleLay_toNat h0 (by omega)]
    constructor <;> omega
  · intro p q n m hp hq hne
    obtain ⟨hp0, hp1⟩ := hpl p n hp
    obtain ⟨hq0, hq1⟩ := hpl q m hq
    rw [scaleLay_toNat hp0 (by omega), scaleLay_toNat hq0 (by omega)]
    rcases region_disj hw hp hq hne with h | h
    · left; omega
    · right; omega
  · intro p n hp i hi
    obtain ⟨v, hv⟩ := cell_mem hw hp hi
    exact ⟨v, hv, hc _ _ hv⟩
  · intro p n hp i hi v hv
    obtain ⟨h0, h1⟩ := hpl p n hp
    have hA : (cellAddr (scaleLay p) (BitVec.ofNat 64 i)).toNat = (8 * p).toNat + 8 * i := by
      rw [cellAddr_toNat _ _ (by rw [scaleLay_toNat h0 (by omega)]; omega), scaleLay_toNat h0 (by omega)]
    have hk : (((cellAddr (scaleLay p) (BitVec.ofNat 64 i)).toNat / 8 : Nat) : Int) = p + i := by
      rw [hA]; omega
    show BitVec.ofInt 64 ((σ.H.lookup (((cellAddr (scaleLay p) (BitVec.ofNat 64 i)).toNat / 8 : Nat) : Int)).getD 0) = _
    rw [hk, hv]; rfl

end K5
