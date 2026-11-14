/-
  O95 layer L5, Lean arm (STATUS 321, LV8 assembly, LV8-MAP Addendum 5): Refine₅ on every mode whose ⟶₅ entry is DEFLATE's own
  — the 21 lifted modes, and every mode with no entry (DONE, REJECT, any other value). Terminal: j = 0 (`stepS_fixed`). Otherwise
  j = 1: `stepSafe` gives DEFLATE's step, `stepS₅_of_stepS` makes it the ⟶₅ step, and `stepS_sole` keeps the store Sole.
-/
import VIRL5.Dispatch5
import VIRL5.SolePres5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- The seven modes whose ⟶₅ entry is not DEFLATE's own. -/
def Reex (m : Int) : Prop := m = mREAD ∨ m = mFIXLENS ∨ m = mSCOPY ∨ m = mBUILD ∨ m = mDECODE ∨ m = mCOPY ∨ m = mREP

/-- Off the seven, the ⟶₅ entry is DEFLATE's (or both have none). -/
theorem lookup_lifted (m : Int) (hm : ¬ Reex m) : modes₅.lookup m = modesL.lookup m := by
  simp only [Reex, not_or] at hm
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hm
  have b1 : (m == mREAD) = false := by simpa using h1
  have b2 : (m == mFIXLENS) = false := by simpa using h2
  have b3 : (m == mSCOPY) = false := by simpa using h3
  have b4 : (m == mBUILD) = false := by simpa using h4
  have b5 : (m == mDECODE) = false := by simpa using h5
  have b6 : (m == mCOPY) = false := by simpa using h6
  have b7 : (m == mREP) = false := by simpa using h7
  simp [modes₅, modesL, modes, List.lookup, lift₅, b1, b2, b3, b4, b5, b6, b7]

/-- **Refine₅ off the seven re-expressed modes.** -/
theorem refine_lifted (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (σ : Store) (f : Int → Int)
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hs : Sole σ p (L0 b.size om)) (hi : Inv b om lit f)
    (hm : ¬ Reex (f cMODE)) :
    ∃ j σ', stepS₅ p σ = some σ' ∧ iterS p j σ = some σ' ∧ Sole σ' p (L0 b.size om) ∧
      (f cMODE ≠ mDONE → f cMODE ≠ mREJECT → 1 ≤ j) := by
  have hL : 0 < L0 b.size om := by unfold L0; omega
  have hl := lookup_lifted (f cMODE) hm
  by_cases ht : f cMODE = mDONE ∨ f cMODE = mREJECT
  · exact ⟨0, σ, stepS₅_of_stepS hw hL hl (stepS_fixed hw hL ht), rfl, hs,
      fun hd hr => absurd ht (by push Not; exact ⟨hd, hr⟩)⟩
  · push Not at ht
    obtain ⟨σ', f', hst, -, -, -⟩ := stepSafe b om lit p σ f hb hw hi ht.1 ht.2
    exact ⟨1, σ', stepS₅_of_stepS hw hL hl hst, by simp [iterS, hst], stepS_sole hs hst, fun _ _ => le_refl _⟩

end VIRL5
