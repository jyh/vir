/-
OBJECT-DEFLATE under X1 (a): Safety's proof (STATUS-vir 293 (b); S-16), mode by mode. For each mode: its `stepS` (Fit.lean), its
result store as a World over an UPDATED cell function, and `Φ` (Measure.lean, written before this file) strictly decreasing.
The invariant `Inv` (S-16's conjuncts) is added here as the proofs reach each premise. This file grows per row.
-/
import VIRDeflate.Measure

namespace VIRDeflate.Step
open VIRL1 VIRL2

/-- The cell function after a `READ` request of k bits returning to rt (`reqH`'s five stores). -/
def reqF (f : Int → Int) (k rt : Int) : Int → Int :=
  Function.update (Function.update (Function.update (Function.update (Function.update f 2068 k) 2069 0) 2070 1) 2071 rt) 0 2

theorem World.req {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2072 ≤ L) (k rt : Int) :
    World ⟨reqH σ.H p k rt, σ.R⟩ p L (reqF f k rt) := by
  unfold reqH reqF
  exact ((((hw.store (i := 2068) (by norm_num) (by omega)).store (i := 2069) (by norm_num) (by omega)).store (i := 2070)
    (by norm_num) (by omega)).store (i := 2071) (by norm_num) (by omega)).store (i := 0) (by norm_num) (by omega)

/-- The simp set that evaluates `Φ` on an updated cell function. -/
macro "phisimp" : tactic => `(tactic| simp [Φ, LOC, TBL, BITS, OUT, Function.update_apply, cMODE, cBY, cBI, cN, cM, cOUTMAX,
  cTB, cTI, cFILL, cPHASE, cINDEX, cX, cTGT, cHLIT, cHDIST, cHCLEN, cPEND, mTABLE, mHDR, mREAD, mHDRB, mHDRD, mSHDR, mFIXLENS,
  mDHDR, mSLEN, mSNLEN, mSCOPY, mBUILD, mLENS, mSYM, mDECODE, mSYMD, mLENX, mDSTD, mDSTX, mCOPY, mDH2, mDH3, mDH4, mCLREAD,
  mCLPUT, mLSYM, mLREP, mREP, mDONE, mREJECT])

/-- **HDR:** Φ drops (LOC 1 → READ's 0; nothing else moves). -/
theorem Φ_hdr {f : Int → Int} (hm : f cMODE = mHDR) : Φ (reqF f 1 3) < Φ f := by
  simp only [reqF]
  simp only [cMODE, mHDR] at hm
  phisimp
  simp [hm]

theorem safe_hdr {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (hm : f cMODE = mHDR) :
    stepS p σ = some ⟨reqH σ.H p 1 3, σ.R⟩ ∧ World ⟨reqH σ.H p 1 3, σ.R⟩ p L (reqF f 1 3) ∧ Φ (reqF f 1 3) < Φ f :=
  ⟨stepS_hdr hw hL hm, hw.req (by omega) 1 3, Φ_hdr hm⟩

end VIRDeflate.Step
