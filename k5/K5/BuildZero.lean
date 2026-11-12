/-
  O95, K5-2: BUILD phase 0's CELL path (j < 16: count[j] := 0, j := j + 1), the one BUILD path no trace covered
  (found by the 69th head while wrapping BUILD; RANGE-SITES did not list it as open). Same walk as `build_zero_end_inR`.
-/
import K5.Modes3

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate.Step

set_option maxHeartbeats 4000000 in
theorem build_zero_cell_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (j X tbb : Int) (hph : f cPHASE = 0) (hj : f cINDEX = j) (hX : f cX = X) (htbb : f (X + 7) = tbb)
    (hX0 : 0 ≤ X) (hXL : X + 8 < L) (hj16 : j < 16) (hj0 : 0 ≤ j) (ht0 : 0 ≤ tbb) (htL : tbb + 16 ≤ L)
    (rr1 : inRange (X + 7) = true) (rr2 : inRange (tbb + j) = true) (rr3 : inRange (j + 1) = true) :
    SrcInRange (closeAt p buildT, σ) := by
  simp only [cPHASE, cINDEX, cX] at hph hj hX
  have g12 := hw.get (i := 12) (by decide) (by omega) hph
  have g13 := hw.get (i := 13) (by decide) (by omega) hj
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g7 := hw.get (i := X + 7) (by omega) (by omega) htbb
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr1, rr2, rr3, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, buildT, buildN, cPHASE, cINDEX, cX, cCODE, cCHK, cLEFT, cREST, cTOTAL, bZeroN, g12, g13, g79, g7, hj16, show (12 : Int) < L by omega, show (13 : Int) < L by omega,
    show (2079 : Int) < L by omega, show (0 : Int) ≤ X + 7 by omega, show X + 7 < L by omega,
    show (0 : Int) ≤ tbb + j by omega, show tbb + j < L by omega])

end K5
