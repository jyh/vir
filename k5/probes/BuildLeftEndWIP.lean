/- K5-2 WIP (68th head): build_left_end on the checked runner after porter rounds k5p-040..048.
   OPEN: whnf heartbeat timeout under the walk (and fix.py added duplicate rrN facts). Not imported. -/
import K5.Modes3

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate.Step

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8000 in
theorem build_left_end_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (j X tbb left rest tot c1 var : Int) (hph : f cPHASE = 3) (hj : f cINDEX = j) (hX : f cX = X) (htbb : f (X + 7) = tbb)
    (hX0 : 0 ≤ X) (hXL : X + 8 < L) (hj15 : ¬ j ≤ 15) (ht0 : 0 ≤ tbb) (htL : tbb + 352 ≤ L)
    (hleft : f cLEFT = left) (hrest : f cREST = rest) (htot : f cTOTAL = tot) (hc1 : f (tbb + 1) = c1)
    (hvar : f (X + 8) = var)
    (rr1 : inRange (X + 7) = true)
    (rr2 : inRange (tbb + 1) = true) (rr3 : inRange (X + 7) = true)
    (rr4 : inRange (X + 8) = true) (rr5 : inRange (X + 7) = true) (rr6 : inRange (tbb + 1) = true) :
    SrcInRange (closeAt p buildT, σ) := by
  simp only [cPHASE, cINDEX, cX, cLEFT, cREST, cTOTAL] at hph hj hX hleft hrest htot
  have g12 := hw.get (i := 12) (by decide) (by omega) hph
  have g13 := hw.get (i := 13) (by decide) (by omega) hj
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g7 := hw.get (i := X + 7) (by omega) (by omega) htbb
  have g76 := hw.get (i := 2076) (by decide) (by omega) hleft
  have g77 := hw.get (i := 2077) (by decide) (by omega) hrest
  have g78 := hw.get (i := 2078) (by decide) (by omega) htot
  have gc1 := hw.get (i := tbb + 1) (by omega) (by omega) hc1
  have g8 := hw.get (i := X + 8) (by omega) (by omega) hvar
  by_cases a1 : c1 = 1 <;> by_cases a2 : rest = 0 <;> by_cases a3 : var = 1 <;> by_cases a4 : var = 2 <;>
    by_cases a5 : tot = 0 <;> by_cases a6 : 0 < left <;>
    repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr4, rr5, rr6, rr2, rr3, rr1, a1, a2, a3, a4, a5, a6, g12, g13, g79, g7, g76, g77, g78, gc1, g8, hj15, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, buildT, buildN, cPHASE, cINDEX, cX, cCODE, cCHK, cLEFT, cREST, cTOTAL, bLeftN, bRestN, bExempt, cREASON, rINCOMP, cMODE, mREJECT,
      show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (2079 : Int) < L by omega,
      show (2076 : Int) < L by omega, show (2077 : Int) < L by omega, show (2078 : Int) < L by omega,
      show (14 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega,
      show (0 : Int) ≤ X + 7 by omega, show X + 7 < L by omega, show (0 : Int) ≤ X + 8 by omega, show X + 8 < L by omega,
      show (0 : Int) ≤ tbb + 1 by omega, show tbb + 1 < L by omega])


end K5
