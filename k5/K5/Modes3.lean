/-
  O95, K5-2 route A, batch 3: the BUILD family on the checked runner (the porter, as Modes1).
-/
import K5.Modes2

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate.Step

set_option maxHeartbeats 4000000 in
theorem build_zero_end_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (j X tbb : Int) (hph : f cPHASE = 0) (hj : f cINDEX = j) (hX : f cX = X) (htbb : f (X + 7) = tbb)
    (hX0 : 0 ≤ X) (hXL : X + 8 < L) (hj16 : ¬ j < 16)
    (rr1 : inRange (X + 7) = true) :
    SrcInRange (closeAt p buildT, σ) := by
  simp only [cPHASE, cINDEX, cX] at hph hj hX
  have g12 := hw.get (i := 12) (by decide) (by omega) hph
  have g13 := hw.get (i := 13) (by decide) (by omega) hj
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g7 := hw.get (i := X + 7) (by omega) (by omega) htbb
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, buildT, buildN, cPHASE, cINDEX, cX, cCODE, cCHK, cLEFT, cREST, cTOTAL, bZeroN, g12, g13, g79, g7, hj16, show (12 : Int) < L by omega, show (13 : Int) < L by omega,
    show (2079 : Int) < L by omega, show (0 : Int) ≤ X + 7 by omega, show X + 7 < L by omega])

set_option maxHeartbeats 4000000 in
theorem build_count_cell_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (j X tbb sb nn l c : Int) (hph : f cPHASE = 1) (hj : f cINDEX = j) (hX : f cX = X) (htbb : f (X + 7) = tbb)
    (hsb : f (X + 5) = sb) (hnn : f (X + 6) = nn) (hX0 : 0 ≤ X) (hXL : X + 8 < L) (hjn : j < nn)
    (hs0 : 0 ≤ sb + j) (hsL : sb + j < L) (hl : f (sb + j) = l) (ht0 : 0 ≤ tbb) (htL : tbb + 352 ≤ L)
    (hl0 : 0 ≤ l) (hl15 : l ≤ 15) (hc : f (tbb + l) = c)
    (rr1 : inRange (X + 7) = true)
    (rr2 : inRange (X + 5) = true) (rr3 : inRange (X + 7) = true)
    (rr4 : inRange (X + 6) = true) (rr5 : inRange (X + 7) = true) (rr6 : inRange (X + 5) = true)
    (rr7 : inRange (sb + j) = true) (rr8 : inRange (X + 7) = true) (rr9 : inRange (X + 5) = true) (rr10 : inRange (X + 6) = true)
    (rr11 : inRange (j + 1) = true) (rr12 : inRange (X + 7) = true) (rr13 : inRange (X + 5) = true) (rr14 : inRange (X + 6) = true) (rr15 : inRange (sb + j) = true) (rr16 : inRange (tbb + l) = true)
    (rr17 : inRange (c + 1) = true) (rr18 : inRange (X + 7) = true) (rr19 : inRange (X + 5) = true) (rr20 : inRange (X + 6) = true) (rr21 : inRange (sb + j) = true) (rr22 : inRange (j + 1) = true) (rr23 : inRange (tbb + l) = true) :
    SrcInRange (closeAt p buildT, σ) := by
  simp only [cPHASE, cINDEX, cX] at hph hj hX
  have g12 := hw.get (i := 12) (by decide) (by omega) hph
  have g13 := hw.get (i := 13) (by decide) (by omega) hj
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g7 := hw.get (i := X + 7) (by omega) (by omega) htbb
  have g5 := hw.get (i := X + 5) (by omega) (by omega) hsb
  have g6 := hw.get (i := X + 6) (by omega) (by omega) hnn
  have gl := hw.get hs0 hsL hl
  have gc := hw.get (i := tbb + l) (by omega) (by omega) hc
  by_cases h0 : l = 0
  · subst h0
    repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr17, rr18, rr19, rr20, rr21, rr22, rr23, rr11, rr12, rr13, rr14, rr15, rr16, rr7, rr8, rr9, rr10, rr4, rr5, rr6, rr2, rr3, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, buildT, buildN, cPHASE, cINDEX, cX, cCODE, cCHK, cLEFT, cREST, cTOTAL, bCountN, g12, g13, g79, g7, g5, g6, gl, hjn, hs0, hsL, show (12 : Int) < L by omega,
      show (13 : Int) < L by omega, show (2079 : Int) < L by omega, show (0 : Int) ≤ X + 7 by omega,
      show X + 7 < L by omega, show (0 : Int) ≤ X + 5 by omega, show X + 5 < L by omega,
      show (0 : Int) ≤ X + 6 by omega, show X + 6 < L by omega])
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr17, rr18, rr19, rr20, rr21, rr22, rr23, rr11, rr12, rr13, rr14, rr15, rr16, rr7, rr8, rr9, rr10, rr4, rr5, rr6, rr2, rr3, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, buildT, buildN, cPHASE, cINDEX, cX, cCODE, cCHK, cLEFT, cREST, cTOTAL, bCountN, h0, g12, g13, g79, g7, g5, g6, gl, gc, hjn, hs0, hsL, show (12 : Int) < L by omega,
      show (13 : Int) < L by omega, show (2079 : Int) < L by omega, show (0 : Int) ≤ X + 7 by omega,
      show X + 7 < L by omega, show (0 : Int) ≤ X + 5 by omega, show X + 5 < L by omega,
      show (0 : Int) ≤ X + 6 by omega, show X + 6 < L by omega, show (0 : Int) ≤ tbb + l by omega,
      show tbb + l < L by omega])

set_option maxHeartbeats 4000000 in
theorem build_count_end_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (j X tbb sb nn : Int) (hph : f cPHASE = 1) (hj : f cINDEX = j) (hX : f cX = X) (htbb : f (X + 7) = tbb)
    (hsb : f (X + 5) = sb) (hnn : f (X + 6) = nn) (hX0 : 0 ≤ X) (hXL : X + 8 < L) (hjn : ¬ j < nn)
    (ht0 : 0 ≤ tbb) (htL : tbb + 352 ≤ L)
    (rr1 : inRange (X + 7) = true)
    (rr2 : inRange (X + 5) = true) (rr3 : inRange (X + 7) = true)
    (rr4 : inRange (X + 6) = true) (rr5 : inRange (X + 7) = true) (rr6 : inRange (X + 5) = true)
    (rr7 : inRange (tbb + 16) = true) (rr8 : inRange (X + 7) = true) (rr9 : inRange (X + 5) = true) (rr10 : inRange (X + 6) = true)
    (rr11 : inRange (tbb + 32) = true) (rr12 : inRange (X + 7) = true) (rr13 : inRange (X + 5) = true) (rr14 : inRange (X + 6) = true) (rr15 : inRange (tbb + 16) = true) :
    SrcInRange (closeAt p buildT, σ) := by
  simp only [cPHASE, cINDEX, cX] at hph hj hX
  have g12 := hw.get (i := 12) (by decide) (by omega) hph
  have g13 := hw.get (i := 13) (by decide) (by omega) hj
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g7 := hw.get (i := X + 7) (by omega) (by omega) htbb
  have g5 := hw.get (i := X + 5) (by omega) (by omega) hsb
  have g6 := hw.get (i := X + 6) (by omega) (by omega) hnn
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr11, rr12, rr13, rr14, rr15, rr7, rr8, rr9, rr10, rr4, rr5, rr6, rr2, rr3, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, buildT, buildN, cPHASE, cINDEX, cX, cCODE, cCHK, cLEFT, cREST, cTOTAL, bCountN, g12, g13, g79, g7, g5, g6, hjn, show (12 : Int) < L by omega,
    show (13 : Int) < L by omega, show (2079 : Int) < L by omega, show (2075 : Int) < L by omega,
    show (0 : Int) ≤ X + 7 by omega, show X + 7 < L by omega, show (0 : Int) ≤ X + 5 by omega,
    show X + 5 < L by omega, show (0 : Int) ≤ X + 6 by omega, show X + 6 < L by omega,
    show (0 : Int) ≤ tbb + 16 by omega, show tbb + 16 < L by omega, show (0 : Int) ≤ tbb + 32 by omega,
    show tbb + 32 < L by omega])

set_option maxHeartbeats 4000000 in
theorem build_next_cell_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (j X tbb code cp op : Int) (hph : f cPHASE = 2) (hj : f cINDEX = j) (hX : f cX = X) (htbb : f (X + 7) = tbb)
    (hX0 : 0 ≤ X) (hXL : X + 8 < L) (hj1 : 1 ≤ j) (hj15 : j ≤ 15) (ht0 : 0 ≤ tbb) (htL : tbb + 352 ≤ L)
    (hcode : f cCODE = code) (hcp : f (tbb + (j - 1)) = cp) (hop : f (tbb + 32 + (j - 1)) = op)
    (rr1 : inRange (X + 7) = true)
    (rr2 : inRange (j - 1) = true) (rr3 : inRange (tbb + (j - 1)) = true) (rr4 : inRange (X + 7) = true)
    (rr5 : inRange (tbb + 32) = true) (rr6 : inRange (tbb + 32 + (j - 1)) = true) (rr7 : inRange (X + 7) = true) (rr8 : inRange (j - 1) = true) (rr9 : inRange (tbb + (j - 1)) = true)
    (rr10 : inRange (code + cp) = true) (rr11 : inRange (2 * (code + cp)) = true) (rr12 : inRange (X + 7) = true) (rr13 : inRange (j - 1) = true) (rr14 : inRange (tbb + (j - 1)) = true) (rr15 : inRange (tbb + 32) = true) (rr16 : inRange (tbb + 32 + (j - 1)) = true)
    (rr17 : inRange (tbb + 16) = true) (rr18 : inRange (tbb + 16 + j) = true) (rr19 : inRange (X + 7) = true) (rr20 : inRange (j - 1) = true) (rr21 : inRange (tbb + (j - 1)) = true) (rr22 : inRange (tbb + 32) = true) (rr23 : inRange (tbb + 32 + (j - 1)) = true) (rr24 : inRange (code + cp) = true) (rr25 : inRange (2 * (code + cp)) = true)
    (rr26 : inRange (tbb + 32 + j) = true) (rr27 : inRange (op + cp) = true) (rr28 : inRange (X + 7) = true) (rr29 : inRange (j - 1) = true) (rr30 : inRange (tbb + (j - 1)) = true) (rr31 : inRange (tbb + 32) = true) (rr32 : inRange (tbb + 32 + (j - 1)) = true) (rr33 : inRange (code + cp) = true) (rr34 : inRange (2 * (code + cp)) = true) (rr35 : inRange (tbb + 16) = true) (rr36 : inRange (tbb + 16 + j) = true)
    (rr37 : inRange (tbb + 48) = true) (rr38 : inRange (tbb + 48 + j) = true) (rr39 : inRange (X + 7) = true) (rr40 : inRange (j - 1) = true) (rr41 : inRange (tbb + (j - 1)) = true) (rr42 : inRange (tbb + 32) = true) (rr43 : inRange (tbb + 32 + (j - 1)) = true) (rr44 : inRange (code + cp) = true) (rr45 : inRange (2 * (code + cp)) = true) (rr46 : inRange (tbb + 16) = true) (rr47 : inRange (tbb + 16 + j) = true) (rr48 : inRange (tbb + 32 + j) = true) (rr49 : inRange (op + cp) = true)
    (rr50 : inRange (j + 1) = true) (rr51 : inRange (X + 7) = true) (rr52 : inRange (j - 1) = true) (rr53 : inRange (tbb + (j - 1)) = true) (rr54 : inRange (tbb + 32) = true) (rr55 : inRange (tbb + 32 + (j - 1)) = true) (rr56 : inRange (code + cp) = true) (rr57 : inRange (2 * (code + cp)) = true) (rr58 : inRange (tbb + 16) = true) (rr59 : inRange (tbb + 16 + j) = true) (rr60 : inRange (tbb + 32 + j) = true) (rr61 : inRange (op + cp) = true) (rr62 : inRange (tbb + 48) = true) (rr63 : inRange (tbb + 48 + j) = true) :
    SrcInRange (closeAt p buildT, σ) := by
  simp only [cPHASE, cINDEX, cX, cCODE] at hph hj hX hcode
  have g12 := hw.get (i := 12) (by decide) (by omega) hph
  have g13 := hw.get (i := 13) (by decide) (by omega) hj
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g7 := hw.get (i := X + 7) (by omega) (by omega) htbb
  have g75 := hw.get (i := 2075) (by decide) (by omega) hcode
  have gcp := hw.get (i := tbb + (j - 1)) (by omega) (by omega) hcp
  have gop := hw.get (i := tbb + 32 + (j - 1)) (by omega) (by omega) hop
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr50, rr51, rr52, rr53, rr54, rr55, rr56, rr57, rr58, rr59, rr60, rr61, rr62, rr63, rr37, rr38, rr39, rr40, rr41, rr42, rr43, rr44, rr45, rr46, rr47, rr48, rr49, rr26, rr27, rr28, rr29, rr30, rr31, rr32, rr33, rr34, rr35, rr36, rr17, rr18, rr19, rr20, rr21, rr22, rr23, rr24, rr25, rr10, rr11, rr12, rr13, rr14, rr15, rr16, rr5, rr6, rr7, rr8, rr9, rr2, rr3, rr4, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, buildT, buildN, cPHASE, cINDEX, cX, cCODE, cCHK, cLEFT, cREST, cTOTAL, bNextN, g12, g13, g79, g7, g75, gcp, gop, hj15, show (12 : Int) < L by omega,
    show (13 : Int) < L by omega, show (2079 : Int) < L by omega, show (2075 : Int) < L by omega,
    show (0 : Int) ≤ X + 7 by omega, show X + 7 < L by omega,
    show (0 : Int) ≤ tbb + (j - 1) by omega, show tbb + (j - 1) < L by omega,
    show (0 : Int) ≤ tbb + 32 + (j - 1) by omega, show tbb + 32 + (j - 1) < L by omega,
    show (0 : Int) ≤ tbb + 16 + j by omega, show tbb + 16 + j < L by omega,
    show (0 : Int) ≤ tbb + 32 + j by omega, show tbb + 32 + j < L by omega,
    show (0 : Int) ≤ tbb + 48 + j by omega, show tbb + 48 + j < L by omega])

set_option maxHeartbeats 4000000 in
theorem build_next_end_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (j X tbb chk : Int) (hph : f cPHASE = 2) (hj : f cINDEX = j) (hX : f cX = X) (htbb : f (X + 7) = tbb)
    (hX0 : 0 ≤ X) (hXL : X + 8 < L) (hj15 : ¬ j ≤ 15) (hchk : f cCHK = chk)
    (rr1 : inRange (X + 7) = true) :
    SrcInRange (closeAt p buildT, σ) := by
  simp only [cPHASE, cINDEX, cX, cCHK] at hph hj hX hchk
  have g12 := hw.get (i := 12) (by decide) (by omega) hph
  have g13 := hw.get (i := 13) (by decide) (by omega) hj
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g7 := hw.get (i := X + 7) (by omega) (by omega) htbb
  have g72 := hw.get (i := 2072) (by decide) (by omega) hchk
  by_cases h1 : chk = 1
  · subst h1
    repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, buildT, buildN, cPHASE, cINDEX, cX, cCODE, cCHK, cLEFT, cREST, cTOTAL, bNextN, g12, g13, g79, g7, g72, hj15, show (12 : Int) < L by omega,
      show (13 : Int) < L by omega, show (2079 : Int) < L by omega, show (2072 : Int) < L by omega,
      show (2076 : Int) < L by omega, show (2077 : Int) < L by omega, show (2078 : Int) < L by omega,
      show (0 : Int) ≤ X + 7 by omega, show X + 7 < L by omega])
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, buildT, buildN, cPHASE, cINDEX, cX, cCODE, cCHK, cLEFT, cREST, cTOTAL, bNextN, h1, g12, g13, g79, g7, g72, hj15, show (12 : Int) < L by omega,
      show (13 : Int) < L by omega, show (2079 : Int) < L by omega, show (2072 : Int) < L by omega,
      show (0 : Int) ≤ X + 7 by omega, show X + 7 < L by omega])

set_option maxHeartbeats 4000000 in
theorem build_left_cell_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (j X tbb left rest tot c : Int) (hph : f cPHASE = 3) (hj : f cINDEX = j) (hX : f cX = X) (htbb : f (X + 7) = tbb)
    (hX0 : 0 ≤ X) (hXL : X + 8 < L) (hj1 : 1 ≤ j) (hj15 : j ≤ 15) (ht0 : 0 ≤ tbb) (htL : tbb + 352 ≤ L)
    (hleft : f cLEFT = left) (hrest : f cREST = rest) (htot : f cTOTAL = tot) (hc : f (tbb + j) = c)
    (rr1 : inRange (X + 7) = true)
    (rr2 : inRange (tbb + j) = true) (rr3 : inRange (X + 7) = true)
    (rr4 : inRange (2 * left) = true) (rr5 : inRange (2 * left - c) = true) (rr6 : inRange (X + 7) = true) (rr7 : inRange (tbb + j) = true)
    (rr8 : inRange (rest + c) = true) (rr9 : inRange (X + 7) = true) (rr10 : inRange (tbb + j) = true) (rr11 : inRange (2 * left) = true) (rr12 : inRange (2 * left - c) = true) (rr13 : inRange (tot + c) = true)
    (rr14 : inRange (j + 1) = true) (rr15 : inRange (X + 7) = true) (rr16 : inRange (tbb + j) = true) (rr17 : inRange (2 * left) = true) (rr18 : inRange (2 * left - c) = true) (rr19 : inRange (rest + c) = true) (rr20 : inRange (tot + c) = true) :
    SrcInRange (closeAt p buildT, σ) := by
  simp only [cPHASE, cINDEX, cX, cLEFT, cREST, cTOTAL] at hph hj hX hleft hrest htot
  have g12 := hw.get (i := 12) (by decide) (by omega) hph
  have g13 := hw.get (i := 13) (by decide) (by omega) hj
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g7 := hw.get (i := X + 7) (by omega) (by omega) htbb
  have g76 := hw.get (i := 2076) (by decide) (by omega) hleft
  have g77 := hw.get (i := 2077) (by decide) (by omega) hrest
  have g78 := hw.get (i := 2078) (by decide) (by omega) htot
  have gc := hw.get (i := tbb + j) (by omega) (by omega) hc
  by_cases hneg : 2 * left - c < 0
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr14, rr15, rr16, rr17, rr18, rr19, rr20, rr8, rr9, rr10, rr11, rr12, rr13, rr4, rr5, rr6, rr7, rr2, rr3, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, buildT, buildN, cPHASE, cINDEX, cX, cCODE, cCHK, cLEFT, cREST, cTOTAL, bLeftN, bRestN, hneg, g12, g13, g79, g7, g76, g77, g78, gc, hj15, cREASON, rOVERSUB, cMODE, mREJECT,
      show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (2079 : Int) < L by omega,
      show (2076 : Int) < L by omega, show (2077 : Int) < L by omega, show (2078 : Int) < L by omega,
      show (14 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega,
      show (0 : Int) ≤ X + 7 by omega, show X + 7 < L by omega, show (0 : Int) ≤ tbb + j by omega, show tbb + j < L by omega])
  · by_cases h2 : 2 ≤ j <;>
    repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr14, rr15, rr16, rr17, rr18, rr19, rr20, rr8, rr9, rr10, rr11, rr12, rr13, rr4, rr5, rr6, rr7, rr2, rr3, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, buildT, buildN, cPHASE, cINDEX, cX, cCODE, cCHK, cLEFT, cREST, cTOTAL, bLeftN, bRestN, hneg, h2, g12, g13, g79, g7, g76, g77, g78, gc, hj15,
      show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (2079 : Int) < L by omega,
      show (2076 : Int) < L by omega, show (2077 : Int) < L by omega, show (2078 : Int) < L by omega,
      show (0 : Int) ≤ X + 7 by omega, show X + 7 < L by omega, show (0 : Int) ≤ tbb + j by omega, show tbb + j < L by omega])

set_option maxHeartbeats 4000000 in
theorem build_syms_cell_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (j X tbb sb nn l sl : Int) (hph : f cPHASE = 4) (hj : f cINDEX = j) (hX : f cX = X) (htbb : f (X + 7) = tbb)
    (hsb : f (X + 5) = sb) (hnn : f (X + 6) = nn) (hX0 : 0 ≤ X) (hXL : X + 8 < L) (hjn : j < nn)
    (hs0 : 0 ≤ sb + j) (hsL : sb + j < L) (hl : f (sb + j) = l) (ht0 : 0 ≤ tbb) (htL : tbb + 352 ≤ L)
    (hl0 : 0 ≤ l) (hl15 : l ≤ 15) (hsl : f (tbb + 48 + l) = sl) (hsl0 : l ≠ 0 → 0 ≤ sl) (hsl288 : l ≠ 0 → sl < 288)
    (rr1 : inRange (X + 7) = true)
    (rr2 : inRange (X + 5) = true) (rr3 : inRange (X + 7) = true)
    (rr4 : inRange (X + 6) = true) (rr5 : inRange (X + 7) = true) (rr6 : inRange (X + 5) = true)
    (rr7 : inRange (sb + j) = true) (rr8 : inRange (X + 7) = true) (rr9 : inRange (X + 5) = true) (rr10 : inRange (X + 6) = true)
    (rr11 : inRange (j + 1) = true) (rr12 : inRange (X + 7) = true) (rr13 : inRange (X + 5) = true) (rr14 : inRange (X + 6) = true) (rr15 : inRange (sb + j) = true) (rr16 : inRange (tbb + 48) = true) (rr17 : inRange (tbb + 48 + l) = true)
    (rr18 : inRange (tbb + 64) = true) (rr19 : inRange (tbb + 64 + sl) = true) (rr20 : inRange (X + 7) = true) (rr21 : inRange (X + 5) = true) (rr22 : inRange (X + 6) = true) (rr23 : inRange (sb + j) = true) (rr24 : inRange (j + 1) = true) (rr25 : inRange (tbb + 48) = true) (rr26 : inRange (tbb + 48 + l) = true)
    (rr27 : inRange (sl + 1) = true) (rr28 : inRange (X + 7) = true) (rr29 : inRange (X + 5) = true) (rr30 : inRange (X + 6) = true) (rr31 : inRange (sb + j) = true) (rr32 : inRange (j + 1) = true) (rr33 : inRange (tbb + 48) = true) (rr34 : inRange (tbb + 48 + l) = true) (rr35 : inRange (tbb + 64) = true) (rr36 : inRange (tbb + 64 + sl) = true) :
    SrcInRange (closeAt p buildT, σ) := by
  simp only [cPHASE, cINDEX, cX] at hph hj hX
  have g12 := hw.get (i := 12) (by decide) (by omega) hph
  have g13 := hw.get (i := 13) (by decide) (by omega) hj
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g7 := hw.get (i := X + 7) (by omega) (by omega) htbb
  have g5 := hw.get (i := X + 5) (by omega) (by omega) hsb
  have g6 := hw.get (i := X + 6) (by omega) (by omega) hnn
  have gl := hw.get hs0 hsL hl
  have gsl := hw.get (i := tbb + 48 + l) (by omega) (by omega) hsl
  by_cases h0 : l = 0
  · subst h0
    repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr27, rr28, rr29, rr30, rr31, rr32, rr33, rr34, rr35, rr36, rr18, rr19, rr20, rr21, rr22, rr23, rr24, rr25, rr26, rr11, rr12, rr13, rr14, rr15, rr16, rr17, rr7, rr8, rr9, rr10, rr4, rr5, rr6, rr2, rr3, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, buildT, buildN, cPHASE, cINDEX, cX, cCODE, cCHK, cLEFT, cREST, cTOTAL, bSymsN, bRestN, g12, g13, g79, g7, g5, g6, gl, hjn, hs0, hsL, show (12 : Int) < L by omega,
      show (13 : Int) < L by omega, show (2079 : Int) < L by omega, show (0 : Int) ≤ X + 7 by omega,
      show X + 7 < L by omega, show (0 : Int) ≤ X + 5 by omega, show X + 5 < L by omega,
      show (0 : Int) ≤ X + 6 by omega, show X + 6 < L by omega])
  · have hsl0' := hsl0 h0
    have hsl288' := hsl288 h0
    repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr27, rr28, rr29, rr30, rr31, rr32, rr33, rr34, rr35, rr36, rr18, rr19, rr20, rr21, rr22, rr23, rr24, rr25, rr26, rr11, rr12, rr13, rr14, rr15, rr16, rr17, rr7, rr8, rr9, rr10, rr4, rr5, rr6, rr2, rr3, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, buildT, buildN, cPHASE, cINDEX, cX, cCODE, cCHK, cLEFT, cREST, cTOTAL, bSymsN, bRestN, h0, g12, g13, g79, g7, g5, g6, gl, gsl, hjn, hs0, hsL, show (12 : Int) < L by omega,
      show (13 : Int) < L by omega, show (2079 : Int) < L by omega, show (0 : Int) ≤ X + 7 by omega,
      show X + 7 < L by omega, show (0 : Int) ≤ X + 5 by omega, show X + 5 < L by omega,
      show (0 : Int) ≤ X + 6 by omega, show X + 6 < L by omega, show (0 : Int) ≤ tbb + 48 + l by omega,
      show tbb + 48 + l < L by omega, show (0 : Int) ≤ tbb + 64 + sl by omega, show tbb + 64 + sl < L by omega])

set_option maxHeartbeats 4000000 in
theorem build_syms_end_cl_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (j X tbb sb nn : Int) (hph : f cPHASE = 4) (hj : f cINDEX = j) (hX : f cX = X) (htbb : f (X + 7) = tbb)
    (hsb : f (X + 5) = sb) (hnn : f (X + 6) = nn) (hX0 : 0 ≤ X) (hXL : X + 8 < L) (hjn : ¬ j < nn)
    (htg : f cTGT = 0)
    (rr1 : inRange (X + 7) = true)
    (rr2 : inRange (X + 5) = true) (rr3 : inRange (X + 7) = true)
    (rr4 : inRange (X + 6) = true) (rr5 : inRange (X + 7) = true) (rr6 : inRange (X + 5) = true) :
    SrcInRange (closeAt p buildT, σ) := by
  simp only [cPHASE, cINDEX, cX, cTGT] at hph hj hX htg
  have g12 := hw.get (i := 12) (by decide) (by omega) hph
  have g13 := hw.get (i := 13) (by decide) (by omega) hj
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g7 := hw.get (i := X + 7) (by omega) (by omega) htbb
  have g5 := hw.get (i := X + 5) (by omega) (by omega) hsb
  have g6 := hw.get (i := X + 6) (by omega) (by omega) hnn
  have g74 := hw.get (i := 2074) (by decide) (by omega) htg
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr4, rr5, rr6, rr2, rr3, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, buildT, buildN, cPHASE, cINDEX, cX, cCODE, cCHK, cLEFT, cREST, cTOTAL, bSymsN, bRestN, g12, g13, g79, g7, g5, g6, g74, hjn, cTGT, cMODE, mLENS,
    show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (2079 : Int) < L by omega,
    show (2074 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega,
    show (0 : Int) ≤ X + 7 by omega, show X + 7 < L by omega, show (0 : Int) ≤ X + 5 by omega,
    show X + 5 < L by omega, show (0 : Int) ≤ X + 6 by omega, show X + 6 < L by omega])

set_option maxHeartbeats 4000000 in
theorem build_syms_end_l_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (j X tbb sb nn hl hd n om dy : Int) (hph : f cPHASE = 4) (hj : f cINDEX = j) (hX : f cX = X) (htbb : f (X + 7) = tbb)
    (hsb : f (X + 5) = sb) (hnn : f (X + 6) = nn) (hX0 : 0 ≤ X) (hXL : X + 8 < L) (hjn : ¬ j < nn)
    (htg : f cTGT = 1) (hhl : f cHLIT = hl) (hhd : f cHDIST = hd) (hn : f cN = n) (hom : f cOUTMAX = om)
    (hdy : f cDYN = dy)
    (rr1 : inRange (X + 7) = true)
    (rr2 : inRange (X + 5) = true) (rr3 : inRange (X + 7) = true)
    (rr4 : inRange (X + 6) = true) (rr5 : inRange (X + 7) = true) (rr6 : inRange (X + 5) = true)
    (rr7 : inRange (2080 + n) = true) (rr8 : inRange (2080 + n + om) = true) (rr9 : inRange (2080 + n + om + hl) = true) (rr10 : inRange (X + 7) = true) (rr11 : inRange (X + 5) = true) (rr12 : inRange (X + 6) = true)
    (rr13 : inRange (2080 + n + om + 1041) = true) (rr14 : inRange (X + 7) = true) (rr15 : inRange (X + 5) = true) (rr16 : inRange (X + 6) = true) (rr17 : inRange (2080 + n) = true) (rr18 : inRange (2080 + n + om) = true) (rr19 : inRange (2080 + n + om + hl) = true)
    (rr20 : inRange (X + 8) = true) (rr21 : inRange (X + 7) = true) (rr22 : inRange (X + 5) = true) (rr23 : inRange (X + 6) = true) (rr24 : inRange (2080 + n) = true) (rr25 : inRange (2080 + n + om) = true) (rr26 : inRange (2080 + n + om + hl) = true) (rr27 : inRange (2080 + n + om + 1041) = true) :
    SrcInRange (closeAt p buildT, σ) := by
  simp only [cPHASE, cINDEX, cX, cTGT, cHLIT, cHDIST, cN, cOUTMAX, cDYN] at hph hj hX htg hhl hhd hn hom hdy
  have g12 := hw.get (i := 12) (by decide) (by omega) hph
  have g13 := hw.get (i := 13) (by decide) (by omega) hj
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g7 := hw.get (i := X + 7) (by omega) (by omega) htbb
  have g5 := hw.get (i := X + 5) (by omega) (by omega) hsb
  have g6 := hw.get (i := X + 6) (by omega) (by omega) hnn
  have g74 := hw.get (i := 2074) (by decide) (by omega) htg
  have g07 := hw.get (i := 7) (by decide) (by omega) hhl
  have g08 := hw.get (i := 8) (by decide) (by omega) hhd
  have g15 := hw.get (i := 15) (by decide) (by omega) hn
  have g16 := hw.get (i := 16) (by decide) (by omega) hom
  have g73 := hw.get (i := 2073) (by decide) (by omega) hdy
  by_cases hd1 : dy = 1
  · subst hd1
    repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr20, rr21, rr22, rr23, rr24, rr25, rr26, rr27, rr13, rr14, rr15, rr16, rr17, rr18, rr19, rr7, rr8, rr9, rr10, rr11, rr12, rr4, rr5, rr6, rr2, rr3, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, buildT, buildN, cPHASE, cINDEX, cX, cCODE, cCHK, cLEFT, cREST, cTOTAL, bSymsN, bRestN, g12, g13, g79, g7, g5, g6, g74, g07, g08, g15, g16, g73, hjn, cTGT, cHLIT, cHDIST, cN,
      cOUTMAX, cDYN, IN, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (2079 : Int) < L by omega,
      show (2074 : Int) < L by omega, show (2073 : Int) < L by omega, show (7 : Int) < L by omega,
      show (8 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega,
      show (0 : Int) ≤ X + 7 by omega, show X + 7 < L by omega, show (0 : Int) ≤ X + 5 by omega,
      show X + 5 < L by omega, show (0 : Int) ≤ X + 6 by omega, show X + 6 < L by omega,
      show (0 : Int) ≤ X + 8 by omega, show X + 8 < L by omega])
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr20, rr21, rr22, rr23, rr24, rr25, rr26, rr27, rr13, rr14, rr15, rr16, rr17, rr18, rr19, rr7, rr8, rr9, rr10, rr11, rr12, rr4, rr5, rr6, rr2, rr3, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, buildT, buildN, cPHASE, cINDEX, cX, cCODE, cCHK, cLEFT, cREST, cTOTAL, bSymsN, bRestN, hd1, g12, g13, g79, g7, g5, g6, g74, g07, g08, g15, g16, g73, hjn, cTGT, cHLIT, cHDIST,
      cN, cOUTMAX, cDYN, IN, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (2079 : Int) < L by omega,
      show (2074 : Int) < L by omega, show (2073 : Int) < L by omega, show (7 : Int) < L by omega,
      show (8 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega,
      show (0 : Int) ≤ X + 7 by omega, show X + 7 < L by omega, show (0 : Int) ≤ X + 5 by omega,
      show X + 5 < L by omega, show (0 : Int) ≤ X + 6 by omega, show X + 6 < L by omega,
      show (0 : Int) ≤ X + 8 by omega, show X + 8 < L by omega])

set_option maxHeartbeats 4000000 in
theorem build_syms_end_d_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (j X tbb sb nn : Int) (hph : f cPHASE = 4) (hj : f cINDEX = j) (hX : f cX = X) (htbb : f (X + 7) = tbb)
    (hsb : f (X + 5) = sb) (hnn : f (X + 6) = nn) (hX0 : 0 ≤ X) (hXL : X + 8 < L) (hjn : ¬ j < nn)
    (htg : f cTGT = 2)
    (rr1 : inRange (X + 7) = true)
    (rr2 : inRange (X + 5) = true) (rr3 : inRange (X + 7) = true)
    (rr4 : inRange (X + 6) = true) (rr5 : inRange (X + 7) = true) (rr6 : inRange (X + 5) = true) :
    SrcInRange (closeAt p buildT, σ) := by
  simp only [cPHASE, cINDEX, cX, cTGT] at hph hj hX htg
  have g12 := hw.get (i := 12) (by decide) (by omega) hph
  have g13 := hw.get (i := 13) (by decide) (by omega) hj
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g7 := hw.get (i := X + 7) (by omega) (by omega) htbb
  have g5 := hw.get (i := X + 5) (by omega) (by omega) hsb
  have g6 := hw.get (i := X + 6) (by omega) (by omega) hnn
  have g74 := hw.get (i := 2074) (by decide) (by omega) htg
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr4, rr5, rr6, rr2, rr3, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, buildT, buildN, cPHASE, cINDEX, cX, cCODE, cCHK, cLEFT, cREST, cTOTAL, bSymsN, bRestN, g12, g13, g79, g7, g5, g6, g74, hjn, cTGT, cMODE, mSYM,
    show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (2079 : Int) < L by omega,
    show (2074 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega,
    show (0 : Int) ≤ X + 7 by omega, show X + 7 < L by omega, show (0 : Int) ≤ X + 5 by omega,
    show X + 5 < L by omega, show (0 : Int) ≤ X + 6 by omega, show X + 6 < L by omega])

end K5
