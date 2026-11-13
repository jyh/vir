/-
  O95, K5-2 route A, batch 2 of the mode traces on the checked runner (the porter, as Modes1).
-/
import K5.Modes1

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate.Step

set_option maxHeartbeats 4000000 in
theorem readbit_trunc_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (bx n : Int) (hby : f cBY = bx) (hn : f cN = n) (hbyn : n ≤ bx) :
    SrcInRange (closeAt p readT, σ) := by
  simp only [cBY, cN] at hby hn
  have h1 := hw.cell 1 (by decide) (by omega)
  have h2 := hw.cell 2 (by decide) (by omega)
  have h15 := hw.cell 15 (by decide) (by omega)
  rw [hby] at h1; rw [hn] at h15
  have hnlt : ¬ (bx < n) := by omega
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, closeAt, readT, readN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, hnlt,
    Tm.subst, Atom.subst, Atom.substL, stepFn₂, stepFn, opStep, Store.load, Store.store, hw.reg, h1, h2, h15,
    Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool,
    cBY, cBI, cN, cMODE, cREASON, rTRUNC, mREJECT,
    show (1 : Int) < L by omega, show (2 : Int) < L by omega, show (15 : Int) < L by omega,
    show (14 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem scopy_end_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (bf : Int) (hk : f cPEND = 0) (hbf : f cBF = bf) :
    SrcInRange (closeAt p scopyT, σ) := by
  simp only [cPEND, cBF] at hk hbf
  have h5 := hw.cell 5 (by decide) (by omega)
  have h4 := hw.cell 4 (by decide) (by omega)
  rw [hk] at h5; rw [hbf] at h4
  by_cases h : bf = 1
  · subst h
    repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, scopyT, scopyN, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, h5, h4, cPEND, cBF, cMODE, mDONE, show (5 : Int) < L by omega,
      show (4 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega])
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, scopyT, scopyN, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, h, h5, h4, cPEND, cBF, cMODE, mHDR, show (5 : Int) < L by omega,
      show (4 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem scopy_byte_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f)
    (bx n m om : Nat) (k x : Int) (hL : 2080 + n + om ≤ L) (hk : f cPEND = k) (hk0 : k ≠ 0) (hby : f cBY = bx)
    (hn : f cN = n) (hbyn : bx < n) (hx : f (IN + bx) = x) (hm : f cM = m) (hmo : m < om)
    (rr1 : inRange (2080 + (bx : Int)) = true)
    (rr2 : inRange (2080 + (n : Int)) = true) (rr3 : inRange (2080 + (n : Int) + (m : Int)) = true) (rr4 : inRange (2080 + (bx : Int)) = true)
    (rr5 : inRange ((bx : Int) + 1) = true) (rr6 : inRange (2080 + (bx : Int)) = true) (rr7 : inRange (2080 + (n : Int)) = true) (rr8 : inRange (2080 + (n : Int) + (m : Int)) = true)
    (rr9 : inRange ((m : Int) + 1) = true) (rr10 : inRange (2080 + (bx : Int)) = true) (rr11 : inRange (2080 + (n : Int)) = true) (rr12 : inRange (2080 + (n : Int) + (m : Int)) = true) (rr13 : inRange ((bx : Int) + 1) = true)
    (rr14 : inRange (k - 1) = true) (rr15 : inRange (2080 + (bx : Int)) = true) (rr16 : inRange (2080 + (n : Int)) = true) (rr17 : inRange (2080 + (n : Int) + (m : Int)) = true) (rr18 : inRange ((bx : Int) + 1) = true) (rr19 : inRange ((m : Int) + 1) = true) :
    SrcInRange (closeAt p scopyT, σ) := by
  simp only [cPEND, cBY, cN, IN, cM] at hk hby hn hx hm
  have h5 := hw.cell 5 (by decide) (by omega)
  have h1 := hw.cell 1 (by decide) (by omega)
  have h15 := hw.cell 15 (by decide) (by omega)
  have hix := hw.cell (2080 + bx) (by omega) (by omega)
  have h3 := hw.cell 3 (by decide) (by omega)
  rw [hk] at h5; rw [hby] at h1; rw [hn] at h15; rw [hx] at hix; rw [hm] at h3
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr14, rr15, rr16, rr17, rr18, rr19, rr9, rr10, rr11, rr12, rr13, rr5, rr6, rr7, rr8, rr2, rr3, rr4, rr1, scopyT, scopyN, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, hk0, h5, h1, h15, hix, h3, cPEND, cBY, cN, IN, cM,
    show (5 : Int) < L by omega, show (1 : Int) < L by omega, show (15 : Int) < L by omega,
    show (3 : Int) < L by omega, show (2080 : Int) + bx < L by omega, show (0 : Int) ≤ 2080 + bx by omega,
    show (2080 : Int) + n + m < L by omega, show (0 : Int) ≤ 2080 + n + m by omega,
    show (0 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem decode_trunc_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (bx bi n om X : Int) (hby : f cBY = bx) (hbi : f cBI = bi) (hn : f cN = n) (hom : f cOUTMAX = om) (hX : f cX = X)
    (hbyn : n ≤ bx) :
    SrcInRange (closeAt p decodeT, σ) := by
  simp only [cBY, cBI, cN, cOUTMAX, cX] at hby hbi hn hom hX
  have g1 := hw.get (i := 1) (by decide) (by omega) hby
  have g2 := hw.get (i := 2) (by decide) (by omega) hbi
  have g15 := hw.get (i := 15) (by decide) (by omega) hn
  have g16 := hw.get (i := 16) (by decide) (by omega) hom
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have hnlt : ¬ (bx < n) := by omega
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, decodeT, decodeN, cBY, cBI, cN, cOUTMAX, cX, IN, BT, cMODE, cREASON, hnlt, g1, g2, g15, g16, g79, rTRUNC, mREJECT, show (1 : Int) < L by omega, show (2 : Int) < L by omega,
    show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2079 : Int) < L by omega,
    show (14 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem sym_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (X : Int) (hX : f cX = X) (hX0 : 0 ≤ X) (hXL : X + 4 < L)
    (rr1 : inRange (X + 1) = true)
    (rr2 : inRange (X + 2) = true) (rr3 : inRange (X + 1) = true)
    (rr4 : inRange (X + 3) = true) (rr5 : inRange (X + 1) = true) (rr6 : inRange (X + 2) = true) :
    SrcInRange (closeAt p symT, σ) := by
  simp only [cX] at hX
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr4, rr5, rr6, rr2, rr3, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, symT, symN, reqDecN, reqDecH, g79, mSYMD, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega,
    show X < L by omega, show X + 1 < L by omega, show X + 2 < L by omega, show X + 3 < L by omega,
    show (0 : Int) ≤ X + 1 by omega, show (0 : Int) ≤ X + 2 by omega, show (0 : Int) ≤ X + 3 by omega, hX0])

set_option maxHeartbeats 4000000 in
theorem symd_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (X s m om n bf lb le : Int) (hX : f cX = X) (hX0 : 0 ≤ X) (hXL : X + 134 < L) (hs : f (X + 4) = s)
    (hm : f cM = m) (hom : f cOUTMAX = om) (hn : f cN = n) (hbf : f cBF = bf)
    (hlit : s < 256 → m ≠ om → 0 ≤ 2080 + n + m ∧ 2080 + n + m < L)
    (hlb : f (X + 16 + (s - 257)) = lb) (hle : f (X + 45 + (s - 257)) = le)
    (rr1 : inRange (X + 4) = true)
    (rr2 : inRange (2080 + n) = true) (rr3 : inRange (2080 + n + m) = true) (rr4 : inRange (X + 4) = true) (rr5 : inRange (X + 16) = true) (rr6 : inRange (s - 257) = true) (rr7 : inRange (X + 16 + (s - 257)) = true)
    (rr8 : inRange (m + 1) = true) (rr9 : inRange (X + 4) = true) (rr10 : inRange (2080 + n) = true) (rr11 : inRange (2080 + n + m) = true) (rr12 : inRange (X + 16) = true) (rr13 : inRange (s - 257) = true) (rr14 : inRange (X + 16 + (s - 257)) = true) (rr15 : inRange (X + 45) = true) (rr16 : inRange (X + 45 + (s - 257)) = true) :
    SrcInRange (closeAt p symdT, σ) := by
  simp only [cX, cM, cOUTMAX, cN, cBF] at hX hm hom hn hbf
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have gs := hw.get (i := X + 4) (by omega) (by omega) hs
  have g3 := hw.get (i := 3) (by decide) (by omega) hm
  have g16 := hw.get (i := 16) (by decide) (by omega) hom
  have g15 := hw.get (i := 15) (by decide) (by omega) hn
  have g4 := hw.get (i := 4) (by decide) (by omega) hbf
  by_cases h1 : s < 256
  · by_cases h2 : m = om
    · subst h2
      repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr8, rr9, rr10, rr11, rr12, rr13, rr14, rr15, rr16, rr2, rr3, rr4, rr5, rr6, rr7, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, symdT, symdN, symdH, rejN, h1, g79, gs, g3, g16, g15, rOVER, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega,
        show X + 4 < L by omega, show (0 : Int) ≤ X + 4 by omega])
    · obtain ⟨o0, oL⟩ := hlit h1 h2
      repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr8, rr9, rr10, rr11, rr12, rr13, rr14, rr15, rr16, rr2, rr3, rr4, rr5, rr6, rr7, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, symdT, symdN, symdH, h1, h2, g79, gs, g3, g16, g15, mSYM, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega, o0, oL,
        show X + 4 < L by omega, show (0 : Int) ≤ X + 4 by omega])
  by_cases h3 : s = 256
  · subst h3
    by_cases h4 : bf = 1
    · subst h4
      repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr8, rr9, rr10, rr11, rr12, rr13, rr14, rr15, rr16, rr2, rr3, rr4, rr5, rr6, rr7, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, symdT, symdN, symdH, g79, gs, g3, g16, g15, g4, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega, show X + 4 < L by omega,
        show (0 : Int) ≤ X + 4 by omega])
    · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr8, rr9, rr10, rr11, rr12, rr13, rr14, rr15, rr16, rr2, rr3, rr4, rr5, rr6, rr7, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, symdT, symdN, symdH, h4, g79, gs, g3, g16, g15, g4, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega, show X + 4 < L by omega,
        show (0 : Int) ≤ X + 4 by omega])
  by_cases h5 : s ≤ 285
  · have glb := hw.get (i := X + 16 + (s - 257)) (by omega) (by omega) hlb
    have gle := hw.get (i := X + 45 + (s - 257)) (by omega) (by omega) hle
    by_cases h6 : le = 0
    · subst h6
      repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr8, rr9, rr10, rr11, rr12, rr13, rr14, rr15, rr16, rr2, rr3, rr4, rr5, rr6, rr7, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, symdT, symdN, symdH, reqKN, reqKH, h1, h3, h5, g79, gs, g3, g16, g15, glb, gle, mLENX, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega,
        show X + 4 < L by omega, show (0 : Int) ≤ X + 4 by omega,
        show X + 16 + (s - 257) < L by omega, show (0 : Int) ≤ X + 16 + (s - 257) by omega,
        show X + 45 + (s - 257) < L by omega, show (0 : Int) ≤ X + 45 + (s - 257) by omega])
    · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr8, rr9, rr10, rr11, rr12, rr13, rr14, rr15, rr16, rr2, rr3, rr4, rr5, rr6, rr7, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, symdT, symdN, symdH, reqKN, reqKH, h1, h3, h5, h6, g79, gs, g3, g16, g15, glb, gle, mLENX, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega,
        show X + 4 < L by omega, show (0 : Int) ≤ X + 4 by omega,
        show X + 16 + (s - 257) < L by omega, show (0 : Int) ≤ X + 16 + (s - 257) by omega,
        show X + 45 + (s - 257) < L by omega, show (0 : Int) ≤ X + 45 + (s - 257) by omega])
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr8, rr9, rr10, rr11, rr12, rr13, rr14, rr15, rr16, rr2, rr3, rr4, rr5, rr6, rr7, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, symdT, symdN, symdH, rejN, h1, h3, h5, g79, gs, g3, g16, g15, rBADLIT, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega,
      show X + 4 < L by omega, show (0 : Int) ≤ X + 4 by omega])

set_option maxHeartbeats 4000000 in
theorem lenx_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (X a pd : Int) (hX : f cX = X) (hX0 : 0 ≤ X) (hXL : X + 4 < L) (ha : f cACC = a) (hpd : f cPEND = pd)
    (rr1 : inRange (pd + a) = true)
    (rr2 : inRange (X + 1) = true) (rr3 : inRange (pd + a) = true)
    (rr4 : inRange (X + 2) = true) (rr5 : inRange (pd + a) = true) (rr6 : inRange (X + 1) = true)
    (rr7 : inRange (X + 3) = true) (rr8 : inRange (pd + a) = true) (rr9 : inRange (X + 1) = true) (rr10 : inRange (X + 2) = true) :
    SrcInRange (closeAt p lenxT, σ) := by
  simp only [cX, cACC, cPEND] at hX ha hpd
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g69 := hw.get (i := 2069) (by decide) (by omega) ha
  have g5 := hw.get (i := 5) (by decide) (by omega) hpd
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr7, rr8, rr9, rr10, rr4, rr5, rr6, rr2, rr3, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, lenxT, lenxN, reqDecN, reqDecH, g79, g69, g5, mDSTD, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega,
    show X < L by omega, show X + 1 < L by omega, show X + 2 < L by omega, show X + 3 < L by omega,
    show (0 : Int) ≤ X + 1 by omega, show (0 : Int) ≤ X + 2 by omega, show (0 : Int) ≤ X + 3 by omega, hX0])

set_option maxHeartbeats 4000000 in
theorem dstd_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (X d db de : Int) (hX : f cX = X) (hX0 : 0 ≤ X) (hXL : X + 134 < L) (hd : f (X + 4) = d) (hd0 : 0 ≤ d)
    (hdb : f (X + 74 + d) = db) (hde : f (X + 104 + d) = de)
    (rr1 : inRange (X + 4) = true)
    (rr2 : inRange (X + 74) = true) (rr3 : inRange (X + 74 + d) = true) (rr4 : inRange (X + 4) = true)
    (rr5 : inRange (X + 104) = true) (rr6 : inRange (X + 104 + d) = true) (rr7 : inRange (X + 4) = true) (rr8 : inRange (X + 74) = true) (rr9 : inRange (X + 74 + d) = true) :
    SrcInRange (closeAt p dstdT, σ) := by
  simp only [cX] at hX
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have gd := hw.get (i := X + 4) (by omega) (by omega) hd
  by_cases h30 : 30 ≤ d
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr5, rr6, rr7, rr8, rr9, rr2, rr3, rr4, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, dstdT, dstdN, rejN, h30, g79, gd, rBADDIST, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega, show X + 4 < L by omega,
      show (0 : Int) ≤ X + 4 by omega])
  · have gdb := hw.get (i := X + 74 + d) (by omega) (by omega) hdb
    have gde := hw.get (i := X + 104 + d) (by omega) (by omega) hde
    by_cases h0 : de = 0
    · subst h0
      repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr5, rr6, rr7, rr8, rr9, rr2, rr3, rr4, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, dstdT, dstdN, reqKN, reqKH, cDIST, h30, g79, gd, gdb, gde, mDSTX, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega,
        show X + 4 < L by omega, show (0 : Int) ≤ X + 4 by omega, show X + 74 + d < L by omega,
        show (0 : Int) ≤ X + 74 + d by omega, show X + 104 + d < L by omega, show (0 : Int) ≤ X + 104 + d by omega])
    · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr5, rr6, rr7, rr8, rr9, rr2, rr3, rr4, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, dstdT, dstdN, reqKN, reqKH, cDIST, h30, h0, g79, gd, gdb, gde, mDSTX, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega,
        show X + 4 < L by omega, show (0 : Int) ≤ X + 4 by omega, show X + 74 + d < L by omega,
        show (0 : Int) ≤ X + 74 + d by omega, show X + 104 + d < L by omega, show (0 : Int) ≤ X + 104 + d by omega])

set_option maxHeartbeats 4000000 in
theorem dstx_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (a ds m pd om : Int) (ha : f cACC = a) (hds : f cDIST = ds) (hm : f cM = m) (hpd : f cPEND = pd)
    (hom : f cOUTMAX = om)
    (rr1 : inRange (ds + a) = true)
    (rr2 : inRange (m + pd) = true) (rr3 : inRange (ds + a) = true) :
    SrcInRange (closeAt p dstxT, σ) := by
  simp only [cACC, cDIST, cM, cPEND, cOUTMAX] at ha hds hm hpd hom
  have g69 := hw.get (i := 2069) (by decide) (by omega) ha
  have g6 := hw.get (i := 6) (by decide) (by omega) hds
  have g3 := hw.get (i := 3) (by decide) (by omega) hm
  have g5 := hw.get (i := 5) (by decide) (by omega) hpd
  have g16 := hw.get (i := 16) (by decide) (by omega) hom
  by_cases h1 : m < ds + a
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr2, rr3, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, dstxT, dstxN, rejN, cDIST, h1, g69, g6, g3, g5, g16, rFAR, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega])
  by_cases h2 : om < m + pd
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr2, rr3, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, dstxT, dstxN, rejN, cDIST, h1, h2, g69, g6, g3, g5, g16, rOVER, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega])
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr2, rr3, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, dstxT, dstxN, cDIST, h1, h2, g69, g6, g3, g5, g16, mCOPY, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem copy_end_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (hpd : f cPEND = 0) :
    SrcInRange (closeAt p copyT, σ) := by
  simp only [cPEND] at hpd
  have g5 := hw.get (i := 5) (by decide) (by omega) hpd
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, copyT, copyN, g5, mSYM, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem copy_byte_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (pd n m ds y : Int) (hpd : f cPEND = pd) (hpd0 : pd ≠ 0) (hn : f cN = n) (hm : f cM = m) (hds : f cDIST = ds)
    (hs0 : 0 ≤ 2080 + n + (m - ds)) (hsL : 2080 + n + (m - ds) < L) (hy : f (2080 + n + (m - ds)) = y)
    (ho0 : 0 ≤ 2080 + n + m) (hoL : 2080 + n + m < L)
    (rr1 : inRange (2080 + n) = true) (rr2 : inRange (m - ds) = true) (rr3 : inRange (2080 + n + (m - ds)) = true)
    (rr4 : inRange (2080 + n + m) = true) (rr5 : inRange (2080 + n) = true) (rr6 : inRange (m - ds) = true) (rr7 : inRange (2080 + n + (m - ds)) = true)
    (rr8 : inRange (m + 1) = true) (rr9 : inRange (2080 + n) = true) (rr10 : inRange (m - ds) = true) (rr11 : inRange (2080 + n + (m - ds)) = true) (rr12 : inRange (2080 + n + m) = true)
    (rr13 : inRange (pd - 1) = true) (rr14 : inRange (2080 + n) = true) (rr15 : inRange (m - ds) = true) (rr16 : inRange (2080 + n + (m - ds)) = true) (rr17 : inRange (2080 + n + m) = true) (rr18 : inRange (m + 1) = true) :
    SrcInRange (closeAt p copyT, σ) := by
  simp only [cPEND, cN, cM, cDIST] at hpd hn hm hds
  have g5 := hw.get (i := 5) (by decide) (by omega) hpd
  have g15 := hw.get (i := 15) (by decide) (by omega) hn
  have g3 := hw.get (i := 3) (by decide) (by omega) hm
  have g6 := hw.get (i := 6) (by decide) (by omega) hds
  have gy := hw.get hs0 hsL hy
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr13, rr14, rr15, rr16, rr17, rr18, rr8, rr9, rr10, rr11, rr12, rr4, rr5, rr6, rr7, rr1, rr2, rr3, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, copyT, copyN, cDIST, hpd0, g5, g15, g3, g6, gy, hs0, hsL, ho0, hoL, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem clread_req_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (i hc X n om : Int) (hi : f cFILL = i) (hhc : f cHCLEN = hc) (hX : f cX = X) (hn : f cN = n) (hom : f cOUTMAX = om)
    (hlt : i < hc) :
    SrcInRange (closeAt p clreadT, σ) := by
  simp only [cFILL, cHCLEN, cX, cN, cOUTMAX] at hi hhc hX hn hom
  have g10 := hw.get (i := 10) (by decide) (by omega) hi
  have g9 := hw.get (i := 9) (by decide) (by omega) hhc
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g15 := hw.get (i := 15) (by decide) (by omega) hn
  have g16 := hw.get (i := 16) (by decide) (by omega) hom
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, clreadT, clreadN, hlt, g10, g9, g79, g15, g16, mCLPUT, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem clread_zero_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (i hc X n om o : Int) (hi : f cFILL = i) (hhc : f cHCLEN = hc) (hX : f cX = X) (hn : f cN = n) (hom : f cOUTMAX = om)
    (hlt : ¬ i < hc) (h19 : i < 19) (hi0 : 0 ≤ i) (hX0 : 0 ≤ X) (hXL : X + 153 ≤ L) (ho : f (X + 134 + i) = o)
    (hc0 : 0 ≤ 2080 + n + om + 318 + o) (hcL : 2080 + n + om + 318 + o < L)
    (rr1 : inRange (X + 134) = true) (rr2 : inRange (X + 134 + i) = true)
    (rr3 : inRange (2080 + n) = true) (rr4 : inRange (2080 + n + om) = true) (rr5 : inRange (2080 + n + om + 318) = true) (rr6 : inRange (2080 + n + om + 318 + o) = true) (rr7 : inRange (X + 134) = true) (rr8 : inRange (X + 134 + i) = true)
    (rr9 : inRange (i + 1) = true) (rr10 : inRange (X + 134) = true) (rr11 : inRange (X + 134 + i) = true) (rr12 : inRange (2080 + n) = true) (rr13 : inRange (2080 + n + om) = true) (rr14 : inRange (2080 + n + om + 318) = true) (rr15 : inRange (2080 + n + om + 318 + o) = true) :
    SrcInRange (closeAt p clreadT, σ) := by
  simp only [cFILL, cHCLEN, cX, cN, cOUTMAX] at hi hhc hX hn hom
  have g10 := hw.get (i := 10) (by decide) (by omega) hi
  have g9 := hw.get (i := 9) (by decide) (by omega) hhc
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g15 := hw.get (i := 15) (by decide) (by omega) hn
  have g16 := hw.get (i := 16) (by decide) (by omega) hom
  have go := hw.get (i := X + 134 + i) (by omega) (by omega) ho
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr9, rr10, rr11, rr12, rr13, rr14, rr15, rr3, rr4, rr5, rr6, rr7, rr8, rr1, rr2, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, clreadT, clreadN, hlt, h19, g10, g9, g79, g15, g16, go, hc0, hcL, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega,
    show X + 134 + i < L by omega, show (0 : Int) ≤ X + 134 + i by omega])

set_option maxHeartbeats 4000000 in
theorem clread_end_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (i hc X n om : Int) (hi : f cFILL = i) (hhc : f cHCLEN = hc) (hX : f cX = X) (hn : f cN = n) (hom : f cOUTMAX = om)
    (hlt : ¬ i < hc) (h19 : ¬ i < 19) (hX0 : 0 ≤ X) (hXL : X + 153 ≤ L)
    (rr1 : inRange (X + 5) = true) (rr2 : inRange (2080 + n) = true) (rr3 : inRange (2080 + n + om) = true) (rr4 : inRange (2080 + n + om + 318) = true)
    (rr5 : inRange (X + 6) = true) (rr6 : inRange (X + 5) = true) (rr7 : inRange (2080 + n) = true) (rr8 : inRange (2080 + n + om) = true) (rr9 : inRange (2080 + n + om + 318) = true)
    (rr10 : inRange (X + 7) = true) (rr11 : inRange (2080 + n + om + 337) = true) (rr12 : inRange (X + 5) = true) (rr13 : inRange (2080 + n) = true) (rr14 : inRange (2080 + n + om) = true) (rr15 : inRange (2080 + n + om + 318) = true) (rr16 : inRange (X + 6) = true)
    (rr17 : inRange (X + 8) = true) (rr18 : inRange (X + 5) = true) (rr19 : inRange (2080 + n) = true) (rr20 : inRange (2080 + n + om) = true) (rr21 : inRange (2080 + n + om + 318) = true) (rr22 : inRange (X + 6) = true) (rr23 : inRange (X + 7) = true) (rr24 : inRange (2080 + n + om + 337) = true) :
    SrcInRange (closeAt p clreadT, σ) := by
  simp only [cFILL, cHCLEN, cX, cN, cOUTMAX] at hi hhc hX hn hom
  have g10 := hw.get (i := 10) (by decide) (by omega) hi
  have g9 := hw.get (i := 9) (by decide) (by omega) hhc
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g15 := hw.get (i := 15) (by decide) (by omega) hn
  have g16 := hw.get (i := 16) (by decide) (by omega) hom
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr17, rr18, rr19, rr20, rr21, rr22, rr23, rr24, rr10, rr11, rr12, rr13, rr14, rr15, rr16, rr5, rr6, rr7, rr8, rr9, rr1, rr2, rr3, rr4, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, clreadT, clreadN, hlt, h19, g10, g9, g79, g15, g16, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega, show X + 5 < L by omega, show (0 : Int) ≤ X + 5 by omega, show X + 6 < L by omega, show (0 : Int) ≤ X + 6 by omega, show X + 7 < L by omega, show (0 : Int) ≤ X + 7 by omega, show X + 8 < L by omega, show (0 : Int) ≤ X + 8 by omega])

set_option maxHeartbeats 4000000 in
theorem lens_req_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (fl hl hd X n om : Int) (hfl : f cFILL = fl) (hhl : f cHLIT = hl) (hhd : f cHDIST = hd) (hX : f cX = X) (hn : f cN = n)
    (hom : f cOUTMAX = om) (hlt : fl < hl + hd) (hX0 : 0 ≤ X) (hXL : X + 8 < L)
    (rr1 : inRange (hl + hd) = true)
    (rr2 : inRange (X + 1) = true) (rr3 : inRange (hl + hd) = true)
    (rr4 : inRange (X + 2) = true) (rr5 : inRange (hl + hd) = true) (rr6 : inRange (X + 1) = true)
    (rr7 : inRange (X + 3) = true) (rr8 : inRange (hl + hd) = true) (rr9 : inRange (X + 1) = true) (rr10 : inRange (X + 2) = true) :
    SrcInRange (closeAt p lensT, σ) := by
  simp only [cFILL, cHLIT, cHDIST, cX, cN, cOUTMAX] at hfl hhl hhd hX hn hom
  have g10 := hw.get (i := 10) (by decide) (by omega) hfl
  have g7 := hw.get (i := 7) (by decide) (by omega) hhl
  have g8 := hw.get (i := 8) (by decide) (by omega) hhd
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g15 := hw.get (i := 15) (by decide) (by omega) hn
  have g16 := hw.get (i := 16) (by decide) (by omega) hom
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr7, rr8, rr9, rr10, rr4, rr5, rr6, rr2, rr3, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, cLAST, reqDecN, reqDecH, mLENS, lensT, lensN, hlt, g10, g7, g8, g79, g15, g16, mLSYM, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (11 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega, hX0, show X < L by omega, show X + 1 < L by omega, show (0 : Int) ≤ X + 1 by omega, show X + 2 < L by omega, show (0 : Int) ≤ X + 2 by omega, show X + 3 < L by omega, show (0 : Int) ≤ X + 3 by omega])

set_option maxHeartbeats 4000000 in
theorem lens_end_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (fl hl hd X n om z : Int) (hfl : f cFILL = fl) (hhl : f cHLIT = hl) (hhd : f cHDIST = hd) (hX : f cX = X)
    (hn : f cN = n) (hom : f cOUTMAX = om) (hlt : ¬ fl < hl + hd) (hX0 : 0 ≤ X) (hXL : X + 8 < L)
    (hz0 : 0 ≤ 2080 + n + om + 256) (hzL : 2080 + n + om + 256 < L) (hz : f (2080 + n + om + 256) = z)
    (rr1 : inRange (hl + hd) = true)
    (rr2 : inRange (2080 + n) = true) (rr3 : inRange (2080 + n + om) = true) (rr4 : inRange (2080 + n + om + 256) = true) (rr5 : inRange (hl + hd) = true)
    (rr6 : inRange (X + 5) = true) (rr7 : inRange (hl + hd) = true) (rr8 : inRange (2080 + n) = true) (rr9 : inRange (2080 + n + om) = true) (rr10 : inRange (2080 + n + om + 256) = true)
    (rr11 : inRange (X + 6) = true) (rr12 : inRange (hl + hd) = true) (rr13 : inRange (2080 + n) = true) (rr14 : inRange (2080 + n + om) = true) (rr15 : inRange (2080 + n + om + 256) = true) (rr16 : inRange (X + 5) = true)
    (rr17 : inRange (X + 7) = true) (rr18 : inRange (2080 + n + om + 689) = true) (rr19 : inRange (hl + hd) = true) (rr20 : inRange (2080 + n) = true) (rr21 : inRange (2080 + n + om) = true) (rr22 : inRange (2080 + n + om + 256) = true) (rr23 : inRange (X + 5) = true) (rr24 : inRange (X + 6) = true)
    (rr25 : inRange (X + 8) = true) (rr26 : inRange (hl + hd) = true) (rr27 : inRange (2080 + n) = true) (rr28 : inRange (2080 + n + om) = true) (rr29 : inRange (2080 + n + om + 256) = true) (rr30 : inRange (X + 5) = true) (rr31 : inRange (X + 6) = true) (rr32 : inRange (X + 7) = true) (rr33 : inRange (2080 + n + om + 689) = true) :
    SrcInRange (closeAt p lensT, σ) := by
  simp only [cFILL, cHLIT, cHDIST, cX, cN, cOUTMAX] at hfl hhl hhd hX hn hom
  have g10 := hw.get (i := 10) (by decide) (by omega) hfl
  have g7 := hw.get (i := 7) (by decide) (by omega) hhl
  have g8 := hw.get (i := 8) (by decide) (by omega) hhd
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g15 := hw.get (i := 15) (by decide) (by omega) hn
  have g16 := hw.get (i := 16) (by decide) (by omega) hom
  have gz := hw.get hz0 hzL hz
  by_cases h0 : z = 0
  · subst h0
    repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr25, rr26, rr27, rr28, rr29, rr30, rr31, rr32, rr33, rr17, rr18, rr19, rr20, rr21, rr22, rr23, rr24, rr11, rr12, rr13, rr14, rr15, rr16, rr6, rr7, rr8, rr9, rr10, rr2, rr3, rr4, rr5, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, cLAST, reqDecN, reqDecH, mLENS, lensT, lensN, hlt, g10, g7, g8, g79, g15, g16, gz, hz0, hzL, rNOEOB, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (11 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega])
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr25, rr26, rr27, rr28, rr29, rr30, rr31, rr32, rr33, rr17, rr18, rr19, rr20, rr21, rr22, rr23, rr24, rr11, rr12, rr13, rr14, rr15, rr16, rr6, rr7, rr8, rr9, rr10, rr2, rr3, rr4, rr5, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, cLAST, reqDecN, reqDecH, mLENS, lensT, lensN, hlt, h0, g10, g7, g8, g79, g15, g16, gz, hz0, hzL, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (11 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega, show X + 5 < L by omega, show (0 : Int) ≤ X + 5 by omega, show X + 6 < L by omega, show (0 : Int) ≤ X + 6 by omega, show X + 7 < L by omega, show (0 : Int) ≤ X + 7 by omega, show X + 8 < L by omega, show (0 : Int) ≤ X + 8 by omega])

set_option maxHeartbeats 4000000 in
theorem lsym_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (X s fl n om pv : Int) (hX : f cX = X) (hX0 : 0 ≤ X) (hXL : X + 8 < L) (hs : f (X + 4) = s) (hfl : f cFILL = fl)
    (hn : f cN = n) (hom : f cOUTMAX = om) (hw0 : s ≤ 15 → 0 ≤ 2080 + n + om + fl ∧ 2080 + n + om + fl < L)
    (hp0 : s = 16 → fl ≠ 0 → 0 ≤ 2080 + n + om + (fl - 1) ∧ 2080 + n + om + (fl - 1) < L)
    (hpv : f (2080 + n + om + (fl - 1)) = pv)
    (rr1 : inRange (X + 4) = true)
    (rr2 : inRange (2080 + n) = true) (rr3 : inRange (2080 + n + om) = true) (rr4 : inRange (2080 + n + om + fl) = true) (rr5 : inRange (X + 4) = true) (rr6 : inRange (fl - 1) = true) (rr7 : inRange (2080 + n + om + (fl - 1)) = true)
    (rr8 : inRange (fl + 1) = true) (rr9 : inRange (X + 4) = true) (rr10 : inRange (2080 + n) = true) (rr11 : inRange (2080 + n + om) = true) (rr12 : inRange (2080 + n + om + fl) = true) (rr13 : inRange (fl - 1) = true) (rr14 : inRange (2080 + n + om + (fl - 1)) = true) :
    SrcInRange (closeAt p lsymT, σ) := by
  simp only [cX, cFILL, cN, cOUTMAX] at hX hfl hn hom
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have gs := hw.get (i := X + 4) (by omega) (by omega) hs
  have g10 := hw.get (i := 10) (by decide) (by omega) hfl
  have g15 := hw.get (i := 15) (by decide) (by omega) hn
  have g16 := hw.get (i := 16) (by decide) (by omega) hom
  by_cases h1 : s ≤ 15
  · obtain ⟨a0, aL⟩ := hw0 h1
    repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr8, rr9, rr10, rr11, rr12, rr13, rr14, rr2, rr3, rr4, rr5, rr6, rr7, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, cLAST, reqDecN, reqDecH, mLENS, lsymT, lsymN, lsymH, h1, g79, gs, g10, g15, g16, a0, aL, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (11 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega, show X + 4 < L by omega, show (0 : Int) ≤ X + 4 by omega])
  by_cases h2 : s = 16
  · subst h2
    by_cases h3 : fl = 0
    · subst h3
      repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr8, rr9, rr10, rr11, rr12, rr13, rr14, rr2, rr3, rr4, rr5, rr6, rr7, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, cLAST, reqDecN, reqDecH, mLENS, lsymT, lsymN, lsymH, g79, gs, g10, g15, g16, rNOFIRST, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (11 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega, show X + 4 < L by omega, show (0 : Int) ≤ X + 4 by omega])
    · obtain ⟨a0, aL⟩ := hp0 rfl h3
      have gp := hw.get a0 aL hpv
      repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr8, rr9, rr10, rr11, rr12, rr13, rr14, rr2, rr3, rr4, rr5, rr6, rr7, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, cLAST, reqDecN, reqDecH, mLENS, lsymT, lsymN, lsymH, h3, g79, gs, g10, g15, g16, gp, a0, aL, mLREP, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (11 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega, show X + 4 < L by omega, show (0 : Int) ≤ X + 4 by omega])
  by_cases h4 : s = 17
  · subst h4
    repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr8, rr9, rr10, rr11, rr12, rr13, rr14, rr2, rr3, rr4, rr5, rr6, rr7, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, cLAST, reqDecN, reqDecH, mLENS, lsymT, lsymN, lsymH, g79, gs, g10, g15, g16, mLREP, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (11 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega, show X + 4 < L by omega, show (0 : Int) ≤ X + 4 by omega])
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr8, rr9, rr10, rr11, rr12, rr13, rr14, rr2, rr3, rr4, rr5, rr6, rr7, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, cLAST, reqDecN, reqDecH, mLENS, lsymT, lsymN, lsymH, h1, h2, h4, g79, gs, g10, g15, g16, mLREP, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (11 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega, show X + 4 < L by omega, show (0 : Int) ≤ X + 4 by omega])

set_option maxHeartbeats 4000000 in
theorem lrep_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (pd a fl hl hd : Int) (hpd : f cPEND = pd) (ha : f cACC = a) (hfl : f cFILL = fl) (hhl : f cHLIT = hl)
    (hhd : f cHDIST = hd)
    (rr1 : inRange (hl + hd) = true) (rr2 : inRange (pd + a) = true) (rr3 : inRange (fl + (pd + a)) = true) :
    SrcInRange (closeAt p lrepT, σ) := by
  simp only [cPEND, cACC, cFILL, cHLIT, cHDIST] at hpd ha hfl hhl hhd
  have g5 := hw.get (i := 5) (by decide) (by omega) hpd
  have g69 := hw.get (i := 2069) (by decide) (by omega) ha
  have g10 := hw.get (i := 10) (by decide) (by omega) hfl
  have g7 := hw.get (i := 7) (by decide) (by omega) hhl
  have g8 := hw.get (i := 8) (by decide) (by omega) hhd
  by_cases h : hl + hd < fl + (pd + a)
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr1, rr2, rr3, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, cLAST, reqDecN, reqDecH, mLENS, lrepT, lrepN, h, g5, g69, g10, g7, g8, rREPEAT, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (11 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega])
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr1, rr2, rr3, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, cLAST, reqDecN, reqDecH, mLENS, lrepT, lrepN, h, g5, g69, g10, g7, g8, mREP, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (11 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem rep_end_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (hpd : f cPEND = 0) :
    SrcInRange (closeAt p repT, σ) := by
  simp only [cPEND] at hpd
  have g5 := hw.get (i := 5) (by decide) (by omega) hpd
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, cLAST, reqDecN, reqDecH, mLENS, repT, repN, g5, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (11 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem rep_byte_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (pd fl la n om : Int) (hpd : f cPEND = pd) (hpd0 : pd ≠ 0) (hfl : f cFILL = fl) (hla : f cLAST = la) (hn : f cN = n)
    (hom : f cOUTMAX = om) (ha0 : 0 ≤ 2080 + n + om + fl) (haL : 2080 + n + om + fl < L)
    (rr1 : inRange (2080 + n) = true) (rr2 : inRange (2080 + n + om) = true) (rr3 : inRange (2080 + n + om + fl) = true)
    (rr4 : inRange (fl + 1) = true) (rr5 : inRange (2080 + n) = true) (rr6 : inRange (2080 + n + om) = true) (rr7 : inRange (2080 + n + om + fl) = true)
    (rr8 : inRange (pd - 1) = true) (rr9 : inRange (2080 + n) = true) (rr10 : inRange (2080 + n + om) = true) (rr11 : inRange (2080 + n + om + fl) = true) (rr12 : inRange (fl + 1) = true) :
    SrcInRange (closeAt p repT, σ) := by
  simp only [cPEND, cFILL, cLAST, cN, cOUTMAX] at hpd hfl hla hn hom
  have g5 := hw.get (i := 5) (by decide) (by omega) hpd
  have g10 := hw.get (i := 10) (by decide) (by omega) hfl
  have g11 := hw.get (i := 11) (by decide) (by omega) hla
  have g15 := hw.get (i := 15) (by decide) (by omega) hn
  have g16 := hw.get (i := 16) (by decide) (by omega) hom
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr8, rr9, rr10, rr11, rr12, rr4, rr5, rr6, rr7, rr1, rr2, rr3, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, cLAST, reqDecN, reqDecH, mLENS, repT, repN, hpd0, g5, g10, g11, g15, g16, ha0, haL, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (11 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega])

end K5
