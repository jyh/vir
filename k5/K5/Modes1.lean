/-
  O95, K5-2 route A: the mode traces of Step.lean, re-run on the checked runner (generated from Step.lean by a porter that
  only swaps the conclusion and wraps each trace simp in the one-step walk; range facts are added by hand where a build asks).
-/
import K5.Read

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate.Step

set_option maxHeartbeats 4000000 in
theorem hdrb_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (a : Int) (ha : f cACC = a) :
    SrcInRange (closeAt p hdrbT, σ) := by
  simp only [cACC] at ha
  have hia := hw.cell 2069 (by decide) (by omega)
  rw [ha] at hia
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, closeAt, hdrbT, hdrbN, reqN, reqH, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst,
    Atom.substL, stepFn₂, stepFn, opStep, Store.load, Store.store, hw.reg, hia, Atom.eval, Atom.evalL, cK, cACC, cWT,
    cRET, cMODE, cBF, mREAD, mHDRD, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega,
    show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (4 : Int) < L by omega,
    show (0 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem hdrd_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (a : Int) (ha : f cACC = a) :
    SrcInRange (closeAt p hdrdT, σ) := by
  simp only [cACC] at ha
  have hia := hw.cell 2069 (by decide) (by omega)
  rw [ha] at hia
  by_cases h0 : a = 0
  · subst h0
    repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, closeAt, hdrdT, hdrdN, hdrdH, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst,
      Atom.substL, stepFn₂, stepFn, opStep, Store.load, Store.store, hw.reg, hia, Atom.eval, Atom.evalL, constsOf, S₂,
      pInterp, L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool, cACC, cMODE, mSHDR,
      show (2069 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega])
  by_cases h1 : a = 1
  · subst h1
    repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, closeAt, hdrdT, hdrdN, hdrdH, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst,
      Atom.substL, stepFn₂, stepFn, opStep, Store.load, Store.store, hw.reg, hia, Atom.eval, Atom.evalL, constsOf, S₂,
      pInterp, L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool, cACC, cMODE, cFILL, mFIXLENS,
      show (2069 : Int) < L by omega, show (10 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega])
  by_cases h2 : a = 2
  · subst h2
    repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, closeAt, hdrdT, hdrdN, hdrdH, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst,
      Atom.substL, stepFn₂, stepFn, opStep, Store.load, Store.store, hw.reg, hia, Atom.eval, Atom.evalL, constsOf, S₂,
      pInterp, L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool, cACC, cMODE, mDHDR,
      show (2069 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega])
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, closeAt, hdrdT, hdrdN, hdrdH, h0, h1, h2, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst,
    Atom.subst, Atom.substL, stepFn₂, stepFn, opStep, Store.load, Store.store, hw.reg, hia, Atom.eval, Atom.evalL,
    constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool, cACC, cMODE, cREASON, rBTYPE, mREJECT,
    show (2069 : Int) < L by omega, show (14 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem shdr_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (bx bi : Int) (hby : f cBY = bx) (hbi : f cBI = bi)
    (rr1 : inRange (bx + 1) = true) :
    SrcInRange (closeAt p shdrT, σ) := by
  simp only [cBY, cBI] at hby hbi
  have h1 := hw.cell 1 (by decide) (by omega)
  have h2 := hw.cell 2 (by decide) (by omega)
  rw [hby] at h1; rw [hbi] at h2
  by_cases h0 : bi = 0
  · subst h0
    repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr1, shdrT, shdrN, reqN, reqH, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, h1, h2, cBY, cBI, cK, cACC, cWT, cRET, cMODE, mREAD, mSLEN,
      show (1 : Int) < L by omega, show (2 : Int) < L by omega, show (2068 : Int) < L by omega,
      show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega,
      show (0 : Int) < L by omega, show 0 < L by omega])
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr1, shdrT, shdrN, reqN, reqH, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, h0, h1, h2, cBY, cBI, cK, cACC, cWT, cRET, cMODE, mREAD, mSLEN,
      show (1 : Int) < L by omega, show (2 : Int) < L by omega, show (2068 : Int) < L by omega,
      show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega,
      show (0 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem slen_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (a : Int) (ha : f cACC = a) :
    SrcInRange (closeAt p slenT, σ) := by
  simp only [cACC] at ha
  have hia := hw.cell 2069 (by decide) (by omega)
  rw [ha] at hia
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, slenT, slenN, reqN, reqH, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, hia, cK, cACC, cWT, cRET, cMODE, cPEND, mREAD, mSNLEN,
    show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega,
    show (2071 : Int) < L by omega, show (5 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem snlen_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (a len bx n m om : Int) (ha : f cACC = a) (hlen : f cPEND = len) (hby : f cBY = bx) (hn : f cN = n) (hm : f cM = m)
    (hom : f cOUTMAX = om)
    (rr1 : inRange (a + len) = true)
    (rr2 : inRange (bx + len) = true) (rr3 : inRange (a + len) = true)
    (rr4 : inRange (m + len) = true) (rr5 : inRange (a + len) = true) (rr6 : inRange (bx + len) = true) :
    SrcInRange (closeAt p snlenT, σ) := by
  simp only [cACC, cPEND, cBY, cN, cM, cOUTMAX] at ha hlen hby hn hm hom
  have hia := hw.cell 2069 (by decide) (by omega)
  have h5 := hw.cell 5 (by decide) (by omega)
  have h1 := hw.cell 1 (by decide) (by omega)
  have h15 := hw.cell 15 (by decide) (by omega)
  have h3 := hw.cell 3 (by decide) (by omega)
  have h16 := hw.cell 16 (by decide) (by omega)
  rw [ha] at hia; rw [hlen] at h5; rw [hby] at h1; rw [hn] at h15; rw [hm] at h3; rw [hom] at h16
  by_cases hs : a + len = 65535
  · by_cases ht : n < bx + len
    · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr4, rr5, rr6, (inRange_eq (by norm_num) (by norm_num) : inRange 65535 = true), rr2, rr3, (inRange_eq (by norm_num) (by norm_num) : inRange 65535 = true), (inRange_eq (by norm_num) (by norm_num) : inRange 65535 = true), rr1, snlenT, snlenN, snlenH, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, hs, ht, hia, h5, h1, h15, h3, h16, cACC, cPEND, cBY, cN, cM, cOUTMAX, cMODE,
        cREASON, rTRUNC, mREJECT, show (2069 : Int) < L by omega, show (5 : Int) < L by omega, show (1 : Int) < L by omega,
        show (15 : Int) < L by omega, show (3 : Int) < L by omega, show (16 : Int) < L by omega,
        show (14 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega])
    · by_cases ho : om < m + len
      · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr4, rr5, rr6, (inRange_eq (by norm_num) (by norm_num) : inRange 65535 = true), rr2, rr3, (inRange_eq (by norm_num) (by norm_num) : inRange 65535 = true), (inRange_eq (by norm_num) (by norm_num) : inRange 65535 = true), rr1, snlenT, snlenN, snlenH, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, hs, ht, ho, hia, h5, h1, h15, h3, h16, cACC, cPEND, cBY, cN, cM, cOUTMAX,
          cMODE, cREASON, rOVER, mREJECT, show (2069 : Int) < L by omega, show (5 : Int) < L by omega,
          show (1 : Int) < L by omega, show (15 : Int) < L by omega, show (3 : Int) < L by omega,
          show (16 : Int) < L by omega, show (14 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega])
      · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr4, rr5, rr6, (inRange_eq (by norm_num) (by norm_num) : inRange 65535 = true), rr2, rr3, (inRange_eq (by norm_num) (by norm_num) : inRange 65535 = true), (inRange_eq (by norm_num) (by norm_num) : inRange 65535 = true), rr1, snlenT, snlenN, snlenH, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, hs, ht, ho, hia, h5, h1, h15, h3, h16, cACC, cPEND, cBY, cN, cM, cOUTMAX,
          cMODE, mSCOPY, show (2069 : Int) < L by omega, show (5 : Int) < L by omega, show (1 : Int) < L by omega,
          show (15 : Int) < L by omega, show (3 : Int) < L by omega, show (16 : Int) < L by omega,
          show (0 : Int) < L by omega, show 0 < L by omega])
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr4, rr5, rr6, (inRange_eq (by norm_num) (by norm_num) : inRange 65535 = true), rr2, rr3, (inRange_eq (by norm_num) (by norm_num) : inRange 65535 = true), (inRange_eq (by norm_num) (by norm_num) : inRange 65535 = true), rr1, snlenT, snlenN, snlenH, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, hs, hia, h5, h1, h15, h3, h16, cACC, cPEND, cBY, cN, cM, cOUTMAX, cMODE,
      cREASON, rSTORED, mREJECT, show (2069 : Int) < L by omega, show (5 : Int) < L by omega, show (1 : Int) < L by omega,
      show (15 : Int) < L by omega, show (3 : Int) < L by omega, show (16 : Int) < L by omega,
      show (14 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem fixlens_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f)
    (i n om : Nat) (hL : 2080 + n + om + 318 ≤ L) (hi : f cFILL = i) (hi318 : i < 318) (hn : f cN = n)
    (hom : f cOUTMAX = om)
    (rr1 : inRange (2080 + (n : Int)) = true) (rr2 : inRange (2080 + (n : Int) + (om : Int)) = true) (rr3 : inRange (2080 + (n : Int) + (om : Int) + (i : Int)) = true)
    (rr4 : inRange ((i : Int) + 1) = true) (rr5 : inRange (2080 + (n : Int)) = true) (rr6 : inRange (2080 + (n : Int) + (om : Int)) = true) (rr7 : inRange (2080 + (n : Int) + (om : Int) + (i : Int)) = true) :
    SrcInRange (closeAt p fixlensT, σ) := by
  simp only [cFILL, cN, cOUTMAX] at hi hn hom
  have h10 := hw.cell 10 (by decide) (by omega)
  have h15 := hw.cell 15 (by decide) (by omega)
  have h16 := hw.cell 16 (by decide) (by omega)
  rw [hi] at h10; rw [hn] at h15; rw [hom] at h16
  have hlt : (i : Int) < 318 := by exact_mod_cast hi318
  have haL : (2080 : Int) + n + om + i < L := by omega
  have ha0 : (0 : Int) ≤ 2080 + n + om + i := by omega
  by_cases c1 : (i : Int) < 144
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr4, rr5, rr6, rr7, rr1, rr2, rr3, fixlensT, fixlensN, fixLenI, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, hlt, c1, h10, h15, h16, haL, ha0, cFILL, cN, cOUTMAX, IN,
      show (10 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega,
      show (0 : Int) < L by omega, show 0 < L by omega])
  by_cases c2 : (i : Int) < 256
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr4, rr5, rr6, rr7, rr1, rr2, rr3, fixlensT, fixlensN, fixLenI, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, hlt, c1, c2, h10, h15, h16, haL, ha0, cFILL, cN, cOUTMAX, IN,
      show (10 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega,
      show (0 : Int) < L by omega, show 0 < L by omega])
  by_cases c3 : (i : Int) < 280
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr4, rr5, rr6, rr7, rr1, rr2, rr3, fixlensT, fixlensN, fixLenI, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, hlt, c1, c2, c3, h10, h15, h16, haL, ha0, cFILL, cN, cOUTMAX, IN,
      show (10 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega,
      show (0 : Int) < L by omega, show 0 < L by omega])
  by_cases c4 : (i : Int) < 288
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr4, rr5, rr6, rr7, rr1, rr2, rr3, fixlensT, fixlensN, fixLenI, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, hlt, c1, c2, c3, c4, h10, h15, h16, haL, ha0, cFILL, cN, cOUTMAX, IN,
      show (10 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega,
      show (0 : Int) < L by omega, show 0 < L by omega])
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr4, rr5, rr6, rr7, rr1, rr2, rr3, fixlensT, fixlensN, fixLenI, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, hlt, c1, c2, c3, c4, h10, h15, h16, haL, ha0, cFILL, cN, cOUTMAX, IN,
    show (10 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega,
    show (0 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem fixlens_end_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (n om lit X : Int) (hi : f cFILL = 318) (hn : f cN = n) (hom : f cOUTMAX = om) (hlit : f cLIT = lit) (hX : f cX = X)
    (hX0 : 0 ≤ X) (hXL : X + 8 < L)
    (rr1 : inRange (X + 5) = true) (rr2 : inRange (2080 + n) = true) (rr3 : inRange (2080 + n + om) = true)
    (rr4 : inRange (X + 6) = true) (rr5 : inRange (X + 5) = true) (rr6 : inRange (2080 + n) = true) (rr7 : inRange (2080 + n + om) = true)
    (rr8 : inRange (X + 7) = true) (rr9 : inRange (2080 + n + om + 689) = true) (rr10 : inRange (X + 5) = true) (rr11 : inRange (2080 + n) = true) (rr12 : inRange (2080 + n + om) = true) (rr13 : inRange (X + 6) = true)
    (rr14 : inRange (X + 8) = true) (rr15 : inRange (X + 5) = true) (rr16 : inRange (2080 + n) = true) (rr17 : inRange (2080 + n + om) = true) (rr18 : inRange (X + 6) = true) (rr19 : inRange (X + 7) = true) (rr20 : inRange (2080 + n + om + 689) = true) :
    SrcInRange (closeAt p fixlensT, σ) := by
  simp only [cFILL, cN, cOUTMAX, cLIT, cX] at hi hn hom hlit hX
  have h10 := hw.cell 10 (by decide) (by omega)
  have h15 := hw.cell 15 (by decide) (by omega)
  have h16 := hw.cell 16 (by decide) (by omega)
  have h17 := hw.cell 17 (by decide) (by omega)
  have h2079 := hw.cell 2079 (by decide) (by omega)
  rw [hi] at h10; rw [hn] at h15; rw [hom] at h16; rw [hlit] at h17; rw [hX] at h2079
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr14, rr15, rr16, rr17, rr18, rr19, rr20, rr8, rr9, rr10, rr11, rr12, rr13, rr4, rr5, rr6, rr7, rr1, rr2, rr3, fixlensT, fixlensN, closeAt, h2079, cX, IN, show (2079 : Int) < L by omega,
    show (0 : Int) ≤ X + 5 by omega, show X + 5 < L by omega, show (0 : Int) ≤ X + 6 by omega, show X + 6 < L by omega,
    show (0 : Int) ≤ X + 7 by omega, show X + 7 < L by omega, show (0 : Int) ≤ X + 8 by omega, show X + 8 < L by omega, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, h10, h15, h16, h17, cFILL, cN, cOUTMAX, cLIT, cHLIT, cHDIST, cCHK, cPHASE, cINDEX,
    cMODE, mBUILD, cTGT, cDYN, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (10 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega,
    show (17 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega,
    show (2072 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega,
    show (0 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem dhdr_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L) :
    SrcInRange (closeAt p dhdrT, σ) := by
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, dhdrT, dhdrN, mDH2, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem dh2_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (a : Int) (ha : f cACC = a)
    (rr1 : inRange (a + 257) = true) :
    SrcInRange (closeAt p dh2T, σ) := by
  simp only [cACC] at ha
  have g := hw.get (i := 2069) (by decide) (by omega) ha
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, dh2T, dh2N, g, mDH3, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem dh3_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (a : Int) (ha : f cACC = a)
    (rr1 : inRange (a + 1) = true) :
    SrcInRange (closeAt p dh3T, σ) := by
  simp only [cACC] at ha
  have g := hw.get (i := 2069) (by decide) (by omega) ha
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, dh3T, dh3N, g, mDH4, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem dh4_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (a hl hd : Int) (ha : f cACC = a) (hhl : f cHLIT = hl) (hhd : f cHDIST = hd)
    (rr1 : inRange (a + 4) = true) :
    SrcInRange (closeAt p dh4T, σ) := by
  simp only [cACC, cHLIT, cHDIST] at ha hhl hhd
  have g := hw.get (i := 2069) (by decide) (by omega) ha
  have g7 := hw.get (i := 7) (by decide) (by omega) hhl
  have g8 := hw.get (i := 8) (by decide) (by omega) hhd
  by_cases h1 : 286 < hl
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, dh4T, dh4N, h1, g, g7, g8, rTOOMANY, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega])
  by_cases h2 : 30 < hd
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, dh4T, dh4N, h1, h2, g, g7, g8, rTOOMANY, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega])
  · repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, dh4T, dh4N, h1, h2, g, g7, g8, mCLREAD, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega])

set_option maxHeartbeats 4000000 in
theorem clput_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (i X n om a o : Int) (hi : f cFILL = i) (hX : f cX = X) (hn : f cN = n) (hom : f cOUTMAX = om) (ha : f cACC = a)
    (hi0 : 0 ≤ i) (h19 : i < 19) (hX0 : 0 ≤ X) (hXL : X + 153 ≤ L) (ho : f (X + 134 + i) = o)
    (hc0 : 0 ≤ 2080 + n + om + 318 + o) (hcL : 2080 + n + om + 318 + o < L)
    (rr1 : inRange (X + 134) = true) (rr2 : inRange (X + 134 + i) = true)
    (rr3 : inRange (2080 + n) = true) (rr4 : inRange (2080 + n + om) = true) (rr5 : inRange (2080 + n + om + 318) = true) (rr6 : inRange (2080 + n + om + 318 + o) = true) (rr7 : inRange (X + 134) = true) (rr8 : inRange (X + 134 + i) = true)
    (rr9 : inRange (i + 1) = true) (rr10 : inRange (X + 134) = true) (rr11 : inRange (X + 134 + i) = true) (rr12 : inRange (2080 + n) = true) (rr13 : inRange (2080 + n + om) = true) (rr14 : inRange (2080 + n + om + 318) = true) (rr15 : inRange (2080 + n + om + 318 + o) = true) :
    SrcInRange (closeAt p clputT, σ) := by
  simp only [cFILL, cX, cN, cOUTMAX, cACC] at hi hX hn hom ha
  have g10 := hw.get (i := 10) (by decide) (by omega) hi
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have g15 := hw.get (i := 15) (by decide) (by omega) hn
  have g16 := hw.get (i := 16) (by decide) (by omega) hom
  have g69 := hw.get (i := 2069) (by decide) (by omega) ha
  have go := hw.get (i := X + 134 + i) (by omega) (by omega) ho
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr9, rr10, rr11, rr12, rr13, rr14, rr15, rr3, rr4, rr5, rr6, rr7, rr8, rr1, rr2, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, cBY, cBI, cN, cOUTMAX, cX, IN, cMODE, cREASON, cM, cPEND, cK, cACC, cWT, cRET,
      cBF, mREAD, mREJECT, mDECODE, mHDR, mDONE, reqN, reqH, rejN, cHLIT, cHDIST, cHCLEN, cFILL, cDYN, cCHK, cTGT, cPHASE,
      cINDEX, mBUILD, clputT, clputN, g10, g79, g15, g16, g69, go, hc0, hcL, mCLREAD, show (0 : Int) < L by omega, show (3 : Int) < L by omega, show (4 : Int) < L by omega, show (5 : Int) < L by omega, show (6 : Int) < L by omega, show (7 : Int) < L by omega, show (8 : Int) < L by omega, show (9 : Int) < L by omega, show (10 : Int) < L by omega, show (12 : Int) < L by omega, show (13 : Int) < L by omega, show (14 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega, show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (2072 : Int) < L by omega, show (2073 : Int) < L by omega, show (2074 : Int) < L by omega, show (2079 : Int) < L by omega, show 0 < L by omega,
    show X + 134 + i < L by omega, show (0 : Int) ≤ X + 134 + i by omega])

end K5
