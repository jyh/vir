/-
  O95, K5-2 (STATUS-vir 295): TABLE on the checked runner. Two checked loads reach the BITc call; `bit_reach` (K5/Bit.lean)
  carries the call (POW/STRIP's arithmetic, every intermediate atom in range) to its result; the stores and the counter
  carry are walked as every other mode trace. Hypotheses: Safety's `tb_rng` (0 ≤ tb < 256 at TABLE, 0 ≤ ti ≤ 7).
-/
import K5.Bit

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step

set_option maxHeartbeats 4000000 in
theorem table_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2068 ≤ L)
    (tb ti : Nat) (htb : f cTB = tb) (hti : f cTI = ti) (htb8 : tb < 256) (hti8 : ti ≤ 7) :
    SrcInRange (closeAt p tableT, σ) := by
  have hb := hw.cell 18 (by decide) (by omega)
  have hi := hw.cell 19 (by decide) (by omega)
  simp only [cTB, cTI] at htb hti
  have r1 : inRange (8 * (tb : Int)) = true := inRange_eq (by omega) (by omega)
  have r2 : inRange (8 * (tb : Int) + ti) = true := inRange_eq (by omega) (by omega)
  have r3 : inRange (20 + (8 * (tb : Int) + ti)) = true := inRange_eq (by omega) (by omega)
  have r4 : inRange ((tb : Int) + 1) = true := inRange_eq (by omega) (by omega)
  have r5 : inRange ((ti : Int) + 1) = true := inRange_eq (by omega) (by omega)
  have r6 : inRange (8 * (tb : Int) + 7) = true := inRange_eq (by omega) (by omega)
  have r7 : inRange (20 + (8 * (tb : Int) + 7)) = true := inRange_eq (by omega) (by omega)
  have r8 : inRange ((7 : Int) + 1) = true := inRange_eq (by omega) (by omega)
  have r9 : inRange (256 : Int) = true := inRange_eq (by norm_num) (by norm_num)
  have htb' : ¬ ((tb : Int) = 256) := by omega
  have hidx7 : (20 : Int) + (8 * tb + 7) < L := by omega
  have hnn7 : (0 : Int) ≤ 20 + (8 * tb + 7) := by omega
  have hidx : (20 : Int) + (8 * tb + ti) < L := by omega
  have hnn : (0 : Int) ≤ 20 + (8 * tb + ti) := by omega
  refine srcInRange_runC 2 _ ?_
  simp [closeAt, tableT, tableN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL,
    run₂C, stepFn₂C, headB, aInR, aInRL, stepFn₂, stepFn, opStep, Store.load, hw.reg, hb, hi, htb, hti, Atom.eval, Atom.evalL,
    cTB, cTI, BITc_subst, show (18 : Int) < L by omega, show (19 : Int) < L by omega]
  refine (bit_reach (tb : Int) ti (by omega) (by omega) hti8 _ (by simp [Atom.eval]) (by simp [aInR]) _ _ _).srcInRange ?_
  by_cases h7 : (ti : Int) = 7 <;> by_cases h256 : (tb : Int) + 1 = 256 <;>
  repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [h7, h256, r1, r2, r3, r4, r5, r6, r7, r8, r9, htb', hidx, hnn, hidx7, hnn7,
    headB, aInR, aInRL, cInR, Tm.subst, Atom.subst, Atom.substL, stepFn₂, stepFn, opStep, Store.store, Store.load, hw.reg,
    Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool, BT, cTB, cTI, cMODE,
    mHDR, show (18 : Int) < L by omega, show (19 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega])

end K5
