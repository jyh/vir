/-
  O95 layer L5, Lean arm (STATUS 318, LV8 Deflate5, FIXLENS's i ≥ 318 branch): DEFLATE's own end of FIXLENS, store for store
  (Step.lean `fixlensN`, `fixlens_end`): the table request at X + 5 … X + 8, HLIT 288, HDIST 30, CHK := LIT, PHASE 0, INDEX 0,
  TGT 1, DYN 0, MODE := BUILD. The triple over RegionAt, with no premise on the contents (LV7).
-/
import VIRL5.Fixlens5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- The contents after FIXLENS's end. -/
def fixlensEndPost (p : Int) (g : Int → Int) (n om lit X : Int) : Int → Int :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update g
      (p + (X + 5)) (IN + n + om)) (p + (X + 6)) 288) (p + (X + 7)) (IN + n + om + 689)) (p + (X + 8)) 0)
      (p + cHLIT) 288) (p + cHDIST) 30) (p + cCHK) lit) (p + cPHASE) 0) (p + cINDEX) 0) (p + cTGT) 1) (p + cDYN) 0)
      (p + cMODE) mBUILD

theorem fixlens5_end (p : Int) (L : Nat) (g : Int → Int) (i n om lit X : Int)
    (hi : g (p + cFILL) = i) (hi318 : ¬ i < 318) (hn : g (p + cN) = n) (hom : g (p + cOUTMAX) = om)
    (hlit : g (p + cLIT) = lit) (hX : g (p + cX) = X) (hX0 : 0 ≤ X) (hXL : X + 8 < L) (hL : 2080 ≤ L) :
    Triple₅ (RegionAt p L g) (fixlensT₅.subst 0 (.const (.cap p)))
      (fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (fixlensEndPost p g n om lit X) σ) := by
  simp [fixlensT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cFILL)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cFILL) ⟨by unfold cFILL; omega, by unfold cFILL; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hi]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cN)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cN) ⟨by unfold cN; omega, by unfold cN; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hn]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cOUTMAX)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cOUTMAX) ⟨by unfold cOUTMAX; omega, by unfold cOUTMAX; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hom]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine ite_rule₅ (b := false) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
  simp only [Bool.false_eq_true, if_false]
  refine letOp_rule₅ (cs := [.cap p, .int (cLIT)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cLIT) ⟨by unfold cLIT; omega, by unfold cLIT; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hlit]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cX)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cX) ⟨by unfold cX; omega, by unfold cX; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hX]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (X + 5), .int (IN + n + om)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (X + 5) (IN + n + om) ⟨by omega, by omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (X + 6), .int (288)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (X + 6) (288) ⟨by omega, by omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (X + 7), .int (IN + n + om + 689)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (X + 7) (IN + n + om + 689) ⟨by omega, by omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (X + 8), .int (0)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (X + 8) (0) ⟨by omega, by omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cHLIT), .int (288)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (cHLIT) (288) ⟨by unfold cHLIT; omega, by unfold cHLIT; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cHDIST), .int (30)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (cHDIST) (30) ⟨by unfold cHDIST; omega, by unfold cHDIST; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cCHK), .int (lit)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (cCHK) (lit) ⟨by unfold cCHK; omega, by unfold cCHK; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cPHASE), .int (0)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (cPHASE) (0) ⟨by unfold cPHASE; omega, by unfold cPHASE; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cINDEX), .int (0)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (cINDEX) (0) ⟨by unfold cINDEX; omega, by unfold cINDEX; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cTGT), .int (1)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (cTGT) (1) ⟨by unfold cTGT; omega, by unfold cTGT; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cDYN), .int (0)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (cDYN) (0) ⟨by unfold cDYN; omega, by unfold cDYN; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cMODE), .int (mBUILD)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (cMODE) (mBUILD) ⟨by unfold cMODE; omega, by unfold cMODE; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => h)
    (ret_rule₅ (v := .const (.cap p))
      (Q := fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (fixlensEndPost p g n om lit X) σ) (by simp [Atom₅.eval]))

end VIRL5
