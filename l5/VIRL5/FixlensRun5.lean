/-
  O95 layer L5, Lean arm (STATUS 321 item FIXLENS, LV8-MAP Addendum 5): FIXLENS's Fit5 and World form over ⟶₅. The chunk
  costs 3·c + 20 ⟶₅ steps (c = min(b − i, 32), at most 116) and the end 18, each within KSTEP − 29 = 483. Both run at every
  fuel above that cost (run_of_triple₅), and on a Sole store each gives a World over an explicit cell function. `fixLenI`
  (DEFLATE's length table) is `fixLenV` (the chain5 term's value).
-/
import VIRL5.Fixlens5
import VIRL5.FixlensEnd5
import VIRL5.Costs
import VIRL5.RunTriple5
import VIRL5.ScopyWorld5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

theorem fixLenI_eq_V (i : Int) : fixLenI i = fixLenV i := by
  unfold fixLenI fixLenV chain5; rfl

theorem chain5_cost (P : Assn) (i t1 t2 t3 t4 v1 v2 v3 v4 v5 : Int) :
    Cost₅ P (chain5T (.const (.int i)) t1 t2 t3 t4 v1 v2 v3 v4 v5) 4 := by
  unfold chain5T
  by_cases h1 : i < t1
  · refine Cost₅.mono (n := 0 + 1) (cost_ite₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_) (by omega)
    simp only [if_true]; exact cost_ret₅ _ _
  refine Cost₅.mono (n := 3 + 1) (cost_ite₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_) (by omega)
  simp only [Bool.false_eq_true, if_false]
  by_cases h2 : i < t2
  · refine Cost₅.mono (n := 0 + 1) (cost_ite₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_) (by omega)
    simp only [if_true]; exact cost_ret₅ _ _
  refine Cost₅.mono (n := 2 + 1) (cost_ite₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_) (by omega)
  simp only [Bool.false_eq_true, if_false]
  by_cases h3 : i < t3
  · refine Cost₅.mono (n := 0 + 1) (cost_ite₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_) (by omega)
    simp only [if_true]; exact cost_ret₅ _ _
  refine Cost₅.mono (n := 1 + 1) (cost_ite₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_) (by omega)
  simp only [Bool.false_eq_true, if_false]
  by_cases h4 : i < t4
  · refine Cost₅.mono (n := 0 + 1) (cost_ite₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_) (by omega)
    simp only [if_true]; exact cost_ret₅ _ _
  refine Cost₅.mono (n := 0 + 1) (cost_ite₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_) (by omega)
  simp only [Bool.false_eq_true, if_false]; exact cost_ret₅ _ _

theorem fixlens5_chunk_cost (p : Int) (L : Nat) (g : Int → Int) (i n om : Int)
    (hi : g (p + cFILL) = i) (hi0 : 0 ≤ i) (hi318 : i < 318) (hn : g (p + cN) = n) (hom : g (p + cOUTMAX) = om)
    (hn0 : 0 ≤ n) (hom0 : 0 ≤ om) (hL : IN + n + om + 318 ≤ L) :
    Cost₅ (RegionAt p L g) (fixlensT₅.subst 0 (.const (.cap p))) (3 * (min (fixBndV i - i) CS).toNat + 20) := by
  have hIN : (IN : Int) = 2080 := rfl
  have hb := fixBndV_gt i hi318
  have hb2 := fixBndV_le i
  have hc0 : 0 < min (fixBndV i - i) CS := by unfold CS; omega
  have hcT : ((min (fixBndV i - i) CS).toNat : Int) = min (fixBndV i - i) CS := Int.toNat_of_nonneg (by omega)
  refine Cost₅.mono (n := ((((4 + 1 + (4 + 1 + ((0 + 1) + 1 + (((3 * (min (fixBndV i - i) CS).toNat + 1) + 1) + 1 + (0 + 1))))) + 1) + 1) + 1) + 1) ?_ (by omega)
  simp [fixlensT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int cFILL]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cFILL ⟨by unfold cFILL; omega, by unfold cFILL; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + cFILL))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hi]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int cN]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cN ⟨by unfold cN; omega, by unfold cN; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + cN))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hn]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int cOUTMAX]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cOUTMAX ⟨by unfold cOUTMAX; omega, by unfold cOUTMAX; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + cOUTMAX))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hom]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_ite₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_
  simp only [if_true]
  -- x ← fixLenV i
  refine cost_letE₅ (n₁ := 4) (Q := fun r qs σ => r = .const (.int (fixLenV i)) ∧ qs = [] ∧ RegionAt p L g σ) ?_ ?_
    (fun v qs σ h => h.2.1) (fun v => ?_)
  · simpa [chain5T, Tm₅.subst, Atom₅.subst, Atom₅.substL, fixLenV] using chain5_rule (RegionAt p L g) i 144 256 280 288 8 9 7 8 5
  · simpa [chain5T, Tm₅.subst, Atom₅.subst, Atom₅.substL] using chain5_cost (RegionAt p L g) i 144 256 280 288 8 9 7 8 5
  refine cost_pre_pure₅ (fun hv => ?_)
  subst hv
  refine cost_pre_pure₅ (fun _ => ?_)
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- b ← fixBndV i
  refine cost_letE₅ (n₁ := 4) (Q := fun r qs σ => r = .const (.int (fixBndV i)) ∧ qs = [] ∧ RegionAt p L g σ) ?_ ?_
    (fun v qs σ h => h.2.1) (fun v => ?_)
  · simpa [chain5T, Tm₅.subst, Atom₅.subst, Atom₅.substL, fixBndV] using
      chain5_rule (RegionAt p L g) i 144 256 280 288 144 256 280 288 318
  · simpa [chain5T, Tm₅.subst, Atom₅.subst, Atom₅.substL] using
      chain5_cost (RegionAt p L g) i 144 256 280 288 144 256 280 288 318
  refine cost_pre_pure₅ (fun hv => ?_)
  subst hv
  refine cost_pre_pure₅ (fun _ => ?_)
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- c ← min (b − i) CS
  have hE : Triple₅ (RegionAt p L g) (.ite (.prim .lt [.prim .sub [.const (.int (fixBndV i)), .const (.int i)], .const (.int CS)])
      (.ret (.prim .sub [.const (.int (fixBndV i)), .const (.int i)])) (.ret (.const (.int CS))))
      (fun r qs σ => r = .const (.int (min (fixBndV i - i) CS)) ∧ qs = [] ∧ RegionAt p L g σ) := by
    by_cases hlt : fixBndV i - i < CS
    · refine ite_rule₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_
      simp only [if_true]
      exact conseq₅ (fun σ h => ⟨by rw [min_eq_left (le_of_lt hlt)], rfl, h⟩) (fun r qs σ h => h)
        (ret_rule₅ (v := .const (.int (fixBndV i - i)))
          (Q := fun r qs σ => r = .const (.int (min (fixBndV i - i) CS)) ∧ qs = [] ∧ RegionAt p L g σ)
          (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]))
    · refine ite_rule₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_
      simp only [Bool.false_eq_true, if_false]
      exact conseq₅ (fun σ h => ⟨by rw [min_eq_right (by omega)], rfl, h⟩) (fun r qs σ h => h)
        (ret_rule₅ (v := .const (.int CS))
          (Q := fun r qs σ => r = .const (.int (min (fixBndV i - i) CS)) ∧ qs = [] ∧ RegionAt p L g σ)
          (by simp [Atom₅.eval]))
  have cE : Cost₅ (RegionAt p L g) (.ite (.prim .lt [.prim .sub [.const (.int (fixBndV i)), .const (.int i)], .const (.int CS)])
      (.ret (.prim .sub [.const (.int (fixBndV i)), .const (.int i)])) (.ret (.const (.int CS)))) (0 + 1) := by
    by_cases hlt : fixBndV i - i < CS
    · exact cost_ite₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) (cost_ret₅ _ _)
    · exact cost_ite₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) (cost_ret₅ _ _)
  refine cost_letE₅ (n₁ := 0 + 1) hE cE (fun v qs σ h => h.2.1) (fun v => ?_)
  refine cost_pre_pure₅ (fun hv => ?_)
  subst hv
  refine cost_pre_pure₅ (fun _ => ?_)
  simp [Tm₅.subst, Atom₅.subst, Atom₅.substL]
  set c : Int := min (fixBndV i - i) CS with hcdef
  have ih := fillR_spec p L (fixLenV i) c.toNat (IN + n + om + i) g (by rw [hIN]; omega) (by rw [hcT]; omega)
  have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
  have ic := fillR_cost p L (fixLenV i) c.toNat (IN + n + om + i) g (by rw [hIN]; omega) (by rw [hcT]; omega)
  have ic' := cost_pure_step_rev₅ (n := 3 * c.toNat + 1) (fun σ => Step₅.appKFix rfl rfl rfl rfl) ic
  refine cost_letK₅ (n₁ := (3 * c.toNat + 1) + 1) (Q := fun r qs σ => r = .const .unit ∧ qs = [.const (.cap p)] ∧
      RegionAt p L (fillF g p (IN + n + om + i) c.toNat (fixLenV i)) σ)
    (appKFix_rule₅ rfl ?e1 rfl rfl ih') (cost_appKFix₅ rfl ?e2 rfl rfl ic')
    (fun v qs σ h => by rw [h.2.1]; rfl) (fun v qs _ => ?_)
  case e1 => simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, fillArg, hcT]
  case e2 => simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, fillArg, hcT]
  refine cost_pre_pure₅ (fun hv => ?_)
  subst hv
  refine cost_pre_pure₅ (fun hq => ?_)
  subst hq
  simp [Tm₅.substAll, Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA]
  refine cost_letOp₅ (cs := [.cap p, .int cFILL, .int (i + c)])
    (by simp [Atom₅.evalL, Atom₅.eval, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ cFILL (i + c) ⟨by unfold cFILL; omega, by unfold cFILL; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact cost_ret₅ _ _

theorem fixlens5_end_cost (p : Int) (L : Nat) (g : Int → Int) (i n om lit X : Int)
    (hi : g (p + cFILL) = i) (hi318 : ¬ i < 318) (hn : g (p + cN) = n) (hom : g (p + cOUTMAX) = om)
    (hlit : g (p + cLIT) = lit) (hX : g (p + cX) = X) (hX0 : 0 ≤ X) (hXL : X + 8 < L) (hL : 2080 ≤ L) :
    Cost₅ (RegionAt p L g) (fixlensT₅.subst 0 (.const (.cap p))) 18 := by
  simp [fixlensT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cFILL)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cFILL) ⟨by unfold cFILL; omega, by unfold cFILL; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + (cFILL)))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hi]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cN)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cN) ⟨by unfold cN; omega, by unfold cN; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + (cN)))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hn]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cOUTMAX)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cOUTMAX) ⟨by unfold cOUTMAX; omega, by unfold cOUTMAX; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + (cOUTMAX)))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hom]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_ite₅ (b := false) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
  simp only [Bool.false_eq_true, if_false]
  refine cost_letOp₅ (cs := [.cap p, .int (cLIT)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cLIT) ⟨by unfold cLIT; omega, by unfold cLIT; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + (cLIT)))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hlit]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cX)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cX) ⟨by unfold cX; omega, by unfold cX; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + (cX)))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hX]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (X + 5), .int (IN + n + om)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (X + 5) (IN + n + om) ⟨by omega, by omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (X + 6), .int (288)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (X + 6) (288) ⟨by omega, by omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (X + 7), .int (IN + n + om + 689)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (X + 7) (IN + n + om + 689) ⟨by omega, by omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (X + 8), .int (0)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (X + 8) (0) ⟨by omega, by omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cHLIT), .int (288)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (cHLIT) (288) ⟨by unfold cHLIT; omega, by unfold cHLIT; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cHDIST), .int (30)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (cHDIST) (30) ⟨by unfold cHDIST; omega, by unfold cHDIST; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cCHK), .int (lit)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (cCHK) (lit) ⟨by unfold cCHK; omega, by unfold cCHK; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cPHASE), .int (0)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (cPHASE) (0) ⟨by unfold cPHASE; omega, by unfold cPHASE; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cINDEX), .int (0)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (cINDEX) (0) ⟨by unfold cINDEX; omega, by unfold cINDEX; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cTGT), .int (1)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (cTGT) (1) ⟨by unfold cTGT; omega, by unfold cTGT; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cDYN), .int (0)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (cDYN) (0) ⟨by unfold cDYN; omega, by unfold cDYN; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cMODE), .int (mBUILD)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (cMODE) (mBUILD) ⟨by unfold cMODE; omega, by unfold cMODE; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact cost_ret₅ _ _

theorem fixlens5_chunk_run (p : Int) (L : Nat) (g : Int → Int) (i n om : Int)
    (hi : g (p + cFILL) = i) (hi0 : 0 ≤ i) (hi318 : i < 318) (hn : g (p + cN) = n) (hom : g (p + cOUTMAX) = om)
    (hn0 : 0 ≤ n) (hom0 : 0 ≤ om) (hL : IN + n + om + 318 ≤ L)
    {σ : Store} (hR : RegionAt p L g σ) (hwf : Store.WF σ) {F : Nat} (hF : 3 * (min (fixBndV i - i) CS).toNat + 20 ≤ F) :
    ∃ a, ((run₅ F (fixlensT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
          (run₅ F (fixlensT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧
      a.eval = some (.const (.cap p)) ∧
      RegionAt p L (fixlensPost p g i n om) (run₅ F (fixlensT₅.subst 0 (.const (.cap p)), σ)).2 := by
  obtain ⟨v, qs, ⟨hv, hqs, hreg⟩, hcase⟩ :=
    run_of_triple₅ (fixlens5_chunk p L g i n om hi hi0 hi318 hn hom hn0 hom0 hL)
      (fixlens5_chunk_cost p L g i n om hi hi0 hi318 hn hom hn0 hom0 hL) hR hwf hF
  subst hv
  subst hqs
  rcases hcase with ⟨a, ha, hav, -⟩ | ⟨a, ds, ha, hav, hds⟩
  · exact ⟨a, Or.inl ha, hav, hreg⟩
  · have hl := evalL_length hds
    have hd : ds = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst hd
    exact ⟨a, Or.inr ha, hav, hreg⟩

theorem fixlens5_end_run (p : Int) (L : Nat) (g : Int → Int) (i n om lit X : Int)
    (hi : g (p + cFILL) = i) (hi318 : ¬ i < 318) (hn : g (p + cN) = n) (hom : g (p + cOUTMAX) = om)
    (hlit : g (p + cLIT) = lit) (hX : g (p + cX) = X) (hX0 : 0 ≤ X) (hXL : X + 8 < L) (hL : 2080 ≤ L)
    {σ : Store} (hR : RegionAt p L g σ) (hwf : Store.WF σ) {F : Nat} (hF : 18 ≤ F) :
    ∃ a, ((run₅ F (fixlensT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
          (run₅ F (fixlensT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧
      a.eval = some (.const (.cap p)) ∧
      RegionAt p L (fixlensEndPost p g n om lit X) (run₅ F (fixlensT₅.subst 0 (.const (.cap p)), σ)).2 := by
  obtain ⟨v, qs, ⟨hv, hqs, hreg⟩, hcase⟩ :=
    run_of_triple₅ (fixlens5_end p L g i n om lit X hi hi318 hn hom hlit hX hX0 hXL hL)
      (fixlens5_end_cost p L g i n om lit X hi hi318 hn hom hlit hX hX0 hXL hL) hR hwf hF
  subst hv
  subst hqs
  rcases hcase with ⟨a, ha, hav, -⟩ | ⟨a, ds, ha, hav, hds⟩
  · exact ⟨a, Or.inl ha, hav, hreg⟩
  · have hl := evalL_length hds
    have hd : ds = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst hd
    exact ⟨a, Or.inr ha, hav, hreg⟩

def fixlensPostRel (p : Int) (f : Int → Int) (i n om : Int) : Int → Int :=
  fun j => fixlensPost p (fun a => f (a - p)) i n om (p + j)

def fixlensEndPostRel (p : Int) (f : Int → Int) (n om lit X : Int) : Int → Int :=
  fun j => fixlensEndPost p (fun a => f (a - p)) n om lit X (p + j)

theorem fixlens5_chunk_world (p : Int) (L : Nat) (f : Int → Int) (i n om : Int)
    (hi : f cFILL = i) (hi0 : 0 ≤ i) (hi318 : i < 318) (hn : f cN = n) (hom : f cOUTMAX = om)
    (hn0 : 0 ≤ n) (hom0 : 0 ≤ om) (hL : IN + n + om + 318 ≤ L)
    {σ : Store} (hw : World σ p L f) (hs : Sole σ p L) (hwf : Store.WF σ) {F : Nat}
    (hF : 3 * (min (fixBndV i - i) CS).toNat + 20 ≤ F) :
    ∃ a, ((run₅ F (fixlensT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
          (run₅ F (fixlensT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧
      a.eval = some (.const (.cap p)) ∧
      World (run₅ F (fixlensT₅.subst 0 (.const (.cap p)), σ)).2 p L (fixlensPostRel p f i n om) ∧
      Sole (run₅ F (fixlensT₅.subst 0 (.const (.cap p)), σ)).2 p L := by
  have hR := VIRL5.World.regionAt hw hs
  obtain ⟨a, hterm, hav, hreg⟩ := fixlens5_chunk_run p L (fun a => f (a - p)) i n om
    (by simpa using hi) hi0 hi318 (by simpa using hn) (by simpa using hom) hn0 hom0 hL hR hwf hF
  obtain ⟨hw', hs'⟩ := VIRL5.RegionAt.world hreg
  exact ⟨a, hterm, hav, hw', hs'⟩

theorem fixlens5_end_world (p : Int) (L : Nat) (f : Int → Int) (i n om lit X : Int)
    (hi : f cFILL = i) (hi318 : ¬ i < 318) (hn : f cN = n) (hom : f cOUTMAX = om)
    (hlit : f cLIT = lit) (hX : f cX = X) (hX0 : 0 ≤ X) (hXL : X + 8 < L) (hL : 2080 ≤ L)
    {σ : Store} (hw : World σ p L f) (hs : Sole σ p L) (hwf : Store.WF σ) {F : Nat} (hF : 18 ≤ F) :
    ∃ a, ((run₅ F (fixlensT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
          (run₅ F (fixlensT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧
      a.eval = some (.const (.cap p)) ∧
      World (run₅ F (fixlensT₅.subst 0 (.const (.cap p)), σ)).2 p L (fixlensEndPostRel p f n om lit X) ∧
      Sole (run₅ F (fixlensT₅.subst 0 (.const (.cap p)), σ)).2 p L := by
  have hR := VIRL5.World.regionAt hw hs
  obtain ⟨a, hterm, hav, hreg⟩ := fixlens5_end_run p L (fun a => f (a - p)) i n om lit X
    (by simpa using hi) hi318 (by simpa using hn) (by simpa using hom) (by simpa using hlit) (by simpa using hX)
    hX0 hXL hL hR hwf hF
  obtain ⟨hw', hs'⟩ := VIRL5.RegionAt.world hreg
  exact ⟨a, hterm, hav, hw', hs'⟩

end VIRL5
