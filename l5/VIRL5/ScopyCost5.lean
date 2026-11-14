/-
  O95 layer L5, Lean arm (STATUS 318, LV8 Fit5 for SCOPY). The chunk step's COST: 4·c + 13 ⟶₅ steps for c = min(k, 32) bytes,
  i.e. at most 141, against KSTEP − 29 = 483 (the dispatch's share). Counted by the cost rules head by head, with the routine's
  own cost `copyWithinR_cost` (4·len + 2) moved onto the mode's call atom by one pure step each way.
-/
import VIRL5.Scopy5
import VIRL5.Costs

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

theorem scopy5_chunk_cost (p : Int) (L : Nat) (g : Int → Int) (k bx n m : Int)
    (hk : g (p + cPEND) = k) (hk0 : 0 < k) (hby : g (p + cBY) = bx) (hn : g (p + cN) = n) (hm : g (p + cM) = m)
    (hbx : 0 ≤ bx) (hm0 : 0 ≤ m) (hcap : bx + min k CS ≤ n) (hL : IN + n + m + min k CS ≤ L) :
    Cost₅ (RegionAt p L g) (scopyT₅.subst 0 (.const (.cap p))) (4 * (min k CS).toNat + 13) := by
  have hIN : (IN : Int) = 2080 := rfl
  have hc0 : 0 < min k CS := by unfold CS; omega
  have hcT : ((min k CS).toNat : Int) = min k CS := Int.toNat_of_nonneg (by omega)
  refine Cost₅.mono (n := ((((((0 + 1) + 1 + ((((4 * (min k CS).toNat + 1) + 1) + 1 + (((0 + 1) + 1) + 1)))
    + 1) + 1) + 1) + 1) + 1)) ?_ (by omega)
  simp [scopyT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- k ← PEND
  refine cost_letOp₅ (cs := [.cap p, .int cPEND]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cPEND ⟨by unfold cPEND; omega, by unfold cPEND; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + cPEND))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hk]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_ite₅ (b := false) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
  simp only [Bool.false_eq_true, if_false]
  -- by ← BY
  refine cost_letOp₅ (cs := [.cap p, .int cBY]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cBY ⟨by unfold cBY; omega, by unfold cBY; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + cBY))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hby]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- n ← N
  refine cost_letOp₅ (cs := [.cap p, .int cN]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cN ⟨by unfold cN; omega, by unfold cN; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + cN))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hn]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- m ← M
  refine cost_letOp₅ (cs := [.cap p, .int cM]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cM ⟨by unfold cM; omega, by unfold cM; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + cM))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hm]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- c ← min k CS: its triple (as in scopy5_chunk) and its cost 0 + 1
  have hE : Triple₅ (RegionAt p L g)
      (.ite (.prim .lt [.const (.int k), .const (.int CS)]) (.ret (.const (.int k))) (.ret (.const (.int CS))))
      (fun r qs σ => r = .const (.int (min k CS)) ∧ qs = [] ∧ RegionAt p L g σ) := by
    by_cases hlt : k < CS
    · refine ite_rule₅ (b := true) ?_ ?_
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
      simp only [if_true]
      exact conseq₅ (fun σ h => ⟨by rw [min_eq_left (le_of_lt hlt)], rfl, h⟩) (fun r qs σ h => h)
        (ret_rule₅ (v := .const (.int k)) (Q := fun r qs σ => r = .const (.int (min k CS)) ∧ qs = [] ∧ RegionAt p L g σ)
          (by simp [Atom₅.eval]))
    · refine ite_rule₅ (b := false) ?_ ?_
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
      simp only [Bool.false_eq_true, if_false]
      exact conseq₅ (fun σ h => ⟨by rw [min_eq_right (by omega)], rfl, h⟩) (fun r qs σ h => h)
        (ret_rule₅ (v := .const (.int CS)) (Q := fun r qs σ => r = .const (.int (min k CS)) ∧ qs = [] ∧ RegionAt p L g σ)
          (by simp [Atom₅.eval]))
  have cE : Cost₅ (RegionAt p L g)
      (.ite (.prim .lt [.const (.int k), .const (.int CS)]) (.ret (.const (.int k))) (.ret (.const (.int CS)))) (0 + 1) := by
    by_cases hlt : k < CS
    · exact cost_ite₅ (b := true)
        (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
        (cost_ret₅ _ _)
    · exact cost_ite₅ (b := false)
        (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
        (cost_ret₅ _ _)
  refine cost_letE₅ (n₁ := 0 + 1) hE cE (fun v qs σ h => h.2.1) (fun v => ?_)
  refine cost_pre_pure₅ (fun hv => ?_)
  subst hv
  refine cost_pre_pure₅ (fun _ => ?_)
  simp [Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- the call
  set c : Int := min k CS with hcdef
  have ih := copyWithinR_spec p L c.toNat (IN + bx) (IN + n + m) g (by rw [hIN]; omega)
    (by rw [hcT]; omega) (by rw [hIN]; omega) (by rw [hcT]; omega)
  have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
  have ic := copyWithinR_cost p L c.toNat (IN + bx) (IN + n + m) g (by rw [hIN]; omega)
    (by rw [hcT]; omega) (by rw [hIN]; omega) (by rw [hcT]; omega)
  have ic' := cost_pure_step_rev₅ (n := 4 * c.toNat + 1) (fun σ => Step₅.appKFix rfl rfl rfl rfl) ic
  refine cost_letK₅ (n₁ := (4 * c.toNat + 1) + 1)
    (Q := fun r qs σ => r = .const .unit ∧ qs = [.const (.cap p)] ∧
      RegionAt p L (cwF p g (IN + bx) (IN + n + m) c.toNat) σ)
    (appKFix_rule₅ rfl ?e1 rfl rfl ih') (cost_appKFix₅ rfl ?e2 rfl rfl ic')
    (fun v qs σ h => by rw [h.2.1]; rfl) (fun v qs _ => ?_)
  case e1 => simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, copyArg, hcT]
  case e2 => simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, copyArg, hcT]
  refine cost_pre_pure₅ (fun hv => ?_)
  subst hv
  refine cost_pre_pure₅ (fun hq => ?_)
  subst hq
  simp [Tm₅.substAll, Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA]
  refine cost_letOp₅ (cs := [.cap p, .int cBY, .int (bx + c)])
    (by simp [Atom₅.evalL, Atom₅.eval, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ cBY (bx + c) ⟨by unfold cBY; omega, by unfold cBY; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int cM, .int (m + c)])
    (by simp [Atom₅.evalL, Atom₅.eval, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ cM (m + c) ⟨by unfold cM; omega, by unfold cM; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int cPEND, .int (k - c)])
    (by simp [Atom₅.evalL, Atom₅.eval, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ cPEND (k - c) ⟨by unfold cPEND; omega, by unfold cPEND; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact cost_ret₅ _ _

end VIRL5
