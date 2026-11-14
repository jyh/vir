/-
  O95 layer L5, Lean arm (STATUS 318, LV8 Deflate5 + Fit5 for COPY). As for SCOPY (ScopyCost5, ScopyRun5, ScopyWorld5), in one
  file: the chunk step's COST, 4·c + 12 ⟶₅ steps for c = min(pd, 32) (≤ 140, against KSTEP − 29 = 483); its RUN at every fuel above
  that, by run_of_triple₅; and the same in DEFLATE's terms (World on a Sole store) through bridge (i).
-/
import VIRL5.Copy5
import VIRL5.ScopyWorld5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

theorem copy5_chunk_cost (p : Int) (L : Nat) (g : Int → Int) (pd n m ds : Int)
    (hpd : g (p + cPEND) = pd) (hpd0 : 0 < pd) (hn : g (p + cN) = n) (hm : g (p + cM) = m) (hds : g (p + cDIST) = ds)
    (hn0 : 0 ≤ n) (hds1 : 1 ≤ ds) (hdsm : ds ≤ m) (hL : IN + n + m + min pd CS ≤ L) :
    Cost₅ (RegionAt p L g) (copyT₅.subst 0 (.const (.cap p))) (4 * (min pd CS).toNat + 12) := by
  have hIN : (IN : Int) = 2080 := rfl
  have hc0 : 0 < min pd CS := by unfold CS; omega
  have hcT : ((min pd CS).toNat : Int) = min pd CS := Int.toNat_of_nonneg (by omega)
  refine Cost₅.mono (n := ((((((0 + 1) + 1 + ((((4 * (min pd CS).toNat + 1) + 1) + 1 + ((0 + 1) + 1)))
    + 1) + 1) + 1) + 1) + 1)) ?_ (by omega)
  simp [copyT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- pd ← PEND
  refine cost_letOp₅ (cs := [.cap p, .int cPEND]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cPEND ⟨by unfold cPEND; omega, by unfold cPEND; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + cPEND))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hpd]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_ite₅ (b := false) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
  simp only [Bool.false_eq_true, if_false]
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
  -- ds ← DIST
  refine cost_letOp₅ (cs := [.cap p, .int cDIST]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cDIST ⟨by unfold cDIST; omega, by unfold cDIST; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + cDIST))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hds]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- c ← min pd CS
  have hE : Triple₅ (RegionAt p L g)
      (.ite (.prim .lt [.const (.int pd), .const (.int CS)]) (.ret (.const (.int pd))) (.ret (.const (.int CS))))
      (fun r qs σ => r = .const (.int (min pd CS)) ∧ qs = [] ∧ RegionAt p L g σ) := by
    by_cases hlt : pd < CS
    · refine ite_rule₅ (b := true) ?_ ?_
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
      simp only [if_true]
      exact conseq₅ (fun σ h => ⟨by rw [min_eq_left (le_of_lt hlt)], rfl, h⟩) (fun r qs σ h => h)
        (ret_rule₅ (v := .const (.int pd)) (Q := fun r qs σ => r = .const (.int (min pd CS)) ∧ qs = [] ∧ RegionAt p L g σ)
          (by simp [Atom₅.eval]))
    · refine ite_rule₅ (b := false) ?_ ?_
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
      simp only [Bool.false_eq_true, if_false]
      exact conseq₅ (fun σ h => ⟨by rw [min_eq_right (by omega)], rfl, h⟩) (fun r qs σ h => h)
        (ret_rule₅ (v := .const (.int CS)) (Q := fun r qs σ => r = .const (.int (min pd CS)) ∧ qs = [] ∧ RegionAt p L g σ)
          (by simp [Atom₅.eval]))
  have cE : Cost₅ (RegionAt p L g)
      (.ite (.prim .lt [.const (.int pd), .const (.int CS)]) (.ret (.const (.int pd))) (.ret (.const (.int CS)))) (0 + 1) := by
    by_cases hlt : pd < CS
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
  set c : Int := min pd CS with hcdef
  have ih := copyWithinR_spec p L c.toNat (IN + n + m - ds) (IN + n + m) g (by rw [hIN]; omega)
    (by rw [hcT]; omega) (by rw [hIN]; omega) (by rw [hcT]; omega)
  have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
  have ic := copyWithinR_cost p L c.toNat (IN + n + m - ds) (IN + n + m) g (by rw [hIN]; omega)
    (by rw [hcT]; omega) (by rw [hIN]; omega) (by rw [hcT]; omega)
  have ic' := cost_pure_step_rev₅ (n := 4 * c.toNat + 1) (fun σ => Step₅.appKFix rfl rfl rfl rfl) ic
  refine cost_letK₅ (n₁ := (4 * c.toNat + 1) + 1)
    (Q := fun r qs σ => r = .const .unit ∧ qs = [.const (.cap p)] ∧
      RegionAt p L (cwF p g (IN + n + m - ds) (IN + n + m) c.toNat) σ)
    (appKFix_rule₅ rfl ?e1 rfl rfl ih') (cost_appKFix₅ rfl ?e2 rfl rfl ic')
    (fun v qs σ h => by rw [h.2.1]; rfl) (fun v qs _ => ?_)
  case e1 => simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, copyArg, hcT]
  case e2 => simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, copyArg, hcT]
  refine cost_pre_pure₅ (fun hv => ?_)
  subst hv
  refine cost_pre_pure₅ (fun hq => ?_)
  subst hq
  simp [Tm₅.substAll, Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA]
  refine cost_letOp₅ (cs := [.cap p, .int cM, .int (m + c)])
    (by simp [Atom₅.evalL, Atom₅.eval, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ cM (m + c) ⟨by unfold cM; omega, by unfold cM; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int cPEND, .int (pd - c)])
    (by simp [Atom₅.evalL, Atom₅.eval, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ cPEND (pd - c) ⟨by unfold cPEND; omega, by unfold cPEND; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact cost_ret₅ _ _

theorem copy5_chunk_run (p : Int) (L : Nat) (g : Int → Int) (pd n m ds : Int)
    (hpd : g (p + cPEND) = pd) (hpd0 : 0 < pd) (hn : g (p + cN) = n) (hm : g (p + cM) = m) (hds : g (p + cDIST) = ds)
    (hn0 : 0 ≤ n) (hds1 : 1 ≤ ds) (hdsm : ds ≤ m) (hL : IN + n + m + min pd CS ≤ L)
    {σ : Store} (hR : RegionAt p L g σ) (hwf : Store.WF σ) {F : Nat} (hF : 4 * (min pd CS).toNat + 12 ≤ F) :
    ∃ a, ((run₅ F (copyT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
          (run₅ F (copyT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧
      a.eval = some (.const (.cap p)) ∧
      RegionAt p L (copyPost p g pd n m ds) (run₅ F (copyT₅.subst 0 (.const (.cap p)), σ)).2 := by
  obtain ⟨v, qs, ⟨hv, hqs, hreg⟩, hcase⟩ :=
    run_of_triple₅ (copy5_chunk p L g pd n m ds hpd hpd0 hn hm hds hn0 hds1 hdsm hL)
      (copy5_chunk_cost p L g pd n m ds hpd hpd0 hn hm hds hn0 hds1 hdsm hL) hR hwf hF
  subst hv
  subst hqs
  rcases hcase with ⟨a, ha, hav, -⟩ | ⟨a, ds', ha, hav, hds'⟩
  · exact ⟨a, Or.inl ha, hav, hreg⟩
  · have hl := evalL_length hds'
    have hd : ds' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst hd
    exact ⟨a, Or.inr ha, hav, hreg⟩

/-- The contents after one COPY chunk, relative to the base (DEFLATE's World form). -/
def copyPostRel (p : Int) (f : Int → Int) (pd n m ds : Int) : Int → Int :=
  fun i => copyPost p (fun a => f (a - p)) pd n m ds (p + i)

theorem copy5_chunk_world (p : Int) (L : Nat) (f : Int → Int) (pd n m ds : Int)
    (hpd : f cPEND = pd) (hpd0 : 0 < pd) (hn : f cN = n) (hm : f cM = m) (hds : f cDIST = ds)
    (hn0 : 0 ≤ n) (hds1 : 1 ≤ ds) (hdsm : ds ≤ m) (hL : IN + n + m + min pd CS ≤ L)
    {σ : Store} (hw : World σ p L f) (hs : Sole σ p L) (hwf : Store.WF σ) {F : Nat} (hF : 4 * (min pd CS).toNat + 12 ≤ F) :
    ∃ a, ((run₅ F (copyT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
          (run₅ F (copyT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧
      a.eval = some (.const (.cap p)) ∧
      World (run₅ F (copyT₅.subst 0 (.const (.cap p)), σ)).2 p L (copyPostRel p f pd n m ds) ∧
      Sole (run₅ F (copyT₅.subst 0 (.const (.cap p)), σ)).2 p L := by
  have hR := VIRL5.World.regionAt hw hs
  obtain ⟨a, hterm, hav, hreg⟩ := copy5_chunk_run p L (fun a => f (a - p)) pd n m ds
    (by simpa using hpd) hpd0 (by simpa using hn) (by simpa using hm) (by simpa using hds)
    hn0 hds1 hdsm hL hR hwf hF
  obtain ⟨hw', hs'⟩ := VIRL5.RegionAt.world hreg
  exact ⟨a, hterm, hav, hw', hs'⟩

end VIRL5
