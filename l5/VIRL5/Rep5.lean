/-
  O95 layer L5, Lean arm (STATUS 318, LV8 Deflate5 + Fit5; LV8-MAP: REP → fillR, C = 32). DEFLATE's REP writes ONE repeated code
  length per step (Step.lean `repN`). The L5 mode writes a CHUNK of c = min(pd, 32) copies of LAST per step through the library
  routine `fillR`, then advances FILL and PEND by c; the pending-0 branch is DEFLATE's own (MODE := LENS). In one file, as for
  SCOPY and COPY: the triples (no content premise, LV7), the cost 3·c + 13 (≤ 109, against 483), the run, and DEFLATE's World form.
-/
import VIRL5.CopyRun5
import VIRL5.Fill

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- fillR is closed: substitution leaves it as it is. -/
@[simp] theorem fillR_subst (i : Nat) (v : Atom₅) : fillR.subst i v = fillR := by
  simp [fillR, fillBody, Atom₅.subst, Tm₅.subst, Atom₅.substL]

/-- REP over ⟶₅, with the world at #0. -/
def repT₅ : Tm₅ :=
  .letOp .load [.var 0, .const (.int cPEND)] t5int                                  -- pd w
  (.ite (.prim .eq [.var 0, .const (.int 0)])
    (.letOp .store [.var 1, .const (.int cMODE), .const (.int mLENS)] t5cap (.ret (.var 0)))
    (.letOp .load [.var 1, .const (.int cFILL)] t5int                               -- fl pd w
      (.letOp .load [.var 2, .const (.int cLAST)] t5int                             -- la fl pd w
        (.letOp .load [.var 3, .const (.int cN)] t5int                              -- n la fl pd w
          (.letOp .load [.var 4, .const (.int cOUTMAX)] t5int                       -- om n la fl pd w
            (.letE t5int (.ite (.prim .lt [.var 4, .const (.int CS)]) (.ret (.var 4)) (.ret (.const (.int CS))))  -- c om n la fl pd w
              (.letK t5unit 1                                                       -- w1 u c om n la fl pd w
                (.appK fillR
                  (.pair (.prim .add [.prim .add [.prim .add [.const (.int IN), .var 2], .var 1], .var 4])
                    (.pair (.var 0) (.var 3)))
                  [.var 6])
                (.letOp .store [.var 0, .const (.int cFILL), .prim .add [.var 6, .var 2]] t5cap   -- w2 w1 u c om n la fl pd w
                  (.letOp .store [.var 0, .const (.int cPEND), .prim .sub [.var 8, .var 3]] t5cap -- w3 …
                    (.ret (.var 0)))))))))))

/-- The contents after one chunk: LAST written to c cells from IN + n + om + fl, then FILL and PEND advanced by c. -/
def repPost (p : Int) (g : Int → Int) (pd fl la n om : Int) : Int → Int :=
  Function.update (Function.update
    (fillF g p (IN + n + om + fl) (min pd CS).toNat la) (p + cFILL) (fl + min pd CS)) (p + cPEND) (pd - min pd CS)

/-- **REP, one chunk (pd ≠ 0).** -/
theorem rep5_chunk (p : Int) (L : Nat) (g : Int → Int) (pd fl la n om : Int)
    (hpd : g (p + cPEND) = pd) (hpd0 : 0 < pd) (hfl : g (p + cFILL) = fl) (hla : g (p + cLAST) = la)
    (hn : g (p + cN) = n) (hom : g (p + cOUTMAX) = om)
    (hfl0 : 0 ≤ fl) (hn0 : 0 ≤ n) (hom0 : 0 ≤ om) (hL : IN + n + om + fl + min pd CS ≤ L) :
    Triple₅ (RegionAt p L g) (repT₅.subst 0 (.const (.cap p)))
      (fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (repPost p g pd fl la n om) σ) := by
  have hIN : (IN : Int) = 2080 := rfl
  have hc0 : 0 < min pd CS := by unfold CS; omega
  have hcT : ((min pd CS).toNat : Int) = min pd CS := Int.toNat_of_nonneg (by omega)
  simp [repT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int cPEND]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cPEND ⟨by unfold cPEND; omega, by unfold cPEND; omega⟩) (fun w => ?_)
  show Triple₅ (fun σ => w = .const (.int (g (p + cPEND))) ∧ RegionAt p L g σ) _ _
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hpd]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine ite_rule₅ (b := false) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
  simp only [Bool.false_eq_true, if_false]
  refine letOp_rule₅ (cs := [.cap p, .int cFILL]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cFILL ⟨by unfold cFILL; omega, by unfold cFILL; omega⟩) (fun w => ?_)
  show Triple₅ (fun σ => w = .const (.int (g (p + cFILL))) ∧ RegionAt p L g σ) _ _
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hfl]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int cLAST]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cLAST ⟨by unfold cLAST; omega, by unfold cLAST; omega⟩) (fun w => ?_)
  show Triple₅ (fun σ => w = .const (.int (g (p + cLAST))) ∧ RegionAt p L g σ) _ _
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hla]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int cN]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cN ⟨by unfold cN; omega, by unfold cN; omega⟩) (fun w => ?_)
  show Triple₅ (fun σ => w = .const (.int (g (p + cN))) ∧ RegionAt p L g σ) _ _
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hn]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int cOUTMAX]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cOUTMAX ⟨by unfold cOUTMAX; omega, by unfold cOUTMAX; omega⟩) (fun w => ?_)
  show Triple₅ (fun σ => w = .const (.int (g (p + cOUTMAX))) ∧ RegionAt p L g σ) _ _
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hom]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letE_rule₅ (Q := fun r qs σ => r = .const (.int (min pd CS)) ∧ qs = [] ∧ RegionAt p L g σ) ?_
    (fun v qs σ h => h.2.1) (fun v => ?_)
  · by_cases hlt : pd < CS
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
  refine pre_pure₅ (fun hv => ?_)
  subst hv
  refine pre_pure₅ (fun _ => ?_)
  simp [Tm₅.subst, Atom₅.subst, Atom₅.substL]
  set c : Int := min pd CS with hcdef
  have ih := fillR_spec p L la c.toNat (IN + n + om + fl) g (by rw [hIN]; omega) (by rw [hcT]; omega)
  have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
  refine letK_rule₅ (Q := fun r qs σ => r = .const .unit ∧ qs = [.const (.cap p)] ∧ RegionAt p L (fillF g p (IN + n + om + fl) c.toNat la) σ)
    (appKFix_rule₅ rfl ?_ rfl rfl ih') (fun v qs σ h => by rw [h.2.1]; rfl) (fun v qs _ => ?_)
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, fillArg, hcT]
  refine pre_pure₅ (fun hv => ?_)
  subst hv
  refine pre_pure₅ (fun hq => ?_)
  subst hq
  simp [Tm₅.substAll, Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA]
  refine letOp_rule₅ (cs := [.cap p, .int cFILL, .int (fl + c)])
    (by simp [Atom₅.evalL, Atom₅.eval, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ cFILL (fl + c) ⟨by unfold cFILL; omega, by unfold cFILL; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int cPEND, .int (pd - c)])
    (by simp [Atom₅.evalL, Atom₅.eval, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ cPEND (pd - c) ⟨by unfold cPEND; omega, by unfold cPEND; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => h)
    (ret_rule₅ (v := .const (.cap p))
      (Q := fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (repPost p g pd fl la n om) σ) (by simp [Atom₅.eval]))

/-- **REP, the run's end (pd = 0).** MODE := LENS; nothing else changes. -/
theorem rep5_end (p : Int) (L : Nat) (g : Int → Int) (hpd : g (p + cPEND) = 0) (hL : 6 ≤ L) :
    Triple₅ (RegionAt p L g) (repT₅.subst 0 (.const (.cap p)))
      (fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (Function.update g (p + cMODE) mLENS) σ) := by
  simp [repT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int cPEND]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cPEND ⟨by unfold cPEND; omega, by unfold cPEND; omega⟩) (fun w => ?_)
  show Triple₅ (fun σ => w = .const (.int (g (p + cPEND))) ∧ RegionAt p L g σ) _ _
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hpd]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine ite_rule₅ (b := true) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
  simp only [if_true]
  refine letOp_rule₅ (cs := [.cap p, .int cMODE, .int mLENS]) (by simp [Atom₅.evalL, Atom₅.eval])
    (store_at p L g cMODE mLENS ⟨by unfold cMODE; omega, by unfold cMODE; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => h)
    (ret_rule₅ (v := .const (.cap p)) (Q := fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧
      RegionAt p L (Function.update g (p + cMODE) mLENS) σ) (by simp [Atom₅.eval]))

theorem rep5_chunk_cost (p : Int) (L : Nat) (g : Int → Int) (pd fl la n om : Int)
    (hpd : g (p + cPEND) = pd) (hpd0 : 0 < pd) (hfl : g (p + cFILL) = fl) (hla : g (p + cLAST) = la)
    (hn : g (p + cN) = n) (hom : g (p + cOUTMAX) = om)
    (hfl0 : 0 ≤ fl) (hn0 : 0 ≤ n) (hom0 : 0 ≤ om) (hL : IN + n + om + fl + min pd CS ≤ L) :
    Cost₅ (RegionAt p L g) (repT₅.subst 0 (.const (.cap p))) (3 * (min pd CS).toNat + 13) := by
  have hIN : (IN : Int) = 2080 := rfl
  have hc0 : 0 < min pd CS := by unfold CS; omega
  have hcT : ((min pd CS).toNat : Int) = min pd CS := Int.toNat_of_nonneg (by omega)
  refine Cost₅.mono (n := (((((((0 + 1) + 1 + ((((3 * (min pd CS).toNat + 1) + 1) + 1 + ((0 + 1) + 1)))
    + 1) + 1) + 1) + 1) + 1) + 1)) ?_ (by omega)
  simp [repT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
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
  refine cost_letOp₅ (cs := [.cap p, .int cFILL]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cFILL ⟨by unfold cFILL; omega, by unfold cFILL; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + cFILL))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hfl]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int cLAST]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cLAST ⟨by unfold cLAST; omega, by unfold cLAST; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + cLAST))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hla]
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
  have hE : Triple₅ (RegionAt p L g) (.ite (.prim .lt [.const (.int pd), .const (.int CS)]) (.ret (.const (.int pd))) (.ret (.const (.int CS))))
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
  have cE : Cost₅ (RegionAt p L g) (.ite (.prim .lt [.const (.int pd), .const (.int CS)]) (.ret (.const (.int pd))) (.ret (.const (.int CS)))) (0 + 1) := by
    by_cases hlt : pd < CS
    · exact cost_ite₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) (cost_ret₅ _ _)
    · exact cost_ite₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) (cost_ret₅ _ _)
  refine cost_letE₅ (n₁ := 0 + 1) hE cE (fun v qs σ h => h.2.1) (fun v => ?_)
  refine cost_pre_pure₅ (fun hv => ?_)
  subst hv
  refine cost_pre_pure₅ (fun _ => ?_)
  simp [Tm₅.subst, Atom₅.subst, Atom₅.substL]
  set c : Int := min pd CS with hcdef
  have ih := fillR_spec p L la c.toNat (IN + n + om + fl) g (by rw [hIN]; omega) (by rw [hcT]; omega)
  have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
  have ic := fillR_cost p L la c.toNat (IN + n + om + fl) g (by rw [hIN]; omega) (by rw [hcT]; omega)
  have ic' := cost_pure_step_rev₅ (n := 3 * c.toNat + 1) (fun σ => Step₅.appKFix rfl rfl rfl rfl) ic
  refine cost_letK₅ (n₁ := (3 * c.toNat + 1) + 1) (Q := fun r qs σ => r = .const .unit ∧ qs = [.const (.cap p)] ∧ RegionAt p L (fillF g p (IN + n + om + fl) c.toNat la) σ)
    (appKFix_rule₅ rfl ?e1 rfl rfl ih') (cost_appKFix₅ rfl ?e2 rfl rfl ic')
    (fun v qs σ h => by rw [h.2.1]; rfl) (fun v qs _ => ?_)
  case e1 => simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, fillArg, hcT]
  case e2 => simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, fillArg, hcT]
  refine cost_pre_pure₅ (fun hv => ?_)
  subst hv
  refine cost_pre_pure₅ (fun hq => ?_)
  subst hq
  simp [Tm₅.substAll, Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA]
  refine cost_letOp₅ (cs := [.cap p, .int cFILL, .int (fl + c)])
    (by simp [Atom₅.evalL, Atom₅.eval, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ cFILL (fl + c) ⟨by unfold cFILL; omega, by unfold cFILL; omega⟩) (fun w => ?_)
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

theorem rep5_chunk_run (p : Int) (L : Nat) (g : Int → Int) (pd fl la n om : Int)
    (hpd : g (p + cPEND) = pd) (hpd0 : 0 < pd) (hfl : g (p + cFILL) = fl) (hla : g (p + cLAST) = la)
    (hn : g (p + cN) = n) (hom : g (p + cOUTMAX) = om)
    (hfl0 : 0 ≤ fl) (hn0 : 0 ≤ n) (hom0 : 0 ≤ om) (hL : IN + n + om + fl + min pd CS ≤ L)
    {σ : Store} (hR : RegionAt p L g σ) (hwf : Store.WF σ) {F : Nat} (hF : 3 * (min pd CS).toNat + 13 ≤ F) :
    ∃ a, (((run₅ F (repT₅.subst 0 (.const (.cap p)), σ)).1) = .ret a ∨ ((run₅ F (repT₅.subst 0 (.const (.cap p)), σ)).1) = .retK a []) ∧ a.eval = some (.const (.cap p)) ∧
      RegionAt p L (repPost p g pd fl la n om) ((run₅ F (repT₅.subst 0 (.const (.cap p)), σ)).2) := by
  obtain ⟨v, qs, ⟨hv, hqs, hreg⟩, hcase⟩ :=
    run_of_triple₅ (rep5_chunk p L g pd fl la n om hpd hpd0 hfl hla hn hom hfl0 hn0 hom0 hL) (rep5_chunk_cost p L g pd fl la n om hpd hpd0 hfl hla hn hom hfl0 hn0 hom0 hL) hR hwf hF
  subst hv
  subst hqs
  rcases hcase with ⟨a, ha, hav, -⟩ | ⟨a, ds', ha, hav, hds'⟩
  · exact ⟨a, Or.inl ha, hav, hreg⟩
  · have hl := evalL_length hds'
    have hd : ds' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst hd
    exact ⟨a, Or.inr ha, hav, hreg⟩

/-- The contents after one REP chunk, relative to the base (DEFLATE's World form). -/
def repPostRel (p : Int) (f : Int → Int) (pd fl la n om : Int) : Int → Int :=
  fun i => repPost p (fun a => f (a - p)) pd fl la n om (p + i)

theorem rep5_chunk_world (p : Int) (L : Nat) (f : Int → Int) (pd fl la n om : Int)
    (hpd : f cPEND = pd) (hpd0 : 0 < pd) (hfl : f cFILL = fl) (hla : f cLAST = la) (hn : f cN = n) (hom : f cOUTMAX = om)
    (hfl0 : 0 ≤ fl) (hn0 : 0 ≤ n) (hom0 : 0 ≤ om) (hL : IN + n + om + fl + min pd CS ≤ L)
    {σ : Store} (hw : World σ p L f) (hs : Sole σ p L) (hwf : Store.WF σ) {F : Nat} (hF : 3 * (min pd CS).toNat + 13 ≤ F) :
    ∃ a, (((run₅ F (repT₅.subst 0 (.const (.cap p)), σ)).1) = .ret a ∨ ((run₅ F (repT₅.subst 0 (.const (.cap p)), σ)).1) = .retK a []) ∧ a.eval = some (.const (.cap p)) ∧
      World ((run₅ F (repT₅.subst 0 (.const (.cap p)), σ)).2) p L (repPostRel p f pd fl la n om) ∧ Sole ((run₅ F (repT₅.subst 0 (.const (.cap p)), σ)).2) p L := by
  have hR := VIRL5.World.regionAt hw hs
  obtain ⟨a, hterm, hav, hreg⟩ := rep5_chunk_run p L (fun a => f (a - p)) pd fl la n om
    (by simpa using hpd) hpd0 (by simpa using hfl) (by simpa using hla) (by simpa using hn) (by simpa using hom)
    hfl0 hn0 hom0 hL hR hwf hF
  obtain ⟨hw', hs'⟩ := VIRL5.RegionAt.world hreg
  exact ⟨a, hterm, hav, hw', hs'⟩

end VIRL5
