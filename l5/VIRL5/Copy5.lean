/-
  O95 layer L5, Lean arm (STATUS 318, LV8 Deflate5; LV8-MAP: COPY → copyWithinR, C = 32). DEFLATE's COPY copies ONE byte per step
  from distance DIST back in the output (Step.lean `copyN`), so a distance shorter than the length repeats (RFC 1951). The L5 mode
  copies a CHUNK of c = min(pd, 32) bytes per step through `copyWithinR`, whose contents `cwF` are exactly that forward copy, then
  advances M and PEND by c. The pending-0 branch is DEFLATE's own (MODE := SYM). `copy5_chunk` / `copy5_end` are the triples over
  RegionAt, with no premise on the contents (LV7).
-/
import VIRL5.Scopy5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- COPY over ⟶₅, with the world at #0. Scopes (innermost first) are given at each binder. -/
def copyT₅ : Tm₅ :=
  .letOp .load [.var 0, .const (.int cPEND)] t5int                                  -- pd w
  (.ite (.prim .eq [.var 0, .const (.int 0)])
    (.letOp .store [.var 1, .const (.int cMODE), .const (.int mSYM)] t5cap (.ret (.var 0)))
    (.letOp .load [.var 1, .const (.int cN)] t5int                                  -- n pd w
      (.letOp .load [.var 2, .const (.int cM)] t5int                                -- m n pd w
        (.letOp .load [.var 3, .const (.int cDIST)] t5int                           -- ds m n pd w
          (.letE t5int (.ite (.prim .lt [.var 3, .const (.int CS)]) (.ret (.var 3)) (.ret (.const (.int CS))))  -- c ds m n pd w
            (.letK t5unit 1                                                         -- w1 u c ds m n pd w
              (.appK copyWithinR
                (.pair (.prim .sub [.prim .add [.prim .add [.const (.int IN), .var 3], .var 2], .var 1])
                  (.pair (.prim .add [.prim .add [.const (.int IN), .var 3], .var 2]) (.var 0)))
                [.var 5])
              (.letOp .store [.var 0, .const (.int cM), .prim .add [.var 4, .var 2]] t5cap        -- w2 w1 u c ds m n pd w
                (.letOp .store [.var 0, .const (.int cPEND), .prim .sub [.var 7, .var 3]] t5cap   -- w3 …
                  (.ret (.var 0))))))))))

/-- The contents after one chunk: the routine's forward copy from distance ds, then M and PEND advanced by c. -/
def copyPost (p : Int) (g : Int → Int) (pd n m ds : Int) : Int → Int :=
  Function.update (Function.update
    (cwF p g (IN + n + m - ds) (IN + n + m) (min pd CS).toNat) (p + cM) (m + min pd CS)) (p + cPEND) (pd - min pd CS)

/-- **COPY, one chunk (pd ≠ 0).** From the exact region with ANY contents g, the mode returns the world and the region holds
  `copyPost`. The premises are the counters' values and the bounds that keep both ends of the copy inside the region. -/
theorem copy5_chunk (p : Int) (L : Nat) (g : Int → Int) (pd n m ds : Int)
    (hpd : g (p + cPEND) = pd) (hpd0 : 0 < pd) (hn : g (p + cN) = n) (hm : g (p + cM) = m) (hds : g (p + cDIST) = ds)
    (hn0 : 0 ≤ n) (hds1 : 0 ≤ ds) (hdsm : ds ≤ m) (hL : IN + n + m + min pd CS ≤ L) :
    Triple₅ (RegionAt p L g) (copyT₅.subst 0 (.const (.cap p)))
      (fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (copyPost p g pd n m ds) σ) := by
  have hIN : (IN : Int) = 2080 := rfl
  have hc0 : 0 < min pd CS := by unfold CS; omega
  have hcT : ((min pd CS).toNat : Int) = min pd CS := Int.toNat_of_nonneg (by omega)
  simp [copyT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- pd ← PEND
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
  -- n ← N
  refine letOp_rule₅ (cs := [.cap p, .int cN]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cN ⟨by unfold cN; omega, by unfold cN; omega⟩) (fun w => ?_)
  show Triple₅ (fun σ => w = .const (.int (g (p + cN))) ∧ RegionAt p L g σ) _ _
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hn]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- m ← M
  refine letOp_rule₅ (cs := [.cap p, .int cM]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cM ⟨by unfold cM; omega, by unfold cM; omega⟩) (fun w => ?_)
  show Triple₅ (fun σ => w = .const (.int (g (p + cM))) ∧ RegionAt p L g σ) _ _
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hm]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- ds ← DIST
  refine letOp_rule₅ (cs := [.cap p, .int cDIST]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cDIST ⟨by unfold cDIST; omega, by unfold cDIST; omega⟩) (fun w => ?_)
  show Triple₅ (fun σ => w = .const (.int (g (p + cDIST))) ∧ RegionAt p L g σ) _ _
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hds]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- c ← min pd CS
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
  -- the call: copyWithinR (IN + n + m − ds, IN + n + m, c) lending ⟨p⟩
  set c : Int := min pd CS with hcdef
  have ih := copyWithinR_spec p L c.toNat (IN + n + m - ds) (IN + n + m) g (by rw [hIN]; omega)
    (by rw [hcT]; omega) (by rw [hIN]; omega) (by rw [hcT]; omega)
  have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
  refine letK_rule₅ (Q := fun r qs σ => r = .const .unit ∧ qs = [.const (.cap p)] ∧
      RegionAt p L (cwF p g (IN + n + m - ds) (IN + n + m) c.toNat) σ)
    (appKFix_rule₅ rfl ?_ rfl rfl ih') (fun v qs σ h => by rw [h.2.1]; rfl) (fun v qs _ => ?_)
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, copyArg, hcT]
  refine pre_pure₅ (fun hv => ?_)
  subst hv
  refine pre_pure₅ (fun hq => ?_)
  subst hq
  simp [Tm₅.substAll, Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA]
  -- M ← m + c
  refine letOp_rule₅ (cs := [.cap p, .int cM, .int (m + c)])
    (by simp [Atom₅.evalL, Atom₅.eval, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ cM (m + c) ⟨by unfold cM; omega, by unfold cM; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- PEND ← pd − c
  refine letOp_rule₅ (cs := [.cap p, .int cPEND, .int (pd - c)])
    (by simp [Atom₅.evalL, Atom₅.eval, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ cPEND (pd - c) ⟨by unfold cPEND; omega, by unfold cPEND; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => h)
    (ret_rule₅ (v := .const (.cap p))
      (Q := fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (copyPost p g pd n m ds) σ) (by simp [Atom₅.eval]))

/-- **COPY, the run's end (pd = 0).** MODE := SYM; nothing else changes. -/
theorem copy5_end (p : Int) (L : Nat) (g : Int → Int) (hpd : g (p + cPEND) = 0) (hL : 6 ≤ L) :
    Triple₅ (RegionAt p L g) (copyT₅.subst 0 (.const (.cap p)))
      (fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (Function.update g (p + cMODE) mSYM) σ) := by
  simp [copyT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
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
  refine letOp_rule₅ (cs := [.cap p, .int cMODE, .int mSYM]) (by simp [Atom₅.evalL, Atom₅.eval])
    (store_at p L g cMODE mSYM ⟨by unfold cMODE; omega, by unfold cMODE; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => h)
    (ret_rule₅ (v := .const (.cap p)) (Q := fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧
      RegionAt p L (Function.update g (p + cMODE) mSYM) σ) (by simp [Atom₅.eval]))

end VIRL5
