/-
  O95 layer L5, Lean arm (STATUS 318, LV8 Deflate5; LV8-MAP: SCOPY → copyWithinR, C = 32). DEFLATE's SCOPY copies ONE input byte
  per step (Step.lean `scopyN`). The L5 mode copies a CHUNK of c = min(k, 32) bytes per step through the library routine
  `copyWithinR` (the one lent region), then advances BY, M and PEND by c. The pending-0 branch is DEFLATE's own, cell for cell.
  `scopy5_chunk` is the chunk step's triple over `RegionAt` (absolute contents), with no premise on the contents (LV7): the region
  comes back with the routine's `cwF` followed by the three counter stores. Bridge (i) (Bridge5.lean) moves it to DEFLATE's World.
-/
import VIRL5.CopyWithin
import VIRL5.Bridge5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- copyWithinR is closed: substitution leaves it as it is. -/
@[simp] theorem copyWithinR_subst (i : Nat) (v : Atom₅) : copyWithinR.subst i v = copyWithinR := by
  simp [copyWithinR, cwBody, Atom₅.subst, Tm₅.subst, Atom₅.substL]

/-- The chunk size. -/
def CS : Int := 32

/-- SCOPY over ⟶₅, with the world at #0. Scopes (innermost first) are given at each binder. -/
def scopyT₅ : Tm₅ :=
  .letOp .load [.var 0, .const (.int cPEND)] t5int                                  -- k w
  (.ite (.prim .eq [.var 0, .const (.int 0)])
    (.letOp .load [.var 1, .const (.int cBF)] t5int                                 -- bf k w
      (.ite (.prim .eq [.var 0, .const (.int 1)])
        (.letOp .store [.var 2, .const (.int cMODE), .const (.int mDONE)] t5cap (.ret (.var 0)))
        (.letOp .store [.var 2, .const (.int cMODE), .const (.int mHDR)] t5cap (.ret (.var 0)))))
    (.letOp .load [.var 1, .const (.int cBY)] t5int                                 -- by k w
      (.letOp .load [.var 2, .const (.int cN)] t5int                                -- n by k w
        (.letOp .load [.var 3, .const (.int cM)] t5int                              -- m n by k w
          (.letE t5int (.ite (.prim .lt [.var 3, .const (.int CS)]) (.ret (.var 3)) (.ret (.const (.int CS))))  -- c m n by k w
            (.letK t5unit 1                                                         -- w1 u c m n by k w
              (.appK copyWithinR
                (.pair (.prim .add [.const (.int IN), .var 3])
                  (.pair (.prim .add [.prim .add [.const (.int IN), .var 2], .var 1]) (.var 0)))
                [.var 5])
              (.letOp .store [.var 0, .const (.int cBY), .prim .add [.var 5, .var 2]] t5cap        -- w2 w1 u c m n by k w
                (.letOp .store [.var 0, .const (.int cM), .prim .add [.var 4, .var 3]] t5cap       -- w3 w2 w1 u c m n by k w
                  (.letOp .store [.var 0, .const (.int cPEND), .prim .sub [.var 8, .var 4]] t5cap  -- w4 …
                    (.ret (.var 0)))))))))))

/-- The contents after one chunk: the routine's forward copy, then BY, M and PEND advanced by c. -/
def scopyPost (p : Int) (g : Int → Int) (k bx n m : Int) : Int → Int :=
  Function.update (Function.update (Function.update
    (cwF p g (IN + bx) (IN + n + m) (min k CS).toNat) (p + cBY) (bx + min k CS)) (p + cM) (m + min k CS)) (p + cPEND)
    (k - min k CS)

/-- **SCOPY, one chunk (k ≠ 0).** From the exact region with ANY contents g, the mode returns the world and the region holds
  `scopyPost`. The only premises are the counters' values and the bounds that keep both copies inside the region. -/
theorem scopy5_chunk (p : Int) (L : Nat) (g : Int → Int) (k bx n m : Int)
    (hk : g (p + cPEND) = k) (hk0 : 0 < k) (hby : g (p + cBY) = bx) (hn : g (p + cN) = n) (hm : g (p + cM) = m)
    (hbx : 0 ≤ bx) (hm0 : 0 ≤ m) (hcap : bx + min k CS ≤ n) (hL : IN + n + m + min k CS ≤ L) :
    Triple₅ (RegionAt p L g) (scopyT₅.subst 0 (.const (.cap p)))
      (fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (scopyPost p g k bx n m) σ) := by
  have hIN : (IN : Int) = 2080 := rfl
  have hc0 : 0 < min k CS := by unfold CS; omega
  have hcT : ((min k CS).toNat : Int) = min k CS := Int.toNat_of_nonneg (by omega)
  simp [scopyT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- k ← PEND
  refine letOp_rule₅ (cs := [.cap p, .int cPEND]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cPEND ⟨by unfold cPEND; omega, by unfold cPEND; omega⟩) (fun w => ?_)
  show Triple₅ (fun σ => w = .const (.int (g (p + cPEND))) ∧ RegionAt p L g σ) _ _
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hk]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine ite_rule₅ (b := false) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
  simp only [Bool.false_eq_true, if_false]
  -- by ← BY
  refine letOp_rule₅ (cs := [.cap p, .int cBY]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cBY ⟨by unfold cBY; omega, by unfold cBY; omega⟩) (fun w => ?_)
  show Triple₅ (fun σ => w = .const (.int (g (p + cBY))) ∧ RegionAt p L g σ) _ _
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hby]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
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
  -- c ← min k CS
  refine letE_rule₅ (Q := fun r qs σ => r = .const (.int (min k CS)) ∧ qs = [] ∧ RegionAt p L g σ) ?_
    (fun v qs σ h => h.2.1) (fun v => ?_)
  · by_cases hlt : k < CS
    · refine ite_rule₅ (b := true) ?_ ?_
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
      simp only [if_true]
      exact conseq₅ (fun σ h => ⟨by rw [min_eq_left (le_of_lt hlt)], rfl, h⟩) (fun r qs σ h => h)
        (ret_rule₅ (v := .const (.int k)) (Q := fun r qs σ => r = .const (.int (min k CS)) ∧ qs = [] ∧ RegionAt p L g σ) (by simp [Atom₅.eval]))
    · refine ite_rule₅ (b := false) ?_ ?_
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
      simp only [Bool.false_eq_true, if_false]
      exact conseq₅ (fun σ h => ⟨by rw [min_eq_right (by omega)], rfl, h⟩) (fun r qs σ h => h)
        (ret_rule₅ (v := .const (.int CS)) (Q := fun r qs σ => r = .const (.int (min k CS)) ∧ qs = [] ∧ RegionAt p L g σ) (by simp [Atom₅.eval]))
  refine pre_pure₅ (fun hv => ?_)
  subst hv
  refine pre_pure₅ (fun _ => ?_)
  simp [Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- the call: copyWithinR (IN + bx, IN + n + m, c) lending ⟨p⟩
  set c : Int := min k CS with hcdef
  have ih := copyWithinR_spec p L c.toNat (IN + bx) (IN + n + m) g (by rw [hIN]; omega)
    (by rw [hcT]; omega) (by rw [hIN]; omega) (by rw [hcT]; omega)
  have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
  refine letK_rule₅ (Q := fun r qs σ => r = .const .unit ∧ qs = [.const (.cap p)] ∧
      RegionAt p L (cwF p g (IN + bx) (IN + n + m) c.toNat) σ)
    (appKFix_rule₅ rfl ?_ rfl rfl ih') (fun v qs σ h => by rw [h.2.1]; rfl) (fun v qs _ => ?_)
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, copyArg, hcT]
  refine pre_pure₅ (fun hv => ?_)
  subst hv
  refine pre_pure₅ (fun hq => ?_)
  subst hq
  simp [Tm₅.substAll, Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA]
  -- BY ← bx + c
  refine letOp_rule₅ (cs := [.cap p, .int cBY, .int (bx + c)])
    (by simp [Atom₅.evalL, Atom₅.eval, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ cBY (bx + c) ⟨by unfold cBY; omega, by unfold cBY; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- M ← m + c
  refine letOp_rule₅ (cs := [.cap p, .int cM, .int (m + c)])
    (by simp [Atom₅.evalL, Atom₅.eval, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ cM (m + c) ⟨by unfold cM; omega, by unfold cM; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- PEND ← k − c
  refine letOp_rule₅ (cs := [.cap p, .int cPEND, .int (k - c)])
    (by simp [Atom₅.evalL, Atom₅.eval, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ cPEND (k - c) ⟨by unfold cPEND; omega, by unfold cPEND; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => h)
    (ret_rule₅ (Q := fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (scopyPost p g k bx n m) σ)
      (by simp [Atom₅.eval]))

end VIRL5
