/-
  O95 layer L5, Lean arm (STATUS 318, LV8 Deflate5; LV8-MAP: BUILD phase ZERO → fillR, 16 ≤ C). DEFLATE's BUILD clears count[j]
  ONE cell per step (Step.lean `bZeroN`, `build_zero_cell`) for j < 16, then moves to phase 1 (`build_zero_end`). The L5 ZERO branch
  clears ALL remaining counts [tbb + j, tbb + 16) in ONE fillR call and sets INDEX := 16, so the next step is DEFLATE's own end
  branch, unchanged (PHASE := 1, INDEX := 0). BUILD's other phases stay lifted. This file holds the ZERO branch over the world (the
  phase test belongs to the BUILD wrapper of the Deflate5 assembly): triples, cost, run, and DEFLATE's World form.
-/
import VIRL5.Rep5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- BUILD phase ZERO over ⟶₅, with the world at #0. -/
def zeroT₅ : Tm₅ :=
  .letOp .load [.var 0, .const (.int cINDEX)] t5int                                 -- j w
  (.ite (.prim .lt [.var 0, .const (.int 16)])
    (.letOp .load [.var 1, .const (.int cX)] t5int                                  -- x j w
      (.letOp .load [.var 2, .prim .add [.var 0, .const (.int 7)]] t5int            -- t x j w
        (.letK t5unit 1                                                             -- w1 u t x j w
          (.appK fillR (.pair (.prim .add [.var 0, .var 2])
            (.pair (.prim .sub [.const (.int 16), .var 2]) (.const (.int 0)))) [.var 3])
          (.letOp .store [.var 0, .const (.int cINDEX), .const (.int 16)] t5cap (.ret (.var 0))))))
    (.letOp .store [.var 1, .const (.int cPHASE), .const (.int 1)] t5cap            -- w1 j w
      (.letOp .store [.var 0, .const (.int cINDEX), .const (.int 0)] t5cap (.ret (.var 0)))))

/-- The contents after the ZERO chunk: counts [tbb + j, tbb + 16) cleared, INDEX := 16. -/
def zeroPost (p : Int) (g : Int → Int) (j tbb : Int) : Int → Int :=
  Function.update (fillF g p (tbb + j) (16 - j).toNat 0) (p + cINDEX) 16

/-- **ZERO, the chunk (j < 16).** -/
theorem zero5_chunk (p : Int) (L : Nat) (g : Int → Int) (j X tbb : Int)
    (hj : g (p + cINDEX) = j) (hj0 : 0 ≤ j) (hj16 : j < 16) (hX : g (p + cX) = X) (ht : g (p + (X + 7)) = tbb)
    (hX0 : 0 ≤ X) (hXL : X + 8 < L) (ht0 : 0 ≤ tbb) (htL : tbb + 16 ≤ L) (hL : 2080 ≤ L) :
    Triple₅ (RegionAt p L g) (zeroT₅.subst 0 (.const (.cap p)))
      (fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (zeroPost p g j tbb) σ) := by
  have hlT : ((16 - j).toNat : Int) = 16 - j := Int.toNat_of_nonneg (by omega)
  simp [zeroT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int cINDEX]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cINDEX ⟨by unfold cINDEX; omega, by unfold cINDEX; omega⟩) (fun w => ?_)
  show Triple₅ (fun σ => w = .const (.int (g (p + cINDEX))) ∧ RegionAt p L g σ) _ _
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hj]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine ite_rule₅ (b := true) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
  simp only [if_true]
  refine letOp_rule₅ (cs := [.cap p, .int cX]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cX ⟨by unfold cX; omega, by unfold cX; omega⟩) (fun w => ?_)
  show Triple₅ (fun σ => w = .const (.int (g (p + cX))) ∧ RegionAt p L g σ) _ _
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hX]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (X + 7)])
    (by simp [Atom₅.evalL, Atom₅.eval, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L g (X + 7) ⟨by omega, by omega⟩) (fun w => ?_)
  show Triple₅ (fun σ => w = .const (.int (g (p + (X + 7)))) ∧ RegionAt p L g σ) _ _
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [ht]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  have ih := fillR_spec p L 0 (16 - j).toNat (tbb + j) g (by omega) (by rw [hlT]; omega)
  have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
  refine letK_rule₅ (Q := fun r qs σ => r = .const .unit ∧ qs = [.const (.cap p)] ∧
      RegionAt p L (fillF g p (tbb + j) (16 - j).toNat 0) σ)
    (appKFix_rule₅ rfl ?_ rfl rfl ih') (fun v qs σ h => by rw [h.2.1]; rfl) (fun v qs _ => ?_)
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, fillArg, hlT]
  refine pre_pure₅ (fun hv => ?_)
  subst hv
  refine pre_pure₅ (fun hq => ?_)
  subst hq
  simp [Tm₅.substAll, Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA]
  refine letOp_rule₅ (cs := [.cap p, .int cINDEX, .int 16]) (by simp [Atom₅.evalL, Atom₅.eval])
    (store_at p L _ cINDEX 16 ⟨by unfold cINDEX; omega, by unfold cINDEX; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => h)
    (ret_rule₅ (v := .const (.cap p))
      (Q := fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (zeroPost p g j tbb) σ) (by simp [Atom₅.eval]))

/-- **ZERO, the end (j ≥ 16):** PHASE := 1, INDEX := 0, as DEFLATE's `build_zero_end`. -/
theorem zero5_end (p : Int) (L : Nat) (g : Int → Int) (j : Int) (hj : g (p + cINDEX) = j) (hj16 : ¬ j < 16) (hL : 2080 ≤ L) :
    Triple₅ (RegionAt p L g) (zeroT₅.subst 0 (.const (.cap p)))
      (fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧
        RegionAt p L (Function.update (Function.update g (p + cPHASE) 1) (p + cINDEX) 0) σ) := by
  simp [zeroT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int cINDEX]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cINDEX ⟨by unfold cINDEX; omega, by unfold cINDEX; omega⟩) (fun w => ?_)
  show Triple₅ (fun σ => w = .const (.int (g (p + cINDEX))) ∧ RegionAt p L g σ) _ _
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hj]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine ite_rule₅ (b := false) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
  simp only [Bool.false_eq_true, if_false]
  refine letOp_rule₅ (cs := [.cap p, .int cPHASE, .int 1]) (by simp [Atom₅.evalL, Atom₅.eval])
    (store_at p L g cPHASE 1 ⟨by unfold cPHASE; omega, by unfold cPHASE; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int cINDEX, .int 0]) (by simp [Atom₅.evalL, Atom₅.eval])
    (store_at p L _ cINDEX 0 ⟨by unfold cINDEX; omega, by unfold cINDEX; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => h)
    (ret_rule₅ (v := .const (.cap p)) (Q := fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧
      RegionAt p L (Function.update (Function.update g (p + cPHASE) 1) (p + cINDEX) 0) σ) (by simp [Atom₅.eval]))

/-- **ZERO chunk cost:** 3·(16 − j) + 8 ⟶₅ steps (≤ 56). -/
theorem zero5_chunk_cost (p : Int) (L : Nat) (g : Int → Int) (j X tbb : Int)
    (hj : g (p + cINDEX) = j) (hj0 : 0 ≤ j) (hj16 : j < 16) (hX : g (p + cX) = X) (ht : g (p + (X + 7)) = tbb)
    (hX0 : 0 ≤ X) (hXL : X + 8 < L) (ht0 : 0 ≤ tbb) (htL : tbb + 16 ≤ L) (hL : 2080 ≤ L) :
    Cost₅ (RegionAt p L g) (zeroT₅.subst 0 (.const (.cap p))) (3 * (16 - j).toNat + 8) := by
  have hlT : ((16 - j).toNat : Int) = 16 - j := Int.toNat_of_nonneg (by omega)
  set l : Nat := (16 - j).toNat with hldef
  refine Cost₅.mono (n := (((((3 * l + 1) + 1) + 1 + ((0 + 1))) + 1) + 1) + 1 + 1) ?_ (by omega)
  simp [zeroT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int cINDEX]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cINDEX ⟨by unfold cINDEX; omega, by unfold cINDEX; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + cINDEX))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hj]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_ite₅ (b := true) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
  simp only [if_true]
  refine cost_letOp₅ (cs := [.cap p, .int cX]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cX ⟨by unfold cX; omega, by unfold cX; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + cX))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hX]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (X + 7)])
    (by simp [Atom₅.evalL, Atom₅.eval, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L g (X + 7) ⟨by omega, by omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + (X + 7)))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [ht]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  have ih := fillR_spec p L 0 l (tbb + j) g (by omega) (by rw [hlT]; omega)
  have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
  have ic := fillR_cost p L 0 l (tbb + j) g (by omega) (by rw [hlT]; omega)
  have ic' := cost_pure_step_rev₅ (n := 3 * l + 1) (fun σ => Step₅.appKFix rfl rfl rfl rfl) ic
  refine cost_letK₅ (n₁ := (3 * l + 1) + 1) (n₂ := 0 + 1)
    (Q := fun r qs σ => r = .const .unit ∧ qs = [.const (.cap p)] ∧ RegionAt p L (fillF g p (tbb + j) l 0) σ)
    ?h1 ?c1 (fun v qs σ h => by simp [h.2.1]) (fun v qs _ => ?_)
  case h1 =>
    refine appKFix_rule₅ rfl ?_ rfl rfl ih'
    simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, fillArg, hlT]
  case c1 =>
    refine cost_appKFix₅ rfl ?_ rfl rfl ic'
    simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, fillArg, hlT]
  refine cost_pre_pure₅ (fun hv => ?_)
  subst hv
  refine cost_pre_pure₅ (fun hq => ?_)
  subst hq
  simp [Tm₅.substAll, Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA]
  refine cost_letOp₅ (cs := [.cap p, .int cINDEX, .int 16]) (by simp [Atom₅.evalL, Atom₅.eval])
    (store_at p L _ cINDEX 16 ⟨by unfold cINDEX; omega, by unfold cINDEX; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact cost_ret₅ _ _

theorem zero5_chunk_run (p : Int) (L : Nat) (g : Int → Int) (j X tbb : Int)
    (hj : g (p + cINDEX) = j) (hj0 : 0 ≤ j) (hj16 : j < 16) (hX : g (p + cX) = X) (ht : g (p + (X + 7)) = tbb)
    (hX0 : 0 ≤ X) (hXL : X + 8 < L) (ht0 : 0 ≤ tbb) (htL : tbb + 16 ≤ L) (hL : 2080 ≤ L)
    {σ : Store} (hR : RegionAt p L g σ) (hwf : Store.WF σ) {F : Nat} (hF : 3 * (16 - j).toNat + 8 ≤ F) :
    ∃ a, ((run₅ F (zeroT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
          (run₅ F (zeroT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧
      a.eval = some (.const (.cap p)) ∧
      RegionAt p L (zeroPost p g j tbb) (run₅ F (zeroT₅.subst 0 (.const (.cap p)), σ)).2 := by
  obtain ⟨v, qs, ⟨hv, hqs, hreg⟩, hcase⟩ :=
    run_of_triple₅ (zero5_chunk p L g j X tbb hj hj0 hj16 hX ht hX0 hXL ht0 htL hL)
      (zero5_chunk_cost p L g j X tbb hj hj0 hj16 hX ht hX0 hXL ht0 htL hL) hR hwf hF
  subst hv
  subst hqs
  rcases hcase with ⟨a, ha, hav, -⟩ | ⟨a, ds', ha, hav, hds'⟩
  · exact ⟨a, Or.inl ha, hav, hreg⟩
  · have hl := evalL_length hds'
    have hd : ds' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst hd
    exact ⟨a, Or.inr ha, hav, hreg⟩

/-- The contents after the ZERO chunk, relative to the base (DEFLATE's World form). -/
def zeroPostRel (p : Int) (f : Int → Int) (j tbb : Int) : Int → Int :=
  fun i => zeroPost p (fun a => f (a - p)) j tbb (p + i)

theorem zero5_chunk_world (p : Int) (L : Nat) (f : Int → Int) (j X tbb : Int)
    (hj : f cINDEX = j) (hj0 : 0 ≤ j) (hj16 : j < 16) (hX : f cX = X) (ht : f (X + 7) = tbb)
    (hX0 : 0 ≤ X) (hXL : X + 8 < L) (ht0 : 0 ≤ tbb) (htL : tbb + 16 ≤ L) (hL : 2080 ≤ L)
    {σ : Store} (hw : World σ p L f) (hs : Sole σ p L) (hwf : Store.WF σ) {F : Nat} (hF : 3 * (16 - j).toNat + 8 ≤ F) :
    ∃ a, ((run₅ F (zeroT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
          (run₅ F (zeroT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧
      a.eval = some (.const (.cap p)) ∧
      World (run₅ F (zeroT₅.subst 0 (.const (.cap p)), σ)).2 p L (zeroPostRel p f j tbb) ∧
      Sole (run₅ F (zeroT₅.subst 0 (.const (.cap p)), σ)).2 p L := by
  have hR := VIRL5.World.regionAt hw hs
  obtain ⟨a, hterm, hav, hreg⟩ := zero5_chunk_run p L (fun a => f (a - p)) j X tbb
    (by simpa using hj) hj0 hj16 (by simpa using hX) (by simpa using ht) hX0 hXL ht0 htL hL hR hwf hF
  obtain ⟨hw', hs'⟩ := VIRL5.RegionAt.world hreg
  exact ⟨a, hterm, hav, hw', hs'⟩

end VIRL5
