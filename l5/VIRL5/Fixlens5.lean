/-
  O95 layer L5, Lean arm (STATUS 318, LV8 Deflate5; LV8-MAP: FIXLENS → fillR, C = 32). DEFLATE's FIXLENS writes ONE fixed code
  length per step (Step.lean `fixlensN`, S5's lengths: 8 below 144, 9 below 256, 7 below 280, 8 below 288, 5 to 318). The L5 mode
  writes a CHUNK per step through `fillR`: the run's value x and its boundary b by two 5-way chains, c = min(b − i, 32) cells (so a
  chunk never crosses a run), then FILL advanced by c. The i ≥ 318 branch is DEFLATE's own, store for store. `chain5_rule` is the
  5-way chain once. The triples are over RegionAt, with no premise on the contents (LV7).
-/
import VIRL5.Zero5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- A 5-way chain on a constant: the first threshold above i picks its value. -/
def chain5 (i t1 t2 t3 t4 v1 v2 v3 v4 v5 : Int) : Int :=
  if i < t1 then v1 else if i < t2 then v2 else if i < t3 then v3 else if i < t4 then v4 else v5

/-- The chain as a ⟶₅ term on a constant. -/
def chain5T (a : Atom₅) (t1 t2 t3 t4 v1 v2 v3 v4 v5 : Int) : Tm₅ :=
  .ite (.prim .lt [a, .const (.int t1)]) (.ret (.const (.int v1)))
    (.ite (.prim .lt [a, .const (.int t2)]) (.ret (.const (.int v2)))
      (.ite (.prim .lt [a, .const (.int t3)]) (.ret (.const (.int v3)))
        (.ite (.prim .lt [a, .const (.int t4)]) (.ret (.const (.int v4))) (.ret (.const (.int v5))))))

theorem chain5_rule (P : Assn) (i t1 t2 t3 t4 v1 v2 v3 v4 v5 : Int) :
    Triple₅ P (chain5T (.const (.int i)) t1 t2 t3 t4 v1 v2 v3 v4 v5)
      (fun r qs σ => r = .const (.int (chain5 i t1 t2 t3 t4 v1 v2 v3 v4 v5)) ∧ qs = [] ∧ P σ) := by
  unfold chain5T chain5
  have fin : ∀ v : Int, ∀ w : Int, w = v → Triple₅ P (.ret (.const (.int v)))
      (fun r qs σ => r = .const (.int w) ∧ qs = [] ∧ P σ) := fun v w hw =>
    conseq₅ (fun σ h => ⟨by rw [hw], rfl, h⟩) (fun r qs σ h => h)
      (ret_rule₅ (v := .const (.int v)) (Q := fun r qs σ => r = .const (.int w) ∧ qs = [] ∧ P σ) (by simp [Atom₅.eval]))
  by_cases h1 : i < t1
  · refine ite_rule₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_
    exact fin v1 _ (by simp [h1])
  refine ite_rule₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_
  by_cases h2 : i < t2
  · refine ite_rule₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_
    exact fin v2 _ (by simp [h1, h2])
  refine ite_rule₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_
  by_cases h3 : i < t3
  · refine ite_rule₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_
    exact fin v3 _ (by simp [h1, h2, h3])
  refine ite_rule₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_
  by_cases h4 : i < t4
  · refine ite_rule₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_
    exact fin v4 _ (by simp [h1, h2, h3, h4])
  refine ite_rule₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_
  exact fin v5 _ (by simp [h1, h2, h3, h4])

/-- S5's fixed length at i, and the end of its run. -/
def fixLenV (i : Int) : Int := chain5 i 144 256 280 288 8 9 7 8 5
def fixBndV (i : Int) : Int := chain5 i 144 256 280 288 144 256 280 288 318

/-- FIXLENS over ⟶₅, with the world at #0. -/
def fixlensT₅ : Tm₅ :=
  .letOp .load [.var 0, .const (.int cFILL)] t5int                                  -- i w
  (.letOp .load [.var 1, .const (.int cN)] t5int                                    -- n i w
    (.letOp .load [.var 2, .const (.int cOUTMAX)] t5int                             -- om n i w
      (.ite (.prim .lt [.var 2, .const (.int 318)])
        (.letE t5int (chain5T (.var 2) 144 256 280 288 8 9 7 8 5)                   -- x om n i w
          (.letE t5int (chain5T (.var 3) 144 256 280 288 144 256 280 288 318)       -- b x om n i w
            (.letE t5int (.ite (.prim .lt [.prim .sub [.var 0, .var 4], .const (.int CS)])
                (.ret (.prim .sub [.var 0, .var 4])) (.ret (.const (.int CS))))      -- c b x om n i w
              (.letK t5unit 1                                                       -- w1 u c b x om n i w
                (.appK fillR (.pair (.prim .add [.prim .add [.prim .add [.const (.int IN), .var 4], .var 3], .var 5])
                  (.pair (.var 0) (.var 2))) [.var 6])
                (.letOp .store [.var 0, .const (.int cFILL), .prim .add [.var 7, .var 2]] t5cap (.ret (.var 0)))))))
        (.letOp .load [.var 3, .const (.int cLIT)] t5int                            -- lit om n i w
          (.letOp .load [.var 4, .const (.int cX)] t5int                            -- X lit om n i w
            (.letOp .store [.var 5, .prim .add [.var 0, .const (.int 5)],
                .prim .add [.prim .add [.const (.int IN), .var 3], .var 2]] t5cap   -- s1 X lit om n i w
              (.letOp .store [.var 0, .prim .add [.var 1, .const (.int 6)], .const (.int 288)] t5cap     -- s2 s1 X …
                (.letOp .store [.var 0, .prim .add [.var 2, .const (.int 7)],
                    .prim .add [.prim .add [.prim .add [.const (.int IN), .var 5], .var 4], .const (.int 689)]] t5cap  -- s3 …
                  (.letOp .store [.var 0, .prim .add [.var 3, .const (.int 8)], .const (.int 0)] t5cap   -- s4 s3 s2 s1 X lit …
                    (.letOp .store [.var 0, .const (.int cHLIT), .const (.int 288)] t5cap                 -- w1 s4 … X lit
                      (.letOp .store [.var 0, .const (.int cHDIST), .const (.int 30)] t5cap               -- w2 w1 s4 s3 s2 s1 X lit
                        (.letOp .store [.var 0, .const (.int cCHK), .var 7] t5cap
                          (.letOp .store [.var 0, .const (.int cPHASE), .const (.int 0)] t5cap
                            (.letOp .store [.var 0, .const (.int cINDEX), .const (.int 0)] t5cap
                              (.letOp .store [.var 0, .const (.int cTGT), .const (.int 1)] t5cap
                                (.letOp .store [.var 0, .const (.int cDYN), .const (.int 0)] t5cap
                                  (.letOp .store [.var 0, .const (.int cMODE), .const (.int mBUILD)] t5cap
                                    (.ret (.var 0)))))))))))))))))))

/-- The contents after one FIXLENS chunk: S5's length written to c cells from IN + n + om + i, FILL := i + c. -/
def fixlensPost (p : Int) (g : Int → Int) (i n om : Int) : Int → Int :=
  Function.update (fillF g p (IN + n + om + i) (min (fixBndV i - i) CS).toNat (fixLenV i)) (p + cFILL)
    (i + min (fixBndV i - i) CS)

theorem fixBndV_gt (i : Int) (h : i < 318) : i < fixBndV i := by
  unfold fixBndV chain5; split_ifs <;> omega

theorem fixBndV_le (i : Int) : fixBndV i ≤ 318 := by
  unfold fixBndV chain5; split_ifs <;> omega

/-- **FIXLENS, one chunk (i < 318).** -/
theorem fixlens5_chunk (p : Int) (L : Nat) (g : Int → Int) (i n om : Int)
    (hi : g (p + cFILL) = i) (hi0 : 0 ≤ i) (hi318 : i < 318) (hn : g (p + cN) = n) (hom : g (p + cOUTMAX) = om)
    (hn0 : 0 ≤ n) (hom0 : 0 ≤ om) (hL : IN + n + om + 318 ≤ L) :
    Triple₅ (RegionAt p L g) (fixlensT₅.subst 0 (.const (.cap p)))
      (fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (fixlensPost p g i n om) σ) := by
  have hIN : (IN : Int) = 2080 := rfl
  have hb := fixBndV_gt i hi318
  have hb2 := fixBndV_le i
  have hc0 : 0 < min (fixBndV i - i) CS := by unfold CS; omega
  have hcT : ((min (fixBndV i - i) CS).toNat : Int) = min (fixBndV i - i) CS := Int.toNat_of_nonneg (by omega)
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
  refine ite_rule₅ (b := true) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
  simp only [if_true]
  -- x ← fixLenV i
  refine letE_rule₅ (Q := fun r qs σ => r = .const (.int (fixLenV i)) ∧ qs = [] ∧ RegionAt p L g σ) ?_
    (fun v qs σ h => h.2.1) (fun v => ?_)
  · simpa [chain5T, Tm₅.subst, Atom₅.subst, Atom₅.substL, fixLenV] using chain5_rule (RegionAt p L g) i 144 256 280 288 8 9 7 8 5
  refine pre_pure₅ (fun hv => ?_)
  subst hv
  refine pre_pure₅ (fun _ => ?_)
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- b ← fixBndV i
  refine letE_rule₅ (Q := fun r qs σ => r = .const (.int (fixBndV i)) ∧ qs = [] ∧ RegionAt p L g σ) ?_
    (fun v qs σ h => h.2.1) (fun v => ?_)
  · simpa [chain5T, Tm₅.subst, Atom₅.subst, Atom₅.substL, fixBndV] using
      chain5_rule (RegionAt p L g) i 144 256 280 288 144 256 280 288 318
  refine pre_pure₅ (fun hv => ?_)
  subst hv
  refine pre_pure₅ (fun _ => ?_)
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- c ← min (b − i) CS
  refine letE_rule₅ (Q := fun r qs σ => r = .const (.int (min (fixBndV i - i) CS)) ∧ qs = [] ∧ RegionAt p L g σ) ?_
    (fun v qs σ h => h.2.1) (fun v => ?_)
  · by_cases hlt : fixBndV i - i < CS
    · refine ite_rule₅ (b := true) ?_ ?_
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
      simp only [if_true]
      exact conseq₅ (fun σ h => ⟨by rw [min_eq_left (le_of_lt hlt)], rfl, h⟩) (fun r qs σ h => h)
        (ret_rule₅ (v := .const (.int (fixBndV i - i)))
          (Q := fun r qs σ => r = .const (.int (min (fixBndV i - i) CS)) ∧ qs = [] ∧ RegionAt p L g σ)
          (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]))
    · refine ite_rule₅ (b := false) ?_ ?_
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
      simp only [Bool.false_eq_true, if_false]
      exact conseq₅ (fun σ h => ⟨by rw [min_eq_right (by omega)], rfl, h⟩) (fun r qs σ h => h)
        (ret_rule₅ (v := .const (.int CS))
          (Q := fun r qs σ => r = .const (.int (min (fixBndV i - i) CS)) ∧ qs = [] ∧ RegionAt p L g σ)
          (by simp [Atom₅.eval]))
  refine pre_pure₅ (fun hv => ?_)
  subst hv
  refine pre_pure₅ (fun _ => ?_)
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  set c : Int := min (fixBndV i - i) CS with hcdef
  have ih := fillR_spec p L (fixLenV i) c.toNat (IN + n + om + i) g (by rw [hIN]; omega) (by rw [hcT]; omega)
  have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
  refine letK_rule₅ (Q := fun r qs σ => r = .const .unit ∧ qs = [.const (.cap p)] ∧
      RegionAt p L (fillF g p (IN + n + om + i) c.toNat (fixLenV i)) σ)
    ?h1 (fun v qs σ h => by simp [h.2.1]) (fun v qs _ => ?_)
  case h1 =>
    refine appKFix_rule₅ rfl ?_ rfl rfl ih'
    simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, fillArg, hcT]
  refine pre_pure₅ (fun hv => ?_)
  subst hv
  refine pre_pure₅ (fun hq => ?_)
  subst hq
  simp [Tm₅.substAll, Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA]
  refine letOp_rule₅ (cs := [.cap p, .int (cFILL), .int (i + c)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ (cFILL) (i + c) ⟨by unfold cFILL; omega, by unfold cFILL; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => h)
    (ret_rule₅ (v := .const (.cap p))
      (Q := fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (fixlensPost p g i n om) σ) (by simp [Atom₅.eval]))

end VIRL5
