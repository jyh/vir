/-
  O95 layer L5, Lean arm (STATUS 320, LV8 Deflate5; LV8-MAP: READ → bitR, C_bit = 1). DEFLATE's READ takes ONE bit per step from the
  TABLE: x = TABLE[8·v + bi] for the input byte v at IN + by (Step.lean `readN`). The L5 mode takes the same bit from the library
  routine `bitR` on the cursor (IN + by, bi, 1), which reads the byte itself and returns the advanced cursor; TABLE is filled as
  before and no longer read (Addendum 2). ACC, WT, K and the MODE := RET at K = 0 are DEFLATE's own; the by ≥ n branch is DEFLATE's
  TRUNC reject. The triples are over RegionAt, with no premise on the contents (LV7).
-/
import VIRL5.FixlensEnd5
import VIRL5.Bit

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- bitR is closed: substitution leaves it as it is. -/
@[simp] theorem bitR_subst (i : Nat) (v : Atom₅) : bitR.subst i v = bitR := by
  simp [bitR, bitBody, Atom₅.subst, Tm₅.subst, Atom₅.substL]

/-- READ over ⟶₅, with the world at #0. The bit comes from `bitR` on the cursor (IN + by, bi, 1); TABLE is not read. -/
def readT₅ : Tm₅ :=
  .letOp .load [.var 0, .const (.int cBY)] t5int                                    -- by w
  (.letOp .load [.var 1, .const (.int cBI)] t5int                                   -- bi by w
    (.letOp .load [.var 2, .const (.int cN)] t5int                                  -- n bi by w
      (.ite (.prim .lt [.var 2, .var 0])
        (.letK τbit 1                                                               -- w1 r n bi by w
          (.appK bitR (.pair (.prim .add [.const (.int IN), .var 2]) (.pair (.var 1) (.const (.int 1)))) [.var 3])
          (.letOp .load [.var 0, .const (.int cK)] t5int                            -- k w1 r n bi by w
            (.letOp .load [.var 1, .const (.int cACC)] t5int                        -- acc k w1 r …
              (.letOp .load [.var 2, .const (.int cWT)] t5int                       -- wt acc k w1 r …
                (.letOp .load [.var 3, .const (.int cRET)] t5int                    -- rt wt acc k w1 r …
                  (.letOp .store [.var 4, .const (.int cBY), .prim .sub [.fst (.snd (.var 5)), .const (.int IN)]] t5cap  -- w2 rt wt acc k w1 r
                    (.letOp .store [.var 0, .const (.int cBI), .snd (.snd (.var 6))] t5cap                      -- w3 w2 rt wt acc k w1 r
                      (.letOp .store [.var 0, .const (.int cACC),
                          .prim .add [.var 4, .prim .mul [.fst (.var 7), .var 3]]] t5cap                         -- w4 w3 w2 rt wt acc k w1 r
                        (.letOp .store [.var 0, .const (.int cWT), .prim .mul [.const (.int 2), .var 4]] t5cap  -- w5 w4 w3 w2 rt wt acc k
                          (.letOp .store [.var 0, .const (.int cK), .prim .sub [.var 7, .const (.int 1)]] t5cap -- w6 w5 w4 w3 w2 rt wt acc k
                            (.ite (.prim .eq [.prim .sub [.var 8, .const (.int 1)], .const (.int 0)])
                              (.letOp .store [.var 0, .const (.int cMODE), .var 5] t5cap (.ret (.var 0)))
                              (.ret (.var 0)))))))))))))
        (.letOp .store [.var 3, .const (.int cREASON), .const (.int rTRUNC)] t5cap
          (.letOp .store [.var 0, .const (.int cMODE), .const (.int mREJECT)] t5cap (.ret (.var 0)))))))

/-- The contents after one READ bit (by < n): the cursor advanced by bitR, ACC += bit · WT, WT doubled, K − 1, MODE := RET at 0. -/
def readPost (p : Int) (g : Int → Int) (bx bi k acc wt rt : Int) : Int → Int :=
  let g5 := Function.update (Function.update (Function.update (Function.update (Function.update g
    (p + cBY) (((8 * (IN + bx) + bi) + 1) / 8 - IN)) (p + cBI) (((8 * (IN + bx) + bi) + 1) % 8))
    (p + cACC) (acc + bitsF g p (8 * (IN + bx) + bi) 1 * wt)) (p + cWT) (2 * wt)) (p + cK) (k - 1)
  if k - 1 = 0 then Function.update g5 (p + cMODE) rt else g5

/-- **READ, one bit (by < n).** -/
theorem read5_bit (p : Int) (L : Nat) (g : Int → Int) (bx bi n k acc wt rt : Int)
    (hby : g (p + cBY) = bx) (hbi : g (p + cBI) = bi) (hn : g (p + cN) = n) (hk : g (p + cK) = k)
    (hacc : g (p + cACC) = acc) (hwt : g (p + cWT) = wt) (hrt : g (p + cRET) = rt)
    (hbx : 0 ≤ bx) (hlt : bx < n) (hbi0 : 0 ≤ bi) (hbi7 : bi ≤ 7) (hL : IN + n ≤ L) :
    Triple₅ (RegionAt p L g) (readT₅.subst 0 (.const (.cap p)))
      (fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (readPost p g bx bi k acc wt rt) σ) := by
  have hIN : (IN : Int) = 2080 := rfl
  simp [readT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cBY)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cBY) ⟨by unfold cBY; omega, by unfold cBY; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hby]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cBI)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cBI) ⟨by unfold cBI; omega, by unfold cBI; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hbi]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cN)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cN) ⟨by unfold cN; omega, by unfold cN; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hn]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine ite_rule₅ (b := true) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
  simp only [if_true]
  have ih := bitR_spec p L g 1 (IN + bx) bi 1 rfl (by rw [hIN]; omega) hbi0 hbi7 (by rw [hIN]; push_cast; omega)
  have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
  refine letK_rule₅ (Q := fun r qs σ => r = .pair (.const (.int (bitsF g p (8 * (IN + bx) + bi) 1))) (curA ((8 * (IN + bx) + bi) + 1)) ∧
      qs = [.const (.cap p)] ∧ RegionAt p L g σ)
    ?h1 (fun v qs σ h => by simp [h.2.1]) (fun v qs _ => ?_)
  case h1 =>
    refine appKFix_rule₅ rfl ?_ rfl rfl ih'
    simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
  refine pre_pure₅ (fun hv => ?_)
  subst hv
  refine pre_pure₅ (fun hq => ?_)
  subst hq
  simp [Tm₅.substAll, Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA, curA]
  refine letOp_rule₅ (cs := [.cap p, .int (cK)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cK) ⟨by unfold cK; omega, by unfold cK; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hk]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cACC)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cACC) ⟨by unfold cACC; omega, by unfold cACC; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hacc]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cWT)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cWT) ⟨by unfold cWT; omega, by unfold cWT; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hwt]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cRET)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cRET) ⟨by unfold cRET; omega, by unfold cRET; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hrt]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cBY), .int (((8 * (IN + bx) + bi) + 1) / 8 - IN)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
    (store_at p L _ (cBY) (((8 * (IN + bx) + bi) + 1) / 8 - IN) ⟨by unfold cBY; omega, by unfold cBY; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cBI), .int (((8 * (IN + bx) + bi) + 1) % 8)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
    (store_at p L _ (cBI) (((8 * (IN + bx) + bi) + 1) % 8) ⟨by unfold cBI; omega, by unfold cBI; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cACC), .int (acc + bitsF g p (8 * (IN + bx) + bi) 1 * wt)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
    (store_at p L _ (cACC) (acc + bitsF g p (8 * (IN + bx) + bi) 1 * wt) ⟨by unfold cACC; omega, by unfold cACC; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cWT), .int (2 * wt)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
    (store_at p L _ (cWT) (2 * wt) ⟨by unfold cWT; omega, by unfold cWT; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cK), .int (k - 1)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
    (store_at p L _ (cK) (k - 1) ⟨by unfold cK; omega, by unfold cK; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  by_cases hk1 : k - 1 = 0
  · refine ite_rule₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_
    simp only [if_true]
    refine letOp_rule₅ (cs := [.cap p, .int (cMODE), .int (rt)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
      (store_at p L _ (cMODE) (rt) ⟨by unfold cMODE; omega, by unfold cMODE; omega⟩) (fun w => ?_)
    refine pre_pure₅ (fun hw => ?_)
    subst hw
    simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
    exact conseq₅ (fun σ h => ⟨rfl, rfl, by simpa [readPost, hk1] using h⟩) (fun r qs σ h => h)
      (ret_rule₅ (v := .const (.cap p))
        (Q := fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (readPost p g bx bi k acc wt rt) σ)
        (by simp [Atom₅.eval]))
  · refine ite_rule₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_
    simp only [Bool.false_eq_true, if_false]
    exact conseq₅ (fun σ h => ⟨rfl, rfl, by simpa [readPost, hk1] using h⟩) (fun r qs σ h => h)
      (ret_rule₅ (v := .const (.cap p))
        (Q := fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (readPost p g bx bi k acc wt rt) σ)
        (by simp [Atom₅.eval]))

/-- **READ, the input exhausted (by ≥ n):** REASON := TRUNC, MODE := REJECT, as DEFLATE's own branch. -/
theorem read5_trunc (p : Int) (L : Nat) (g : Int → Int) (bx bi n : Int)
    (hby : g (p + cBY) = bx) (hbi : g (p + cBI) = bi) (hn : g (p + cN) = n) (hge : ¬ bx < n) (hL : 2080 ≤ L) :
    Triple₅ (RegionAt p L g) (readT₅.subst 0 (.const (.cap p)))
      (fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧
        RegionAt p L (Function.update (Function.update g (p + cREASON) rTRUNC) (p + cMODE) mREJECT) σ) := by
  simp [readT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cBY)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cBY) ⟨by unfold cBY; omega, by unfold cBY; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hby]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cBI)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cBI) ⟨by unfold cBI; omega, by unfold cBI; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hbi]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cN)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cN) ⟨by unfold cN; omega, by unfold cN; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hn]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine ite_rule₅ (b := false) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
  simp only [Bool.false_eq_true, if_false]
  refine letOp_rule₅ (cs := [.cap p, .int (cREASON), .int (rTRUNC)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
    (store_at p L _ (cREASON) (rTRUNC) ⟨by unfold cREASON; omega, by unfold cREASON; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cMODE), .int (mREJECT)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
    (store_at p L _ (cMODE) (mREJECT) ⟨by unfold cMODE; omega, by unfold cMODE; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => h)
    (ret_rule₅ (v := .const (.cap p)) (Q := fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧
      RegionAt p L (Function.update (Function.update g (p + cREASON) rTRUNC) (p + cMODE) mREJECT) σ) (by simp [Atom₅.eval]))

end VIRL5
