/-
  O95 layer L5, Lean arm (STATUS 320, LV8 Deflate5 + Fit5 for DECODE). As for READ (ReadRun5), in one file: each branch's COST in
  ⟶₅ steps (the bit: 5 loads, the test, bitR's 258·1 + 2 through the call, the letK, 6 loads, the hit test, and at most 2 loads +
  4 stores = 280, against KSTEP − 29 = 483; TRUNC: 8); its RUN at every fuel above that, by run_of_triple₅; and the same in
  DEFLATE's terms (World on a Sole store) through bridge (i).
-/
import VIRL5.Decode5
import VIRL5.ReadRun5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

set_option maxHeartbeats 4000000 in
theorem decode5_bit_cost (p : Int) (L : Nat) (g : Int → Int) (bx bi n om X l cv t rt tb fs c o sy : Int)
    (hby : g (p + cBY) = bx) (hbi : g (p + cBI) = bi) (hn : g (p + cN) = n) (hom : g (p + cOUTMAX) = om)
    (hX : g (p + cX) = X)
    (hbx : 0 ≤ bx) (hlt : bx < n) (hbi0 : 0 ≤ bi) (hbi7 : bi ≤ 7) (hL : IN + n ≤ L)
    (hX0 : 0 ≤ X) (hXL : X + 4 < L)
    (hl : g (p + X) = l) (hcv : g (p + (X + 1)) = cv) (ht : g (p + (X + 2)) = t) (hrt : g (p + (X + 3)) = rt)
    (htb : IN + n + om + 337 + 352 * t = tb) (ht0 : 0 ≤ tb) (htL : tb + 352 ≤ L) (hl1 : 1 ≤ l) (hl15 : l ≤ 15)
    (hfs : g (p + (tb + 16 + l)) = fs) (hc : g (p + (tb + l)) = c)
    (ho : fs ≤ 2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 ∧ 2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 < fs + c →
      g (p + (tb + 32 + l)) = o)
    (hsy0 : fs ≤ 2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 ∧ 2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 < fs + c →
      0 ≤ tb + 64 + o + (2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 - fs) ∧
        tb + 64 + o + (2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 - fs) < L)
    (hsy : fs ≤ 2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 ∧ 2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 < fs + c →
      g (p + (tb + 64 + o + (2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 - fs))) = sy) :
    Cost₅ (RegionAt p L g) (decodeT₅.subst 0 (.const (.cap p))) 280 := by
  have hIN : (IN : Int) = 2080 := rfl
  simp [decodeT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cBY)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cBY) ⟨by unfold cBY; omega, by unfold cBY; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hby]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cBI)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cBI) ⟨by unfold cBI; omega, by unfold cBI; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hbi]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cN)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cN) ⟨by unfold cN; omega, by unfold cN; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hn]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cOUTMAX)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cOUTMAX) ⟨by unfold cOUTMAX; omega, by unfold cOUTMAX; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hom]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cX)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cX) ⟨by unfold cX; omega, by unfold cX; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hX]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_ite₅ (b := true) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
  simp only [if_true]
  have ih := bitR_spec p L g 1 (IN + bx) bi 1 rfl (by rw [hIN]; omega) hbi0 hbi7 (by rw [hIN]; push_cast; omega)
  have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
  have ic := bitR_cost p L g 1 (IN + bx) bi 1 rfl (by rw [hIN]; omega) hbi0 hbi7 (by rw [hIN]; push_cast; omega)
  have ic' := cost_pure_step_rev₅ (n := 258 * 1 + 1) (fun σ => Step₅.appKFix rfl rfl rfl rfl) ic
  refine cost_letK₅ (n₁ := (258 * 1 + 1) + 1) (n₂ := 13)
    (Q := fun r qs σ => r = .pair (.const (.int (bitsF g p (8 * (IN + bx) + bi) 1))) (curA ((8 * (IN + bx) + bi) + 1)) ∧
      qs = [.const (.cap p)] ∧ RegionAt p L g σ)
    (appKFix_rule₅ rfl ?e1 rfl rfl ih') (cost_appKFix₅ rfl ?e2 rfl rfl ic')
    (fun v qs σ h => by simp [h.2.1]) (fun v qs _ => ?_)
  case e1 => simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
  case e2 => simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
  refine cost_pre_pure₅ (fun hv => ?_)
  subst hv
  refine cost_pre_pure₅ (fun hq => ?_)
  subst hq
  simp [Tm₅.substAll, Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA, curA]
  generalize hB : bitsF g p (8 * (IN + bx) + bi) 1 = B at ho hsy0 hsy ⊢
  -- ℓ, v, TGT, RET from the cursor-3 at X
  refine cost_letOp₅ (cs := [.cap p, .int X]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ X ⟨by omega, by omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hl]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (X + 1)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (X + 1) ⟨by omega, by omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hcv]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (X + 2)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (X + 2) ⟨by omega, by omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [ht]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (X + 3)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (X + 3) ⟨by omega, by omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hrt]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- first[ℓ] and count[ℓ] in TB(TGT)
  refine cost_letOp₅ (cs := [.cap p, .int (tb + 16 + l)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
    (load_at p L _ (tb + 16 + l) ⟨by omega, by omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hfs]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (tb + l)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
    (load_at p L _ (tb + l) ⟨by omega, by omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hc]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  by_cases hh : fs ≤ 2 * cv + B ∧ 2 * cv + B < fs + c
  · -- a hit: offs[ℓ], the symbol, the cursor, sym at X+4, MODE := RET
    obtain ⟨hy0, hyL⟩ := hsy0 hh
    have ho' := ho hh
    have hsy' := hsy hh
    obtain ⟨h1, h2⟩ := hh
    refine cost_ite₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, h1, h2]) ?_
    simp only [if_true]
    refine cost_letOp₅ (cs := [.cap p, .int (tb + 32 + l)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
      (load_at p L _ (tb + 32 + l) ⟨by omega, by omega⟩) (fun w => ?_)
    refine cost_pre_pure₅ (fun hw => ?_)
    subst hw
    rw [ho']
    simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
    refine cost_letOp₅ (cs := [.cap p, .int (tb + 64 + o + (2 * cv + B - fs))]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
      (load_at p L _ (tb + 64 + o + (2 * cv + B - fs)) ⟨hy0, hyL⟩) (fun w => ?_)
    refine cost_pre_pure₅ (fun hw => ?_)
    subst hw
    rw [hsy']
    simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
    refine cost_letOp₅ (cs := [.cap p, .int (cBY), .int (((8 * (IN + bx) + bi) + 1) / 8 - IN)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
      (store_at p L _ (cBY) (((8 * (IN + bx) + bi) + 1) / 8 - IN) ⟨by unfold cBY; omega, by unfold cBY; omega⟩) (fun w => ?_)
    refine cost_pre_pure₅ (fun hw => ?_)
    subst hw
    simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
    refine cost_letOp₅ (cs := [.cap p, .int (cBI), .int (((8 * (IN + bx) + bi) + 1) % 8)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
      (store_at p L _ (cBI) (((8 * (IN + bx) + bi) + 1) % 8) ⟨by unfold cBI; omega, by unfold cBI; omega⟩) (fun w => ?_)
    refine cost_pre_pure₅ (fun hw => ?_)
    subst hw
    simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
    refine cost_letOp₅ (cs := [.cap p, .int (X + 4), .int sy]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
      (store_at p L _ (X + 4) sy ⟨by omega, by omega⟩) (fun w => ?_)
    refine cost_pre_pure₅ (fun hw => ?_)
    subst hw
    simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
    refine cost_letOp₅ (cs := [.cap p, .int (cMODE), .int rt]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
      (store_at p L _ (cMODE) rt ⟨by unfold cMODE; omega, by unfold cMODE; omega⟩) (fun w => ?_)
    refine cost_pre_pure₅ (fun hw => ?_)
    subst hw
    simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
    exact cost_ret₅ _ _
  · refine cost_ite₅ (b := false) (by
      simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
      intro h1; by_contra h2; exact hh ⟨h1, by omega⟩) ?_
    simp only [Bool.false_eq_true, if_false]
    by_cases hl15' : l = 15
    · -- a miss at ℓ = 15: invalid code, the cursor unmoved
      refine Cost₅.mono (n := 3) ?_ (by omega)
      refine cost_ite₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, hl15']) ?_
      simp only [if_true]
      refine cost_letOp₅ (cs := [.cap p, .int (cREASON), .int rINVCODE]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
        (store_at p L _ (cREASON) rINVCODE ⟨by unfold cREASON; omega, by unfold cREASON; omega⟩) (fun w => ?_)
      refine cost_pre_pure₅ (fun hw => ?_)
      subst hw
      simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine cost_letOp₅ (cs := [.cap p, .int (cMODE), .int mREJECT]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
        (store_at p L _ (cMODE) mREJECT ⟨by unfold cMODE; omega, by unfold cMODE; omega⟩) (fun w => ?_)
      refine cost_pre_pure₅ (fun hw => ?_)
      subst hw
      simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      exact cost_ret₅ _ _
    · -- a miss below ℓ = 15: the cursor, ℓ + 1, v := v'
      refine Cost₅.mono (n := 5) ?_ (by omega)
      refine cost_ite₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, hl15']) ?_
      simp only [Bool.false_eq_true, if_false]
      refine cost_letOp₅ (cs := [.cap p, .int (cBY), .int (((8 * (IN + bx) + bi) + 1) / 8 - IN)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
        (store_at p L _ (cBY) (((8 * (IN + bx) + bi) + 1) / 8 - IN) ⟨by unfold cBY; omega, by unfold cBY; omega⟩) (fun w => ?_)
      refine cost_pre_pure₅ (fun hw => ?_)
      subst hw
      simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine cost_letOp₅ (cs := [.cap p, .int (cBI), .int (((8 * (IN + bx) + bi) + 1) % 8)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
        (store_at p L _ (cBI) (((8 * (IN + bx) + bi) + 1) % 8) ⟨by unfold cBI; omega, by unfold cBI; omega⟩) (fun w => ?_)
      refine cost_pre_pure₅ (fun hw => ?_)
      subst hw
      simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine cost_letOp₅ (cs := [.cap p, .int X, .int (l + 1)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
        (store_at p L _ X (l + 1) ⟨by omega, by omega⟩) (fun w => ?_)
      refine cost_pre_pure₅ (fun hw => ?_)
      subst hw
      simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine cost_letOp₅ (cs := [.cap p, .int (X + 1), .int (2 * cv + B)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
        (store_at p L _ (X + 1) (2 * cv + B) ⟨by omega, by omega⟩) (fun w => ?_)
      refine cost_pre_pure₅ (fun hw => ?_)
      subst hw
      simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      exact cost_ret₅ _ _

theorem decode5_trunc_cost (p : Int) (L : Nat) (g : Int → Int) (bx bi n : Int)
    (hby : g (p + cBY) = bx) (hbi : g (p + cBI) = bi) (hn : g (p + cN) = n) (hge : ¬ bx < n) (hL : 2080 ≤ L) :
    Cost₅ (RegionAt p L g) (decodeT₅.subst 0 (.const (.cap p))) 8 := by
  simp [decodeT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cBY)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cBY) ⟨by unfold cBY; omega, by unfold cBY; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hby]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cBI)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cBI) ⟨by unfold cBI; omega, by unfold cBI; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hbi]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cN)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cN) ⟨by unfold cN; omega, by unfold cN; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hn]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cOUTMAX)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cOUTMAX) ⟨by unfold cOUTMAX; omega, by unfold cOUTMAX; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cX)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cX) ⟨by unfold cX; omega, by unfold cX; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_ite₅ (b := false) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
  simp only [Bool.false_eq_true, if_false]
  refine cost_letOp₅ (cs := [.cap p, .int (cREASON), .int (rTRUNC)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
    (store_at p L _ (cREASON) (rTRUNC) ⟨by unfold cREASON; omega, by unfold cREASON; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cMODE), .int (mREJECT)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
    (store_at p L _ (cMODE) (mREJECT) ⟨by unfold cMODE; omega, by unfold cMODE; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact cost_ret₅ _ _

theorem decode5_bit_run (p : Int) (L : Nat) (g : Int → Int) (bx bi n om X l cv t rt tb fs c o sy : Int)
    (hby : g (p + cBY) = bx) (hbi : g (p + cBI) = bi) (hn : g (p + cN) = n) (hom : g (p + cOUTMAX) = om)
    (hX : g (p + cX) = X)
    (hbx : 0 ≤ bx) (hlt : bx < n) (hbi0 : 0 ≤ bi) (hbi7 : bi ≤ 7) (hL : IN + n ≤ L)
    (hX0 : 0 ≤ X) (hXL : X + 4 < L)
    (hl : g (p + X) = l) (hcv : g (p + (X + 1)) = cv) (ht : g (p + (X + 2)) = t) (hrt : g (p + (X + 3)) = rt)
    (htb : IN + n + om + 337 + 352 * t = tb) (ht0 : 0 ≤ tb) (htL : tb + 352 ≤ L) (hl1 : 1 ≤ l) (hl15 : l ≤ 15)
    (hfs : g (p + (tb + 16 + l)) = fs) (hc : g (p + (tb + l)) = c)
    (ho : fs ≤ 2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 ∧ 2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 < fs + c → g (p + (tb + 32 + l)) = o)
    (hsy0 : fs ≤ 2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 ∧ 2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 < fs + c →
      0 ≤ tb + 64 + o + (2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 - fs) ∧ tb + 64 + o + (2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 - fs) < L)
    (hsy : fs ≤ 2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 ∧ 2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 < fs + c → g (p + (tb + 64 + o + (2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 - fs))) = sy)
    {σ : Store} (hR : RegionAt p L g σ) (hwf : Store.WF σ) {F : Nat} (hF : 280 ≤ F) :
    ∃ a, ((run₅ F (decodeT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨ (run₅ F (decodeT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧ a.eval = some (.const (.cap p)) ∧
      RegionAt p L (decPost p g bx bi X l rt fs c (2 * cv + bitsF g p (8 * (IN + bx) + bi) 1) sy) (run₅ F (decodeT₅.subst 0 (.const (.cap p)), σ)).2 := by
  obtain ⟨v, qs, ⟨hv, hqs, hreg⟩, hcase⟩ :=
    run_of_triple₅ (decode5_bit p L g bx bi n om X l cv t rt tb fs c o sy hby hbi hn hom hX hbx hlt hbi0 hbi7 hL hX0 hXL hl hcv ht hrt htb ht0 htL hl1 hl15 hfs hc ho hsy0 hsy) (decode5_bit_cost p L g bx bi n om X l cv t rt tb fs c o sy hby hbi hn hom hX hbx hlt hbi0 hbi7 hL hX0 hXL hl hcv ht hrt htb ht0 htL hl1 hl15 hfs hc ho hsy0 hsy) hR hwf hF
  subst hv
  subst hqs
  rcases hcase with ⟨a, ha, hav, -⟩ | ⟨a, ds', ha, hav, hds'⟩
  · exact ⟨a, Or.inl ha, hav, hreg⟩
  · have hl := evalL_length hds'
    have hd : ds' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst hd
    exact ⟨a, Or.inr ha, hav, hreg⟩

theorem decode5_trunc_run (p : Int) (L : Nat) (g : Int → Int) (bx bi n : Int)
    (hby : g (p + cBY) = bx) (hbi : g (p + cBI) = bi) (hn : g (p + cN) = n) (hge : ¬ bx < n) (hL : 2080 ≤ L)
    {σ : Store} (hR : RegionAt p L g σ) (hwf : Store.WF σ) {F : Nat} (hF : 8 ≤ F) :
    ∃ a, ((run₅ F (decodeT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨ (run₅ F (decodeT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧ a.eval = some (.const (.cap p)) ∧
      RegionAt p L (Function.update (Function.update g (p + cREASON) rTRUNC) (p + cMODE) mREJECT) (run₅ F (decodeT₅.subst 0 (.const (.cap p)), σ)).2 := by
  obtain ⟨v, qs, ⟨hv, hqs, hreg⟩, hcase⟩ :=
    run_of_triple₅ (decode5_trunc p L g bx bi n hby hbi hn hge hL) (decode5_trunc_cost p L g bx bi n hby hbi hn hge hL) hR hwf hF
  subst hv
  subst hqs
  rcases hcase with ⟨a, ha, hav, -⟩ | ⟨a, ds', ha, hav, hds'⟩
  · exact ⟨a, Or.inl ha, hav, hreg⟩
  · have hl := evalL_length hds'
    have hd : ds' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst hd
    exact ⟨a, Or.inr ha, hav, hreg⟩

/-- The contents after one DECODE bit, relative to the base (DEFLATE's World form). -/
def decPostRel (p : Int) (f : Int → Int) (bx bi X l rt fs c v2 sy : Int) : Int → Int :=
  fun i => decPost p (fun a => f (a - p)) bx bi X l rt fs c v2 sy (p + i)

theorem decode5_bit_world (p : Int) (L : Nat) (f : Int → Int) (bx bi n om X l cv t rt tb fs c o sy : Int)
    (hby : f cBY = bx) (hbi : f cBI = bi) (hn : f cN = n) (hom : f cOUTMAX = om) (hX : f cX = X)
    (hbx : 0 ≤ bx) (hlt : bx < n) (hbi0 : 0 ≤ bi) (hbi7 : bi ≤ 7) (hL : IN + n ≤ L)
    (hX0 : 0 ≤ X) (hXL : X + 4 < L)
    (hl : f X = l) (hcv : f (X + 1) = cv) (ht : f (X + 2) = t) (hrt : f (X + 3) = rt)
    (htb : IN + n + om + 337 + 352 * t = tb) (ht0 : 0 ≤ tb) (htL : tb + 352 ≤ L) (hl1 : 1 ≤ l) (hl15 : l ≤ 15)
    (hfs : f (tb + 16 + l) = fs) (hc : f (tb + l) = c)
    (ho : fs ≤ 2 * cv + bitsF (fun a => f (a - p)) p (8 * (IN + bx) + bi) 1 ∧ 2 * cv + bitsF (fun a => f (a - p)) p (8 * (IN + bx) + bi) 1 < fs + c → f (tb + 32 + l) = o)
    (hsy0 : fs ≤ 2 * cv + bitsF (fun a => f (a - p)) p (8 * (IN + bx) + bi) 1 ∧ 2 * cv + bitsF (fun a => f (a - p)) p (8 * (IN + bx) + bi) 1 < fs + c →
      0 ≤ tb + 64 + o + (2 * cv + bitsF (fun a => f (a - p)) p (8 * (IN + bx) + bi) 1 - fs) ∧ tb + 64 + o + (2 * cv + bitsF (fun a => f (a - p)) p (8 * (IN + bx) + bi) 1 - fs) < L)
    (hsy : fs ≤ 2 * cv + bitsF (fun a => f (a - p)) p (8 * (IN + bx) + bi) 1 ∧ 2 * cv + bitsF (fun a => f (a - p)) p (8 * (IN + bx) + bi) 1 < fs + c → f (tb + 64 + o + (2 * cv + bitsF (fun a => f (a - p)) p (8 * (IN + bx) + bi) 1 - fs)) = sy)
    {σ : Store} (hw : World σ p L f) (hs : Sole σ p L) (hwf : Store.WF σ) {F : Nat} (hF : 280 ≤ F) :
    ∃ a, ((run₅ F (decodeT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨ (run₅ F (decodeT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧ a.eval = some (.const (.cap p)) ∧
      World (run₅ F (decodeT₅.subst 0 (.const (.cap p)), σ)).2 p L (decPostRel p f bx bi X l rt fs c (2 * cv + bitsF (fun a => f (a - p)) p (8 * (IN + bx) + bi) 1) sy) ∧ Sole (run₅ F (decodeT₅.subst 0 (.const (.cap p)), σ)).2 p L := by
  have hR := VIRL5.World.regionAt hw hs
  obtain ⟨a, hterm, hav, hreg⟩ := decode5_bit_run p L (fun a => f (a - p)) bx bi n om X l cv t rt tb fs c o sy
    (by simpa using hby) (by simpa using hbi) (by simpa using hn) (by simpa using hom) (by simpa using hX)
    hbx hlt hbi0 hbi7 hL hX0 hXL
    (by simpa using hl) (by simpa using hcv) (by simpa using ht) (by simpa using hrt)
    htb ht0 htL hl1 hl15 (by simpa using hfs) (by simpa using hc)
    (fun h => by simpa using ho h) hsy0 (fun h => by simpa using hsy h) hR hwf hF
  obtain ⟨hw', hs'⟩ := VIRL5.RegionAt.world hreg
  exact ⟨a, hterm, hav, hw', hs'⟩

theorem decode5_trunc_world (p : Int) (L : Nat) (f : Int → Int) (bx bi n : Int)
    (hby : f cBY = bx) (hbi : f cBI = bi) (hn : f cN = n) (hge : ¬ bx < n) (hL : 2080 ≤ L)
    {σ : Store} (hw : World σ p L f) (hs : Sole σ p L) (hwf : Store.WF σ) {F : Nat} (hF : 8 ≤ F) :
    ∃ a, ((run₅ F (decodeT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨ (run₅ F (decodeT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧ a.eval = some (.const (.cap p)) ∧
      World (run₅ F (decodeT₅.subst 0 (.const (.cap p)), σ)).2 p L
        (fun i => Function.update (Function.update (fun a => f (a - p)) (p + cREASON) rTRUNC) (p + cMODE) mREJECT (p + i)) ∧
      Sole (run₅ F (decodeT₅.subst 0 (.const (.cap p)), σ)).2 p L := by
  have hR := VIRL5.World.regionAt hw hs
  obtain ⟨a, hterm, hav, hreg⟩ := decode5_trunc_run p L (fun a => f (a - p)) bx bi n
    (by simpa using hby) (by simpa using hbi) (by simpa using hn) hge hL hR hwf hF
  obtain ⟨hw', hs'⟩ := VIRL5.RegionAt.world hreg
  exact ⟨a, hterm, hav, hw', hs'⟩

end VIRL5
