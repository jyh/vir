/-
  O95 layer L5, Lean arm (STATUS 320, LV8 Deflate5 + Fit5 for READ). As for COPY (CopyRun5), in one file: each branch's COST in
  ⟶₅ steps (the bit: 3 loads, the test, bitR's 258·1 + 2 through the call, the letK, 4 loads, 5 stores, the K test and at most
  one store = 276, against KSTEP − 29 = 483; TRUNC: 6); its RUN at every fuel above that, by run_of_triple₅; and the same in
  DEFLATE's terms (World on a Sole store) through bridge (i).
-/
import VIRL5.Read5
import VIRL5.RunTriple5
import VIRL5.Bridge5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

theorem read5_bit_cost (p : Int) (L : Nat) (g : Int → Int) (bx bi n k acc wt rt : Int)
    (hby : g (p + cBY) = bx) (hbi : g (p + cBI) = bi) (hn : g (p + cN) = n) (hk : g (p + cK) = k)
    (hacc : g (p + cACC) = acc) (hwt : g (p + cWT) = wt) (hrt : g (p + cRET) = rt)
    (hbx : 0 ≤ bx) (hlt : bx < n) (hbi0 : 0 ≤ bi) (hbi7 : bi ≤ 7) (hL : IN + n ≤ L) :
    Cost₅ (RegionAt p L g) (readT₅.subst 0 (.const (.cap p))) 276 := by
  have hIN : (IN : Int) = 2080 := rfl
  simp [readT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
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
  refine cost_ite₅ (b := true) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
  simp only [if_true]
  have ih := bitR_spec p L g 1 (IN + bx) bi 1 rfl (by rw [hIN]; omega) hbi0 hbi7 (by rw [hIN]; push_cast; omega)
  have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
  have ic := bitR_cost p L g 1 (IN + bx) bi 1 rfl (by rw [hIN]; omega) hbi0 hbi7 (by rw [hIN]; push_cast; omega)
  have ic' := cost_pure_step_rev₅ (n := 258 * 1 + 1) (fun σ => Step₅.appKFix rfl rfl rfl rfl) ic
  refine cost_letK₅ (n₁ := (258 * 1 + 1) + 1) (n₂ := 11)
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
  refine cost_letOp₅ (cs := [.cap p, .int (cK)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cK) ⟨by unfold cK; omega, by unfold cK; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hk]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cACC)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cACC) ⟨by unfold cACC; omega, by unfold cACC; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hacc]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cWT)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cWT) ⟨by unfold cWT; omega, by unfold cWT; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hwt]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cRET)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cRET) ⟨by unfold cRET; omega, by unfold cRET; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hrt]
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
  refine cost_letOp₅ (cs := [.cap p, .int (cACC), .int (acc + bitsF g p (8 * (IN + bx) + bi) 1 * wt)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
    (store_at p L _ (cACC) (acc + bitsF g p (8 * (IN + bx) + bi) 1 * wt) ⟨by unfold cACC; omega, by unfold cACC; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cWT), .int (2 * wt)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
    (store_at p L _ (cWT) (2 * wt) ⟨by unfold cWT; omega, by unfold cWT; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int (cK), .int (k - 1)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
    (store_at p L _ (cK) (k - 1) ⟨by unfold cK; omega, by unfold cK; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  by_cases hk1 : k - 1 = 0
  · refine cost_ite₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_
    simp only [if_true]
    refine cost_letOp₅ (cs := [.cap p, .int (cMODE), .int (rt)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
      (store_at p L _ (cMODE) (rt) ⟨by unfold cMODE; omega, by unfold cMODE; omega⟩) (fun w => ?_)
    refine cost_pre_pure₅ (fun hw => ?_)
    subst hw
    simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
    exact cost_ret₅ _ _
  · refine cost_ite₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega) ?_
    simp only [Bool.false_eq_true, if_false]
    exact Cost₅.mono (cost_ret₅ _ _) (by omega)

theorem read5_trunc_cost (p : Int) (L : Nat) (g : Int → Int) (bx bi n : Int)
    (hby : g (p + cBY) = bx) (hbi : g (p + cBI) = bi) (hn : g (p + cN) = n) (hge : ¬ bx < n) (hL : 2080 ≤ L) :
    Cost₅ (RegionAt p L g) (readT₅.subst 0 (.const (.cap p))) 6 := by
  simp [readT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
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

theorem read5_bit_run (p : Int) (L : Nat) (g : Int → Int) (bx bi n k acc wt rt : Int)
    (hby : g (p + cBY) = bx) (hbi : g (p + cBI) = bi) (hn : g (p + cN) = n) (hk : g (p + cK) = k)
    (hacc : g (p + cACC) = acc) (hwt : g (p + cWT) = wt) (hrt : g (p + cRET) = rt)
    (hbx : 0 ≤ bx) (hlt : bx < n) (hbi0 : 0 ≤ bi) (hbi7 : bi ≤ 7) (hL : IN + n ≤ L)
    {σ : Store} (hR : RegionAt p L g σ) (hwf : Store.WF σ) {F : Nat} (hF : 276 ≤ F) :
    ∃ a, ((run₅ F (readT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
          (run₅ F (readT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧
      a.eval = some (.const (.cap p)) ∧
      RegionAt p L (readPost p g bx bi k acc wt rt) (run₅ F (readT₅.subst 0 (.const (.cap p)), σ)).2 := by
  obtain ⟨v, qs, ⟨hv, hqs, hreg⟩, hcase⟩ :=
    run_of_triple₅ (read5_bit p L g bx bi n k acc wt rt hby hbi hn hk hacc hwt hrt hbx hlt hbi0 hbi7 hL) (read5_bit_cost p L g bx bi n k acc wt rt hby hbi hn hk hacc hwt hrt hbx hlt hbi0 hbi7 hL) hR hwf hF
  subst hv
  subst hqs
  rcases hcase with ⟨a, ha, hav, -⟩ | ⟨a, ds', ha, hav, hds'⟩
  · exact ⟨a, Or.inl ha, hav, hreg⟩
  · have hl := evalL_length hds'
    have hd : ds' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst hd
    exact ⟨a, Or.inr ha, hav, hreg⟩

theorem read5_trunc_run (p : Int) (L : Nat) (g : Int → Int) (bx bi n : Int)
    (hby : g (p + cBY) = bx) (hbi : g (p + cBI) = bi) (hn : g (p + cN) = n) (hge : ¬ bx < n) (hL : 2080 ≤ L)
    {σ : Store} (hR : RegionAt p L g σ) (hwf : Store.WF σ) {F : Nat} (hF : 6 ≤ F) :
    ∃ a, ((run₅ F (readT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
          (run₅ F (readT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧
      a.eval = some (.const (.cap p)) ∧
      RegionAt p L (Function.update (Function.update g (p + cREASON) rTRUNC) (p + cMODE) mREJECT)
        (run₅ F (readT₅.subst 0 (.const (.cap p)), σ)).2 := by
  obtain ⟨v, qs, ⟨hv, hqs, hreg⟩, hcase⟩ :=
    run_of_triple₅ (read5_trunc p L g bx bi n hby hbi hn hge hL) (read5_trunc_cost p L g bx bi n hby hbi hn hge hL) hR hwf hF
  subst hv
  subst hqs
  rcases hcase with ⟨a, ha, hav, -⟩ | ⟨a, ds', ha, hav, hds'⟩
  · exact ⟨a, Or.inl ha, hav, hreg⟩
  · have hl := evalL_length hds'
    have hd : ds' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst hd
    exact ⟨a, Or.inr ha, hav, hreg⟩

/-- The contents after one READ bit, relative to the base (DEFLATE's World form). -/
def readPostRel (p : Int) (f : Int → Int) (bx bi k acc wt rt : Int) : Int → Int :=
  fun i => readPost p (fun a => f (a - p)) bx bi k acc wt rt (p + i)

theorem read5_bit_world (p : Int) (L : Nat) (f : Int → Int) (bx bi n k acc wt rt : Int)
    (hby : f cBY = bx) (hbi : f cBI = bi) (hn : f cN = n) (hk : f cK = k)
    (hacc : f cACC = acc) (hwt : f cWT = wt) (hrt : f cRET = rt)
    (hbx : 0 ≤ bx) (hlt : bx < n) (hbi0 : 0 ≤ bi) (hbi7 : bi ≤ 7) (hL : IN + n ≤ L)
    {σ : Store} (hw : World σ p L f) (hs : Sole σ p L) (hwf : Store.WF σ) {F : Nat} (hF : 276 ≤ F) :
    ∃ a, ((run₅ F (readT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
          (run₅ F (readT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧
      a.eval = some (.const (.cap p)) ∧
      World (run₅ F (readT₅.subst 0 (.const (.cap p)), σ)).2 p L (readPostRel p f bx bi k acc wt rt) ∧
      Sole (run₅ F (readT₅.subst 0 (.const (.cap p)), σ)).2 p L := by
  have hR := VIRL5.World.regionAt hw hs
  obtain ⟨a, hterm, hav, hreg⟩ := read5_bit_run p L (fun a => f (a - p)) bx bi n k acc wt rt
    (by simpa using hby) (by simpa using hbi) (by simpa using hn) (by simpa using hk)
    (by simpa using hacc) (by simpa using hwt) (by simpa using hrt) hbx hlt hbi0 hbi7 hL hR hwf hF
  obtain ⟨hw', hs'⟩ := VIRL5.RegionAt.world hreg
  exact ⟨a, hterm, hav, hw', hs'⟩

theorem read5_trunc_world (p : Int) (L : Nat) (f : Int → Int) (bx bi n : Int)
    (hby : f cBY = bx) (hbi : f cBI = bi) (hn : f cN = n) (hge : ¬ bx < n) (hL : 2080 ≤ L)
    {σ : Store} (hw : World σ p L f) (hs : Sole σ p L) (hwf : Store.WF σ) {F : Nat} (hF : 6 ≤ F) :
    ∃ a, ((run₅ F (readT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
          (run₅ F (readT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧
      a.eval = some (.const (.cap p)) ∧
      World (run₅ F (readT₅.subst 0 (.const (.cap p)), σ)).2 p L
        (fun i => Function.update (Function.update (fun a => f (a - p)) (p + cREASON) rTRUNC) (p + cMODE) mREJECT (p + i)) ∧
      Sole (run₅ F (readT₅.subst 0 (.const (.cap p)), σ)).2 p L := by
  have hR := VIRL5.World.regionAt hw hs
  obtain ⟨a, hterm, hav, hreg⟩ := read5_trunc_run p L (fun a => f (a - p)) bx bi n
    (by simpa using hby) (by simpa using hbi) (by simpa using hn) hge hL hR hwf hF
  obtain ⟨hw', hs'⟩ := VIRL5.RegionAt.world hreg
  exact ⟨a, hterm, hav, hw', hs'⟩

end VIRL5
