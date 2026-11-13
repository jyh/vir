/-
  O95 layer L5, Lean arm (DECLARATIONS-LEAN Addendum 5): each routine's COST lemma, proved with the routine and beside its triple.
  A cost is linear in the count argument, `a · len + b`, with a and b written in the statement. A client (LV8) cites these and the
  triples, never the bodies.
-/
import VIRL5.Cost5
import VIRL5.Fill
import VIRL5.CopyWithin
import VIRL5.Bit

namespace VIRL5
open VIRL1 VIRL2

/-- **fillR's cost**: 3 ⟶₅ steps per cell (the call, the test, the store) and 2 to stop. -/
theorem fillR_cost (p : Int) (n : Nat) (v : Int) : ∀ (len : Nat) (d : Int) (g : Int → Int), 0 ≤ d → d + len ≤ n →
    Cost₅ (RegionAt p n g) (.appK fillR (fillArg d len v) [.const (.cap p)]) (3 * len + 2)
  | 0, d, g, hd, hn => by
      refine Cost₅.mono (n := 0 + 1 + 1) ?_ (by omega)
      refine cost_appKFix₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, fillBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine cost_ite₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
        Const.ofL1]) ?_
      exact cost_retK₅ _ _ _
  | m + 1, d, g, hd, hn => by
      refine Cost₅.mono (n := 3 * m + 2 + 1 + 1 + 1) ?_ (by omega)
      refine cost_appKFix₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, fillBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine cost_ite₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
        Const.ofL1]) ?_
      simp only [Bool.false_eq_true, if_false]
      refine cost_letOp₅ (cs := [.cap p, .int d, .int v]) (by simp [Atom₅.evalL, Atom₅.eval])
        (store_at p n g d v ⟨hd, by push_cast at hn; omega⟩) (fun c => ?_)
      show Cost₅ (fun σ => c = .const (.cap p) ∧ RegionAt p n (Function.update g (p + d) v) σ) _ _
      refine cost_pre_pure₅ (fun hc => ?_)
      subst hc
      have ih := fillR_cost p n v m (d + 1) (Function.update g (p + d) v) (by omega) (by push_cast at hn ⊢; omega)
      have ih' := cost_pure_step_rev₅ (n := 3 * m + 1) (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
      simp only [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine cost_appKFix₅ rfl ?_ rfl rfl ih'
      simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]

/-- **copyWithinR's cost**: 4 ⟶₅ steps per cell (the call, the test, the load, the store) and 2 to stop. -/
theorem copyWithinR_cost (p : Int) (n : Nat) : ∀ (len : Nat) (s d : Int) (g : Int → Int),
    0 ≤ s → s + len ≤ n → 0 ≤ d → d + len ≤ n →
    Cost₅ (RegionAt p n g) (.appK copyWithinR (copyArg s d len) [.const (.cap p)]) (4 * len + 2)
  | 0, s, d, g, hs, hsn, hd, hdn => by
      refine Cost₅.mono (n := 0 + 1 + 1) ?_ (by omega)
      refine cost_appKFix₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, cwBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine cost_ite₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
        Const.ofL1, copyArg]) ?_
      exact cost_retK₅ _ _ _
  | m + 1, s, d, g, hs, hsn, hd, hdn => by
      refine Cost₅.mono (n := 4 * m + 2 + 1 + 1 + 1 + 1) ?_ (by omega)
      refine cost_appKFix₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, cwBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine cost_ite₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
        Const.ofL1, copyArg]) ?_
      simp only [Bool.false_eq_true, if_false]
      refine cost_letOp₅ (cs := [.cap p, .int s]) (by simp [Atom₅.evalL, Atom₅.eval, copyArg])
        (load_at p n g s ⟨hs, by push_cast at hsn; omega⟩) (fun w => ?_)
      show Cost₅ (fun σ => w = .const (.int (g (p + s))) ∧ RegionAt p n g σ) _ _
      refine cost_pre_pure₅ (fun hw => ?_)
      subst hw
      simp only [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine cost_letOp₅ (cs := [.cap p, .int d, .int (g (p + s))]) (by simp [Atom₅.evalL, Atom₅.eval, copyArg])
        (store_at p n g d (g (p + s)) ⟨hd, by push_cast at hdn; omega⟩) (fun c => ?_)
      show Cost₅ (fun σ => c = .const (.cap p) ∧ RegionAt p n (Function.update g (p + d) (g (p + s))) σ) _ _
      refine cost_pre_pure₅ (fun hc => ?_)
      subst hc
      have ih := copyWithinR_cost p n m (s + 1) (d + 1) (Function.update g (p + d) (g (p + s))) (by omega)
        (by push_cast at hsn ⊢; omega) (by omega) (by push_cast at hdn ⊢; omega)
      have ih' := cost_pure_step_rev₅ (n := 4 * m + 1) (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
      simp only [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine cost_appKFix₅ rfl ?_ rfl rfl ih'
      simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, copyArg]

/-! ## The embedding, counted: DEFLATE's own counted ⟶₂ steps carry over one for one (CE forward). -/

theorem stepsN₅_ι {m : Nat} {c d : Config} (h : VIRDeflate.Step.StepsN m c d) : StepsN₅ m (ιE c.1, c.2) (ιE d.1, d.2) := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (ce_fwd s) ih

theorem stepsN₂_steps {m : Nat} {c d : Config} (h : VIRDeflate.Step.StepsN m c d) : Steps₂ c d := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step s ih

theorem cost_embed₅ {P : Assn} {t : Tm₂} {w : Atom₂} {M : Nat}
    (hs : ∀ σ, ∃ m ≤ M, VIRDeflate.Step.StepsN m (t, σ) (.ret w, σ)) : Cost₅ P (ιE t) M := by
  intro σ σf _ _ _
  obtain ⟨m, hm, h⟩ := hs (σ ⊎ σf)
  have h₅ := run₅_of_stepsN (stepsN₅_ι h) 0
  simp only [Nat.add_zero] at h₅
  have ht : (run₅ m (ιE t, σ ⊎ σf)).1.IsTerminal := by rw [h₅]; simp [ιE, run₅, Tm₅.IsTerminal]
  rw [run₅_mono ht hm]
  exact ht

/-- **bitR's cost**: 258 ⟶₅ steps per bit (DEFLATE's own bound for one `BITc` call, 250, and 8 for the loop) and 2 to stop. -/
theorem bitR_cost (p : Int) (n : Nat) (f : Int → Int) : ∀ (len : Nat) (by_ bi k : Int),
    k = len → 0 ≤ by_ → 0 ≤ bi → bi ≤ 7 → 8 * by_ + bi + len ≤ 8 * n →
    Cost₅ (RegionAt p n f)
      (.appK bitR (.pair (.const (.int by_)) (.pair (.const (.int bi)) (.const (.int k)))) [.const (.cap p)]) (258 * len + 2)
  | 0, by_, bi, k, hk, h0, hb0, hb7, hn => by
      subst hk
      refine Cost₅.mono (n := 0 + 1 + 1) ?_ (by omega)
      refine cost_appKFix₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, bitBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine cost_ite₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
        Const.ofL1]) ?_
      exact cost_retK₅ _ _ _
  | m + 1, by_, bi, k, hk, h0, hb0, hb7, hn => by
      have hi' : ((bi.toNat : Nat) : Int) = bi := Int.toNat_of_nonneg hb0
      refine Cost₅.mono (n := 250 + 1 + ((0 + 1) + 1 + ((258 * m + 2) + 1 + 0)) + 1 + 1 + 1) ?_ (by omega)
      refine cost_appKFix₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, bitBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine cost_ite₅ (b := false) ?_ ?_
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
        omega
      simp only [Bool.false_eq_true, if_false]
      refine cost_letOp₅ (cs := [.cap p, .int by_]) (by simp [Atom₅.evalL, Atom₅.eval])
        (load_at p n f by_ ⟨h0, by push_cast at hn; omega⟩) (fun w => ?_)
      show Cost₅ (fun σ => w = .const (.int (f (p + by_))) ∧ RegionAt p n f σ) _ _
      refine cost_pre_pure₅ (fun hw => ?_)
      subst hw
      simp [Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA]
      -- the bit: DEFLATE's BITc, its triple through embed_rule₅ and its count through cost_embed₅
      have hsteps : ∀ σ, ∃ mm ≤ 250, VIRDeflate.Step.StepsN mm
          (.letE tint (.app VIRDeflate.Step.BITc (.pair (.const (.int (f (p + by_))))
            (.fst (.snd (.pair (.const (.int by_)) (.pair (.const (.int bi)) (.const (.int k)))))))) (.ret (.var 0)), σ)
          (.ret (.const (.int (VIRDeflate.bitAt (f (p + by_)) bi.toNat))), σ) := fun σ => by
        obtain ⟨mm, hmm, h⟩ := VIRDeflate.Step.bit_stepsN (f (p + by_)) bi.toNat (by omega)
          (.pair (.const (.int (f (p + by_)))) (.fst (.snd (.pair (.const (.int by_)) (.pair (.const (.int bi))
            (.const (.int k)))))))
          (by simp [Atom.eval, hi']) tint (.ret (.var 0)) σ
        exact ⟨mm, hmm, by simpa [Tm.subst, Atom.subst] using h⟩
      have hb := embed_rule₅ (P := RegionAt p n f) (w := .const (.int (VIRDeflate.bitAt (f (p + by_)) bi.toNat))) rfl
        (fun σ => by obtain ⟨mm, _, h⟩ := hsteps σ; exact stepsN₂_steps h)
      refine cost_letE₅ (n₁ := 250) (n₂ := 0 + 1 + 1 + (258 * m + 2 + 1 + 0)) (Q := fun r qs σ =>
          (r = .const (.int (VIRDeflate.bitAt (f (p + by_)) bi.toNat)) ∧ qs = []) ∧ RegionAt p n f σ)
        (conseq₅ (fun σ h => h) (fun r qs σ h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩) hb) (cost_embed₅ hsteps) (fun _ _ _ h => h.1.2)
        (fun v => ?_)
      refine cost_pre_pure₅ (fun hv => ?_)
      obtain ⟨rfl, -⟩ := hv
      simp [Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA]
      -- the next cursor
      obtain ⟨by', bi', hb0', hb7', hpos, hstep⟩ : ∃ by' bi' : Int, 0 ≤ bi' ∧ bi' ≤ 7 ∧ 8 * by' + bi' = 8 * by_ + bi + 1 ∧
          ∀ (aby abi : Atom₅), aby.eval = some (.const (.int by_)) → abi.eval = some (.const (.int bi)) →
          Triple₅ (RegionAt p n f)
            (.ite (.prim .eq [abi, .const (.int 7)])
              (.ret (.pair (.prim .add [aby, .const (.int 1)]) (.const (.int 0))))
              (.ret (.pair aby (.prim .add [abi, .const (.int 1)]))))
            (fun r qs σ => (r = .pair (.const (.int by')) (.const (.int bi')) ∧ qs = []) ∧ RegionAt p n f σ) ∧
          Cost₅ (RegionAt p n f)
            (.ite (.prim .eq [abi, .const (.int 7)])
              (.ret (.pair (.prim .add [aby, .const (.int 1)]) (.const (.int 0))))
              (.ret (.pair aby (.prim .add [abi, .const (.int 1)])))) (0 + 1) := by
        by_cases h7 : bi = 7
        · refine ⟨by_ + 1, 0, le_refl _, by norm_num, by omega, fun aby abi hby hbi => ⟨?_, ?_⟩⟩
          · refine ite_rule₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
              Const.ofL1, hbi, h7]) ?_
            exact conseq₅ (fun σ h => ⟨⟨rfl, rfl⟩, h⟩) (fun r qs σ h => h)
              (ret_rule₅ (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, hby, hbi]))
          · exact cost_ite₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
              Const.ofL1, hbi, h7]) (cost_ret₅ _ _)
        · refine ⟨by_, bi + 1, by omega, by omega, by omega, fun aby abi hby hbi => ⟨?_, ?_⟩⟩
          · refine ite_rule₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
              Const.ofL1, hbi, h7]) ?_
            exact conseq₅ (fun σ h => ⟨⟨rfl, rfl⟩, h⟩) (fun r qs σ h => h)
              (ret_rule₅ (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, hby, hbi]))
          · exact cost_ite₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
              Const.ofL1, hbi, h7]) (cost_ret₅ _ _)
      obtain ⟨hstepT, hstepC⟩ := hstep (.fst (.pair (.const (.int by_)) (.pair (.const (.int bi)) (.const (.int k)))))
        (.fst (.snd (.pair (.const (.int by_)) (.pair (.const (.int bi)) (.const (.int k)))))) (by simp [Atom₅.eval])
        (by simp [Atom₅.eval])
      refine cost_letE₅ (n₁ := 0 + 1) (n₂ := 258 * m + 2 + 1 + 0) hstepT hstepC (fun _ _ _ h => h.1.2) (fun v => ?_)
      refine cost_pre_pure₅ (fun hv => ?_)
      obtain ⟨rfl, -⟩ := hv
      simp [Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA]
      -- the recursive call: its triple (bitR_spec) and its cost (the induction)
      have sp := bitR_spec p n f m by' bi' (k - 1) (by push_cast at hk; omega) (by omega) hb0' hb7'
        (by push_cast at hn ⊢; omega)
      have sp' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) sp
      have ih := bitR_cost p n f m by' bi' (k - 1) (by push_cast at hk; omega) (by omega) hb0' hb7'
        (by push_cast at hn ⊢; omega)
      have ih' := cost_pure_step_rev₅ (n := 258 * m + 1) (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
      refine cost_letK₅ (n₁ := 258 * m + 2) (n₂ := 0) (appKFix_rule₅ rfl ?_ rfl rfl sp') (cost_appKFix₅ rfl ?_ rfl rfl ih')
        (fun v qs σ h => by rw [h.2.1]; rfl) (fun v qs hl => ?_)
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
      match qs, hl with
      | [_], _ => simp only [Tm₅.substAll, Tm₅.subst]; exact cost_retK₅ _ _ _

end VIRL5
