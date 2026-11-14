/-
  O95 layer L5, Lean arm (STATUS 321, LV8 assembly, LV8-MAP Addendum 5): Refine₅ at BUILD. `buildT₅` differs from DEFLATE's
  `buildN` only in the phase-0 branch, so at phases 1–4 the two runs agree after the phase test (`build5_two`, `build_two`), and DEFLATE's
  step is the ⟶₅ step (`stepS₅_build`, through `body_run`: a DEFLATE step is its mode body's run at every fuel ≥ 483). At
  phase 0 the ⟶₅ step enters zeroT₅ (`zero_entry`): the chunk clears [tbb + j, tbb + 16) in one fillR call, which is 16 − j
  DEFLATE build_zero_cell steps (`zero_iter`); at INDEX = 16 both take DEFLATE's own end (PHASE := 1, INDEX := 0), j = 1.
-/
import VIRL5.RefineFixlens5
import VIRL5.TabKeep5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- A DEFLATE step in a mode with an entry is that body's run, at every fuel ≥ 483. -/
theorem body_run {σ σ' : Store} {p : Int} {L : Nat} {f : Int → Int} {k : Int} {t : NT}
    (hw : World σ p L f) (hL : 0 < L) (hm : f cMODE = k) (hk : modes.lookup k = some t)
    (hfree : appFree (t.c ["w"]) = true) (hlen : plen (t.c ["w"]) ≤ KSTEP - 29) (h : stepS p σ = some σ') :
    ∀ F, KSTEP - 29 ≤ F → run₂ F (closeAt p (t.c ["w"]), σ) = (.ret (.const (.cap p)), σ') := by
  obtain ⟨k₁, hk₁, h₁⟩ := step_dispatchN hw hL k hm
  rw [hk] at h₁
  have e := run₂_stepsN h₁ (KSTEP - k₁)
  rw [show k₁ + (KSTEP - k₁) = KSTEP by unfold KSTEP; omega] at e
  unfold stepS at h
  rw [e] at h
  rcases hr : run₂ (KSTEP - k₁) (closeAt p (t.c ["w"]), σ) with ⟨e', σ''⟩
  rw [hr] at h
  obtain ⟨k₂, hk₂, h₂⟩ := stepsN_run (KSTEP - k₁) hr
  have hb := stepsN_le h₂ (by simpa [closeAt, (plen_subst _ _ _).2] using hfree)
  simp only [closeAt, (plen_subst _ _ _).1] at hb
  cases e' with
  | ret a =>
    cases a with
    | const c =>
      cases c with
      | cap q =>
        simp only at h
        split_ifs at h with hq
        simp only [Option.some.injEq] at h
        subst hq
        subst h
        intro F hF
        exact run₂_of_stepsN h₂ rfl F (by simp only [KSTEP] at hlen hF ⊢; omega)
      | _ => simp at h
    | _ => simp at h
  | _ => simp at h

/-- The first ⟶₅ step of BUILD: PHASE loaded from the world. -/
theorem run₅_load_phase (N : Nat) {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 12 < L)
    (X : Tm₅) :
    run₅ (N + 1) (.letOp .load [.const (.cap p), .const (.int cPHASE)] t5int X, σ) =
      run₅ N (X.subst 0 (.const (.int (f cPHASE))), σ) := by
  have g12 := hw.cell 12 (by decide) (by omega)
  have hL' : (12 : Int) < (L : Int) := by omega
  simp [run₅, stepFn₅, Atom₅.evalL, Atom₅.eval, opStep₅, lowerV, opStep, Store.load, hw.reg, cPHASE, ιA, hL, hL', g12]

/-- BUILD's rest, at the phase φ, closed at ⟨p⟩ (a ⟶₂ term). -/
abbrev restAt (p φ : Int) : Tm₂ :=
  ((buildRestN.c ["ph", "w"]).subst 1 (Atom.const (Const.cap p))).subst 0 (Atom.const (Const.int φ))

/-- **BUILD over ⟶₅, two steps:** the phase test sends phase 0 to zeroT₅ and every other phase to DEFLATE's rest. -/
theorem build5_two (N : Nat) {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 12 < L) :
    run₅ (N + 2) (buildT₅.subst 0 (.const (.cap p)), σ) =
      run₅ N (if f cPHASE = 0 then zeroT₅.subst 0 (.const (.cap p)) else ιE (restAt p (f cPHASE)), σ) := by
  have e : buildT₅.subst 0 (.const (.cap p)) = .letOp .load [.const (.cap p), .const (.int cPHASE)] t5int
      (.ite (.prim .eq [.var 0, .const (.int 0)]) ((zeroT₅.shift 0).subst 1 (.const (.cap p)))
        ((ιE (buildRestN.c ["ph", "w"])).subst 1 (.const (.cap p)))) := by
    simp [buildT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  rw [show N + 2 = (N + 1) + 1 from rfl, e, run₅_load_phase (N + 1) hw hL]
  simp only [Tm₅.subst, Atom₅.subst, Atom₅.substL, show ¬ ((0 : Nat) < 0) by omega, if_false, if_true]
  rw [run₅_ite_eq]
  by_cases h0 : f cPHASE = 0
  · rw [if_pos h0, if_pos h0, shift_branch₅]
  · rw [if_neg h0, if_neg h0, restAt, ιE_subst, ιE_subst]
    rfl

/-- **DEFLATE's BUILD, two steps:** at a phase other than 0, the phase test sends it to its rest. -/
theorem build_two (N : Nat) {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 12 < L)
    (hph : f cPHASE ≠ 0) :
    run₂ (N + 2) (closeAt p (buildN.c ["w"]), σ) = run₂ N (restAt p (f cPHASE), σ) := by
  have g12 := hw.cell 12 (by decide) (by omega)
  have hL' : (12 : Int) < (L : Int) := by omega
  have h12 : f 12 ≠ 0 := hph
  simp [restAt, closeAt, buildN, buildRestN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst,
    Atom.subst, Atom.substL, run₂, stepFn₂, stepFn, opStep, Store.load, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂,
    pInterp, L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool, cPHASE, hL, hL', g12, h12]

theorem build_mem₅ : (mBUILD, buildN) ∈ modes := by simp [modes]

/-- **At phases 1–4, DEFLATE's BUILD step is the ⟶₅ step.** -/
theorem stepS₅_build {σ σ' : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L)
    (hm : f cMODE = mBUILD) (hph : f cPHASE ≠ 0) (h : stepS p σ = some σ') : stepS₅ p σ = some σ' := by
  have hfit := modes_fit (mBUILD, buildN) build_mem₅ (by decide)
  have hb := body_run hw (by omega) hm rfl hfit.1 hfit.2 h
  have hlk : modes₅.lookup (f cMODE) = some (buildT₅.shift 0) := by rw [hm]; rfl
  obtain ⟨σL, hst, hP⟩ := stepS₅_reex hw (by omega) hlk (F₀ := 483) (by omega) (P := fun s => s = σ')
    (fun F hF => by
      obtain ⟨N, rfl⟩ : ∃ N, F = N + 2 := ⟨F - 2, by omega⟩
      have hD := hb (N + 2) (by unfold KSTEP; omega)
      rw [build_two N hw (by omega) hph] at hD
      rw [build5_two N hw (by omega), if_neg hph, run₅_ιE, hD]
      exact ⟨_, Or.inl rfl, by simp [ιA, Atom₅.eval], rfl⟩)
  rw [hst, hP]

/-- At phase 0, BUILD over ⟶₅ enters zeroT₅ after the phase test. -/
theorem zero_entry (N : Nat) {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 12 < L)
    (hph : f cPHASE = 0) :
    run₅ (N + 2) (buildT₅.subst 0 (.const (.cap p)), σ) = run₅ N (zeroT₅.subst 0 (.const (.cap p)), σ) := by
  rw [build5_two N hw hL, if_pos hph]

/-! ## ZERO's end over ⟶₅: cost, run, World -/

theorem zero5_end_cost (p : Int) (L : Nat) (g : Int → Int) (j : Int) (hj : g (p + cINDEX) = j) (hj16 : ¬ j < 16)
    (hL : 2080 ≤ L) : Cost₅ (RegionAt p L g) (zeroT₅.subst 0 (.const (.cap p))) 4 := by
  simp [zeroT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int cINDEX]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cINDEX ⟨by unfold cINDEX; omega, by unfold cINDEX; omega⟩) (fun w => ?_)
  show Cost₅ (fun σ => w = .const (.int (g (p + cINDEX))) ∧ RegionAt p L g σ) _ _
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hj]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_ite₅ (b := false) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
  simp only [Bool.false_eq_true, if_false]
  refine cost_letOp₅ (cs := [.cap p, .int cPHASE, .int 1])
    (by simp [Atom₅.evalL, Atom₅.eval, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ cPHASE 1 ⟨by unfold cPHASE; omega, by unfold cPHASE; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int cINDEX, .int 0])
    (by simp [Atom₅.evalL, Atom₅.eval, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (store_at p L _ cINDEX 0 ⟨by unfold cINDEX; omega, by unfold cINDEX; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact cost_ret₅ _ _

theorem zero5_end_world (p : Int) (L : Nat) (f : Int → Int) (j : Int) (hj : f cINDEX = j) (hj16 : ¬ j < 16)
    (hL : 2080 ≤ L) {σ : Store} (hw : World σ p L f) (hs : Sole σ p L) (hwf : Store.WF σ) {F : Nat} (hF : 4 ≤ F) :
    ∃ a, ((run₅ F (zeroT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
          (run₅ F (zeroT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧
      a.eval = some (.const (.cap p)) ∧
      World (run₅ F (zeroT₅.subst 0 (.const (.cap p)), σ)).2 p L
        (fun i => Function.update (Function.update (fun a => f (a - p)) (p + cPHASE) 1) (p + cINDEX) 0 (p + i)) ∧
      Sole (run₅ F (zeroT₅.subst 0 (.const (.cap p)), σ)).2 p L := by
  have hR := VIRL5.World.regionAt hw hs
  obtain ⟨v, qs, ⟨hv, hqs, hreg⟩, hcase⟩ :=
    run_of_triple₅ (zero5_end p L (fun a => f (a - p)) j (by simpa using hj) hj16 hL)
      (zero5_end_cost p L (fun a => f (a - p)) j (by simpa using hj) hj16 hL) hR hwf hF
  subst hv
  subst hqs
  obtain ⟨hw', hs'⟩ := VIRL5.RegionAt.world hreg
  rcases hcase with ⟨a, ha, hav, -⟩ | ⟨a, ds, ha, hav, hds⟩
  · exact ⟨a, Or.inl ha, hav, hw', hs'⟩
  · have hl := evalL_length hds
    have hd : ds = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst hd
    exact ⟨a, Or.inr ha, hav, hw', hs'⟩

/-! ## ZERO over DEFLATE, c steps -/

/-- DEFLATE's contents after c ZERO steps from INDEX = j, relative to the base. -/
def zeroRel (g : Int → Int) (j tbb : Int) (c : Nat) : Int → Int :=
  Function.update (fun a => if tbb + j ≤ a ∧ a < tbb + j + c then 0 else g a) cINDEX (j + c)

theorem zero_iter {p : Int} {L : Nat} (hL : 2080 ≤ L) (X tbb : Int) : ∀ (c : Nat) (σ : Store) (g : Int → Int) (j : Int),
    World σ p L g → g cMODE = mBUILD → g cPHASE = 0 → g cINDEX = j → g cX = X → g (X + 7) = tbb →
    0 ≤ X → X + 8 < L → 0 ≤ j → j + c ≤ 16 → 2080 ≤ tbb → tbb + 352 ≤ L → tbb + 16 ≤ X →
    ∃ σ', iterS p c σ = some σ' ∧ World σ' p L (zeroRel g j tbb c)
  | 0, σ, g, j, hw, _, _, hj, _, _, _, _, _, _, _, _, _ =>
    ⟨σ, rfl, world_congr hw (fun i _ _ => by
      unfold zeroRel
      simp only [Function.update_apply, Nat.cast_zero, add_zero]
      split_ifs with h1 h2 <;> (try subst_vars) <;> first | omega | simp_all)⟩
  | c + 1, σ, g, j, hw, hm, hph, hj, hX, ht, hX0, hXL, hj0, hc, ht0, htL, htX => by
    have hS := stepS_of_mode hw (by omega) hm rfl (modes_fit (mBUILD, buildN) build_mem₅ (by decide)).1
      (modes_fit (mBUILD, buildN) build_mem₅ (by decide)).2
      (build_zero_cell hw hL j X tbb hph hj hX ht hX0 hXL hj0 (by push_cast at hc; omega) (by omega) htL)
    have hw1 := (hw.store (i := tbb + j) (v := 0) (by omega) (by omega)).store (i := 13) (v := j + 1) (by omega) (by omega)
    set g1 := Function.update (Function.update g (tbb + j) 0) 13 (j + 1) with hg1
    have u : ∀ d : Int, d ≠ tbb + j → d ≠ 13 → g1 d = g d := by
      intro d h1 h2; simp [hg1, Function.update_apply, h1, h2]
    obtain ⟨σ', hit, hw'⟩ := zero_iter hL X tbb c _ g1 (j + 1) hw1
      (by rw [u _ (by unfold cMODE; omega) (by unfold cMODE; omega)]; exact hm)
      (by rw [u _ (by unfold cPHASE; omega) (by unfold cPHASE; omega)]; exact hph)
      (by show g1 13 = j + 1; simp [hg1, Function.update_apply])
      (by rw [u _ (by unfold cX; omega) (by unfold cX; omega)]; exact hX)
      (by rw [u _ (by omega) (by omega)]; exact ht)
      hX0 hXL (by omega) (by push_cast at hc ⊢; omega) ht0 htL htX
    refine ⟨σ', by simp only [iterS, hS, Option.bind_some]; exact hit, world_congr hw' (fun i _ _ => ?_)⟩
    simp only [zeroRel, hg1, Function.update_apply, cINDEX]
    push_cast
    split_ifs <;> omega

/-! ## Refine₅ at BUILD -/

theorem refine_build (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (σ : Store) (f : Int → Int)
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hs : Sole σ p (L0 b.size om)) (hi : Inv b om lit f)
    (hm : f cMODE = mBUILD) :
    ∃ j σ', stepS₅ p σ = some σ' ∧ iterS p j σ = some σ' ∧ Sole σ' p (L0 b.size om) ∧
      (f cMODE ≠ mDONE → f cMODE ≠ mREJECT → 1 ≤ j) := by
  have hL0 : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hLv : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hX : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  have hLB : LB0 b.size om = 2080 + b.size + om := rfl
  have hwf := wf_of_sole hw hs (by omega)
  have hd : f cMODE ≠ mDONE := by rw [hm]; decide
  have hr : f cMODE ≠ mREJECT := by rw [hm]; decide
  by_cases hph : f cPHASE = 0
  · have hbi : buildInv b.size om f := by have h := hi.2.cur; rw [hm, facts_build] at h; exact h
    obtain ⟨ht0, ht2, htb, hsb0, hnn0, hsbn, hnn288⟩ := bp hbi hi.1.hdr_rng
    have hTB : f (X0 b.size om + 7) = LB0 b.size om + 337 + 352 * f cTGT := htb
    obtain ⟨-, -, -, -, h0, -, -, -, -⟩ := hbi
    obtain ⟨hj0, hj16, -⟩ := h0 hph
    have hlk : modes₅.lookup (f cMODE) = some (buildT₅.shift 0) := by rw [hm]; rfl
    by_cases hlt : f cINDEX < 16
    · -- the ZERO chunk: 16 − INDEX DEFLATE steps
      set j := f cINDEX with hjd
      set tbb := f (X0 b.size om + 7) with htbd
      obtain ⟨σL, hstL, hwL, hsL⟩ := stepS₅_reex hw (by omega) hlk (F₀ := 3 * 16 + 8 + 2) (by omega)
        (P := fun σ' => World σ' p (L0 b.size om) (zeroPostRel p f j tbb) ∧ Sole σ' p (L0 b.size om))
        (fun F hF => by
          obtain ⟨N, rfl⟩ : ∃ N, F = N + 2 := ⟨F - 2, by omega⟩
          rw [zero_entry N hw (by omega) hph]
          obtain ⟨a, h1, h2, h3, h4⟩ := zero5_chunk_world p (L0 b.size om) f j (X0 b.size om) tbb rfl hj0 hlt hi.1.x_eq
            rfl (by omega) (by omega) (by omega) (by omega) hL0 hw hs hwf (F := N) (by omega)
          exact ⟨a, h1, h2, h3, h4⟩)
      obtain ⟨σD, hit, hwD⟩ := zero_iter hL0 (X0 b.size om) tbb (16 - j).toNat σ f j hw hm hph rfl hi.1.x_eq rfl
        (by omega) (by omega) hj0 (by omega) (by omega) (by omega) (by omega)
      have hsD := iterS_sole _ σ σD hs hit
      have hcT : ((16 - j).toNat : Int) = 16 - j := Int.toNat_of_nonneg (by omega)
      have e := sole_world_eq' hwL hsL hwD hsD (fun i h0 h1 => by
        simp only [zeroRel, zeroPostRel, zeroPost]
        simp only [hcT, Function.update_apply, fillF, add_right_inj, add_sub_cancel_left, cINDEX]
        split_ifs <;> first | omega | (congr 1; omega) | simp_all)
      subst e
      exact ⟨(16 - j).toNat, _, hstL, hit, hsL, fun _ _ => by omega⟩
    · -- ZERO's end: DEFLATE's own branch, j = 1
      obtain ⟨σL, hstL, hwL, hsL⟩ := stepS₅_reex hw (by omega) hlk (F₀ := 4 + 2) (by omega)
        (P := fun σ' => World σ' p (L0 b.size om)
            (fun i => Function.update (Function.update (fun a => f (a - p)) (p + cPHASE) 1) (p + cINDEX) 0 (p + i)) ∧
          Sole σ' p (L0 b.size om))
        (fun F hF => by
          obtain ⟨N, rfl⟩ : ∃ N, F = N + 2 := ⟨F - 2, by omega⟩
          rw [zero_entry N hw (by omega) hph]
          obtain ⟨a, h1, h2, h3, h4⟩ := zero5_end_world p (L0 b.size om) f (f cINDEX) rfl hlt hL0 hw hs hwf (F := N)
            (by omega)
          exact ⟨a, h1, h2, h3, h4⟩)
      have hfit := modes_fit (mBUILD, buildN) build_mem₅ (by decide)
      have hS := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
        (build_zero_end hw hL0 (f cINDEX) (X0 b.size om) (f (X0 b.size om + 7)) hph rfl hi.1.x_eq rfl (by omega) (by omega)
          hlt)
      have hwD := (hw.store (i := 12) (v := 1) (by omega) (by omega)).store (i := 13) (v := 0) (by omega) (by omega)
      have hsD := stepS_sole hs hS
      have e := sole_world_eq' hwL hsL hwD hsD (fun i _ _ => by
        simp only [Function.update_apply, add_right_inj, add_sub_cancel_left, cPHASE, cINDEX])
      subst e
      exact ⟨1, _, hstL, by simp [iterS, hS], hsL, fun _ _ => le_refl _⟩
  · -- phases 1–4: DEFLATE's own step, j = 1
    obtain ⟨σ1, f1, hst, -, -, -⟩ := stepSafe b om lit p σ f hb hw hi hd hr
    exact ⟨1, σ1, stepS₅_build hw hL0 hm hph hst, by simp [iterS, hst], stepS_sole hs hst, fun _ _ => le_refl _⟩

end VIRL5
