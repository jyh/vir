/-
  O95 layer L5, Lean arm (STATUS 321, LV8 assembly, LV8-MAP Addendum 5): Refine₅ at SCOPY, as at COPY. The ⟶₅ step copies
  c = min(PEND, 32) stored bytes from the input to the output in one copyWithinR call; DEFLATE copies one per step
  (scopy_byte), so c DEFLATE steps reach the same contents (`scopy_iter`, read through `cwR`). At PEND = 0 both take DEFLATE's
  own end branch (MODE := DONE if BFINAL, else HDR), j = 1.
-/
import VIRL5.RefineCopy5
import VIRL5.ScopyWorld5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-! ## SCOPY's end branch over ⟶₅ -/

theorem scopy5_end_cost (p : Int) (L : Nat) (g : Int → Int) (bf : Int)
    (hk : g (p + cPEND) = 0) (hbf : g (p + cBF) = bf) (hL : 6 ≤ L) :
    Cost₅ (RegionAt p L g) (scopyT₅.subst 0 (.const (.cap p))) 5 := by
  simp [scopyT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int cPEND]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cPEND ⟨by unfold cPEND; omega, by unfold cPEND; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hk]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_ite₅ (b := true) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
  simp only [if_true]
  refine cost_letOp₅ (cs := [.cap p, .int cBF]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cBF ⟨by unfold cBF; omega, by unfold cBF; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hbf]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  by_cases h1 : bf = 1
  · refine cost_ite₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
      Const.ofL1, h1]) ?_
    simp only [if_true]
    refine cost_letOp₅ (cs := [.cap p, .int cMODE, .int mDONE]) (by simp [Atom₅.evalL, Atom₅.eval])
      (store_at p L g cMODE mDONE ⟨by unfold cMODE; omega, by unfold cMODE; omega⟩) (fun w => ?_)
    refine cost_pre_pure₅ (fun hw => ?_)
    subst hw
    simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
    exact cost_ret₅ _ _
  · refine cost_ite₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
      Const.ofL1, h1]) ?_
    simp only [Bool.false_eq_true, if_false]
    refine cost_letOp₅ (cs := [.cap p, .int cMODE, .int mHDR]) (by simp [Atom₅.evalL, Atom₅.eval])
      (store_at p L g cMODE mHDR ⟨by unfold cMODE; omega, by unfold cMODE; omega⟩) (fun w => ?_)
    refine cost_pre_pure₅ (fun hw => ?_)
    subst hw
    simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
    exact cost_ret₅ _ _

theorem scopy5_end_world (p : Int) (L : Nat) (f : Int → Int) (bf : Int) (hk : f cPEND = 0) (hbf : f cBF = bf) (hL : 6 ≤ L)
    {σ : Store} (hw : World σ p L f) (hs : Sole σ p L) (hwf : Store.WF σ) {F : Nat} (hF : 5 ≤ F) :
    ∃ a, ((run₅ F (scopyT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
          (run₅ F (scopyT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧
      a.eval = some (.const (.cap p)) ∧
      World (run₅ F (scopyT₅.subst 0 (.const (.cap p)), σ)).2 p L
        (fun i => Function.update (fun a => f (a - p)) (p + cMODE) (if bf = 1 then mDONE else mHDR) (p + i)) ∧
      Sole (run₅ F (scopyT₅.subst 0 (.const (.cap p)), σ)).2 p L := by
  have hR := VIRL5.World.regionAt hw hs
  have hk' : (fun a => f (a - p)) (p + cPEND) = 0 := by simpa using hk
  have hbf' : (fun a => f (a - p)) (p + cBF) = bf := by simpa using hbf
  obtain ⟨v, qs, ⟨hv, hqs, hreg⟩, hcase⟩ :=
    run_of_triple₅ (scopy5_end p L _ bf hk' hbf' hL) (scopy5_end_cost p L _ bf hk' hbf' hL) hR hwf hF
  subst hv
  subst hqs
  obtain ⟨hw', hs'⟩ := VIRL5.RegionAt.world hreg
  rcases hcase with ⟨a, ha, hav, -⟩ | ⟨a, ds', ha, hav, hds'⟩
  · exact ⟨a, Or.inl ha, hav, hw', hs'⟩
  · have hl := evalL_length hds'
    have hd : ds' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst hd
    exact ⟨a, Or.inr ha, hav, hw', hs'⟩

/-! ## SCOPY over DEFLATE, c steps -/

/-- DEFLATE's contents after c SCOPY steps, relative to the base. -/
def scopyRel (f : Int → Int) (k bx m n : Int) (c : Nat) : Int → Int :=
  Function.update (Function.update (Function.update (cwR f (2080 + bx) (2080 + n + m) c) cBY (bx + c)) cM (m + c)) cPEND
    (k - c)

theorem scopy_mem : (mSCOPY, scopyN) ∈ modes := by simp [modes]

theorem scopy_iter {p : Int} {L : Nat} (n om : Nat) (hL : 2080 + n + om ≤ L) :
    ∀ (c : Nat) (σ : Store) (g : Int → Int) (k : Int) (bx m : Nat),
    World σ p L g → g cMODE = mSCOPY → g cPEND = k → g cBY = bx → g cN = n → g cM = m →
    (c : Int) ≤ k → bx + c ≤ n → m + c ≤ om →
    ∃ σ', iterS p c σ = some σ' ∧ World σ' p L (scopyRel g k bx m n c)
  | 0, σ, g, k, bx, m, hw, _, hk, hby, _, hm, _, _, _ =>
    ⟨σ, rfl, world_congr hw (fun i _ _ => by
      unfold scopyRel
      simp only [cwR, Function.update_apply, Nat.cast_zero, add_zero, sub_zero]
      split_ifs with h1 h2 h3 <;> (try subst_vars) <;> first | omega | simp_all)⟩
  | c + 1, σ, g, k, bx, m, hw, hmd, hk, hby, hn, hm, hc, hbc, hmc => by
    have hfit := modes_fit (mSCOPY, scopyN) scopy_mem (by decide)
    have hS := stepS_of_mode hw (by omega) hmd rfl hfit.1 hfit.2
      (scopy_byte hw bx n m om k (g (IN + bx)) hL hk (by omega) hby hn (by omega) rfl hm (by omega))
    have hw1 := (((hw.store (i := 2080 + n + m) (v := g (IN + bx)) (by omega) (by omega)).store
      (i := 1) (v := bx + 1) (by omega) (by omega)).store (i := 3) (v := m + 1) (by omega) (by omega)).store
      (i := 5) (v := k - 1) (by omega) (by omega)
    set g1 := Function.update (Function.update (Function.update (Function.update g (2080 + n + m) (g (IN + bx))) 1
      (bx + 1)) 3 (m + 1)) 5 (k - 1) with hg1
    have u : ∀ d : Int, d ≠ 2080 + n + m → d ≠ 1 → d ≠ 3 → d ≠ 5 → g1 d = g d := by
      intro d h1 h2 h3 h4; simp [hg1, Function.update_apply, h1, h2, h3, h4]
    obtain ⟨σ', hit, hw'⟩ := scopy_iter n om hL c _ g1 (k - 1) (bx + 1) (m + 1) hw1
      (by rw [u _ (by unfold cMODE; omega) (by unfold cMODE; omega) (by unfold cMODE; omega) (by unfold cMODE; omega)]
          exact hmd)
      (by simp [hg1, cPEND])
      (by show g1 1 = _; simp [hg1, Function.update_apply])
      (by rw [u _ (by unfold cN; omega) (by unfold cN; omega) (by unfold cN; omega) (by unfold cN; omega)]; exact hn)
      (by show g1 3 = _; simp [hg1, Function.update_apply])
      (by push_cast at hc ⊢; omega) (by omega) (by omega)
    have e1 : cwR g1 (2080 + ((bx + 1 : Nat) : Int)) (2080 + n + ((m + 1 : Nat) : Int)) c =
        Function.update (Function.update (Function.update (cwR g (2080 + bx) (2080 + n + m) (c + 1)) 1 (bx + 1)) 3 (m + 1))
          5 (k - 1) := by
      rw [hg1, cwR_update 5 _ c _ _ _ (by omega) (by omega), cwR_update 3 _ c _ _ _ (by omega) (by omega),
        cwR_update 1 _ c _ _ _ (by omega) (by omega)]
      simp only [cwR, show (IN : Int) = 2080 from rfl]
      push_cast
      ring_nf
    refine ⟨σ', by simp only [iterS, hS, Option.bind_some]; exact hit, world_congr hw' (fun i _ _ => ?_)⟩
    unfold scopyRel
    rw [e1]
    simp only [Function.update_apply, cPEND, cM, cBY]
    push_cast
    split_ifs <;> omega

/-! ## Refine₅ at SCOPY -/

theorem refine_scopy (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (σ : Store) (f : Int → Int)
    (hw : World σ p (L0 b.size om) f) (hs : Sole σ p (L0 b.size om)) (hi : Inv b om lit f) (hm : f cMODE = mSCOPY) :
    ∃ j σ', stepS₅ p σ = some σ' ∧ iterS p j σ = some σ' ∧ Sole σ' p (L0 b.size om) ∧
      (f cMODE ≠ mDONE → f cMODE ≠ mREJECT → 1 ≤ j) := by
  have hL0 : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hwf := wf_of_sole hw hs (by omega)
  have hc := hi.2.cur
  rw [hm] at hc
  simp only [facts, show mSCOPY = (10 : Int) by rfl, show ¬ ((10 : Int) = mSNLEN) by decide, if_false, if_true] at hc
  obtain ⟨hp0, hmo⟩ := hc
  have hsc := hi.2.scopy hm
  have hn := hi.1.n_eq
  have hom := hi.1.om_eq
  have hbr := hi.1.by_rng
  have hmr := hi.1.m_rng
  have hlk : modes₅.lookup (f cMODE) = some (scopyT₅.shift 0) := by rw [hm]; rfl
  have hfit := modes_fit (mSCOPY, scopyN) scopy_mem (by decide)
  by_cases hpd : f cPEND = 0
  · obtain ⟨σL, hstL, hwL, hsL⟩ := stepS₅_reex hw (by omega) hlk (F₀ := 5) (by omega)
      (P := fun σ' => World σ' p (L0 b.size om)
          (fun i => Function.update (fun a => f (a - p)) (p + cMODE) (if f cBF = 1 then mDONE else mHDR) (p + i)) ∧
        Sole σ' p (L0 b.size om))
      (fun F hF => by
        obtain ⟨a, h1, h2, h3, h4⟩ := scopy5_end_world p (L0 b.size om) f (f cBF) hpd rfl (by omega) hw hs hwf hF
        exact ⟨a, h1, h2, h3, h4⟩)
    have hS := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2 (scopy_end hw hL0 (f cBF) hpd rfl)
    have hwD := hw.store (i := 0) (v := if f cBF = 1 then 98 else 1) (by omega) (by omega)
    have hsD := stepS_sole hs hS
    have e := sole_world_eq' hwL hsL hwD hsD (fun i h0 h1 => by
      by_cases hb : f cBF = 1 <;> simp [Function.update_apply, cMODE, mDONE, mHDR, hb])
    subst e
    exact ⟨1, _, hstL, by simp [iterS, hS], hsL, fun _ _ => le_refl _⟩
  · have hpd0 : 0 < f cPEND := by omega
    obtain ⟨c, hcd⟩ : ∃ c : Int, c = min (f cPEND) CS := ⟨_, rfl⟩
    have hc32 : c ≤ 32 := by rw [hcd]; unfold CS; omega
    have hcp : c ≤ f cPEND := by rw [hcd]; omega
    have hc0 : 0 < c := by rw [hcd]; unfold CS; omega
    have hcT : (c.toNat : Int) = c := Int.toNat_of_nonneg (by omega)
    have hbxT : ((f cBY).toNat : Int) = f cBY := Int.toNat_of_nonneg hbr.1
    have hmT : ((f cM).toNat : Int) = f cM := Int.toNat_of_nonneg hmr.1
    have hcap : f cBY + min (f cPEND) CS ≤ b.size := by rw [← hcd]; omega
    have hbound : IN + (b.size : Int) + f cM + min (f cPEND) CS ≤ L0 b.size om := by
      rw [← hcd]; unfold IN L0; omega
    obtain ⟨σL, hstL, hwL, hsL⟩ := stepS₅_reex hw (by omega) hlk (F₀ := 4 * 32 + 13) (by omega)
      (P := fun σ' => World σ' p (L0 b.size om) (scopyPostRel p f (f cPEND) (f cBY) b.size (f cM)) ∧
        Sole σ' p (L0 b.size om))
      (fun F hF => by
        obtain ⟨a, h1, h2, h3, h4⟩ := scopy5_chunk_world p (L0 b.size om) f (f cPEND) (f cBY) b.size (f cM)
          rfl hpd0 rfl hn rfl hbr.1 hmr.1 hcap hbound hw hs hwf (F := F) (by rw [← hcd]; omega)
        exact ⟨a, h1, h2, h3, h4⟩)
    obtain ⟨σD, hit, hwD⟩ := scopy_iter b.size om (by unfold L0; omega) c.toNat σ f (f cPEND) (f cBY).toNat (f cM).toNat
      hw hm rfl (by rw [hbxT]) hn (by rw [hmT]) (by rw [hcT]; exact hcp) (by omega) (by omega)
    have hsD := iterS_sole _ σ σD hs hit
    have e := sole_world_eq' hwL hsL hwD hsD (fun i h0 h1 => by
      simp only [scopyRel, scopyPostRel, scopyPost]
      simp only [← hcd, hbxT, hmT]
      simp only [Function.update_apply, cwF_rel, hcT, hbxT, hmT, cPEND, cM, cBY, IN, show p + i - p = i by omega,
        show (p + i = p + 1) = (i = 1) by simp, show (p + i = p + 3) = (i = 3) by simp,
        show (p + i = p + 5) = (i = 5) by simp]
      try (split_ifs <;> first | omega | rfl))
    subst e
    exact ⟨c.toNat, _, hstL, hit, hsL, fun _ _ => by omega⟩

end VIRL5
