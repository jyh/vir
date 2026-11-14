/-
  O95 layer L5, Lean arm (STATUS 321, LV8 assembly, LV8-MAP Addendum 5): Refine₅ at REP, the template for a chunked mode. The
  ⟶₅ step writes c = min(PEND, 32) lengths in one fillR call (rep5_chunk_world); DEFLATE writes one per step (rep_byte), so c
  DEFLATE steps reach the same contents (`rep_iter`), and World ∧ Sole make the two stores one (`sole_world_eq'`). At PEND = 0
  both take DEFLATE's own end branch (MODE := LENS), j = 1. Beside it: Sole ∧ World give WF, and `iterS` keeps Sole.
-/
import VIRL5.Reex5
import VIRL5.RefineLift5
import VIRL5.Rep5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- A Sole world is well formed. -/
theorem wf_of_sole {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hs : Sole σ p L) (hL : 0 < L) :
    Store.WF σ := by
  have hR := hs.1
  refine ⟨fun q n h => ?_, fun q r n m hq hr hqr a _ _ => ?_, fun a => ⟨fun ha => ?_, fun ⟨q, n, hq, ha⟩ => ?_⟩⟩
  · rw [hR] at h
    by_cases e : q = p
    · subst e; rw [Finmap.lookup_singleton_eq] at h; simp at h; omega
    · have : (Finmap.singleton p L : Finmap (fun _ : Int => Nat)).lookup q = none := by
        rw [Finmap.lookup_eq_none, Finmap.mem_singleton]; exact e
      rw [this] at h; simp at h
  · have hq' : q = p := by
      rw [hR] at hq; by_contra e
      have : (Finmap.singleton p L : Finmap (fun _ : Int => Nat)).lookup q = none := by
        rw [Finmap.lookup_eq_none, Finmap.mem_singleton]; exact e
      rw [this] at hq; simp at hq
    have hr' : r = p := by
      rw [hR] at hr; by_contra e
      have : (Finmap.singleton p L : Finmap (fun _ : Int => Nat)).lookup r = none := by
        rw [Finmap.lookup_eq_none, Finmap.mem_singleton]; exact e
      rw [this] at hr; simp at hr
    exact hqr (hq'.trans hr'.symm)
  · refine ⟨p, L, by rw [hR]; exact Finmap.lookup_singleton_eq, ?_⟩
    by_contra hn
    have := hs.2 a hn
    rw [Finmap.lookup_eq_none] at this
    exact this ha
  · have hq' : q = p := by
      rw [hR] at hq; by_contra e
      have : (Finmap.singleton p L : Finmap (fun _ : Int => Nat)).lookup q = none := by
        rw [Finmap.lookup_eq_none, Finmap.mem_singleton]; exact e
      rw [this] at hq; simp at hq
    subst hq'
    rw [hR, Finmap.lookup_singleton_eq] at hq
    simp only [Option.some.injEq] at hq
    subst hq
    simp only [Store.InRegion] at ha
    have h1 : σ.H.lookup (q + (a - q)) = some (f (a - q)) := hw.cell (a - q) (by omega) (by omega)
    rw [show q + (a - q) = a by omega] at h1
    exact Finmap.mem_of_lookup_eq_some h1

/-- World only reads the region: functions that agree there are interchangeable. -/
theorem world_congr {σ : Store} {p : Int} {L : Nat} {f g : Int → Int} (hw : World σ p L f)
    (h : ∀ i : Int, 0 ≤ i → i < L → f i = g i) : World σ p L g :=
  ⟨hw.reg, fun i h0 hL => by rw [← h i h0 hL]; exact hw.cell i h0 hL⟩

/-- `iterS` keeps a store Sole. -/
theorem iterS_sole {p : Int} {L : Nat} : ∀ (j : Nat) (σ σ' : Store), Sole σ p L → iterS p j σ = some σ' → Sole σ' p L
  | 0, σ, σ', hs, h => by simp only [iterS, Option.some.injEq] at h; subst h; exact hs
  | j + 1, σ, σ', hs, h => by
    simp only [iterS] at h
    rcases hst : stepS p σ with _ | σ1
    · rw [hst] at h; simp at h
    · rw [hst, Option.bind_some] at h
      exact iterS_sole j σ1 σ' (stepS_sole hs hst) h

/-! ## REP's end branch over ⟶₅: cost, run, World -/

theorem rep5_end_cost (p : Int) (L : Nat) (g : Int → Int) (hpd : g (p + cPEND) = 0) (hL : 6 ≤ L) :
    Cost₅ (RegionAt p L g) (repT₅.subst 0 (.const (.cap p))) 3 := by
  simp [repT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_letOp₅ (cs := [.cap p, .int cPEND]) (by simp [Atom₅.evalL, Atom₅.eval])
    (load_at p L g cPEND ⟨by unfold cPEND; omega, by unfold cPEND; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hpd]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine cost_ite₅ (b := true) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
  simp only [if_true]
  refine cost_letOp₅ (cs := [.cap p, .int cMODE, .int mLENS]) (by simp [Atom₅.evalL, Atom₅.eval])
    (store_at p L g cMODE mLENS ⟨by unfold cMODE; omega, by unfold cMODE; omega⟩) (fun w => ?_)
  refine cost_pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact cost_ret₅ _ _

theorem rep5_end_world (p : Int) (L : Nat) (f : Int → Int) (hpd : f cPEND = 0) (hL : 6 ≤ L)
    {σ : Store} (hw : World σ p L f) (hs : Sole σ p L) (hwf : Store.WF σ) {F : Nat} (hF : 3 ≤ F) :
    ∃ a, ((run₅ F (repT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
          (run₅ F (repT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧
      a.eval = some (.const (.cap p)) ∧
      World (run₅ F (repT₅.subst 0 (.const (.cap p)), σ)).2 p L
        (fun i => Function.update (fun a => f (a - p)) (p + cMODE) mLENS (p + i)) ∧
      Sole (run₅ F (repT₅.subst 0 (.const (.cap p)), σ)).2 p L := by
  have hR := VIRL5.World.regionAt hw hs
  have hpd' : (fun a => f (a - p)) (p + cPEND) = 0 := by simpa using hpd
  obtain ⟨v, qs, ⟨hv, hqs, hreg⟩, hcase⟩ :=
    run_of_triple₅ (rep5_end p L _ hpd' hL) (rep5_end_cost p L _ hpd' hL) hR hwf hF
  subst hv
  subst hqs
  obtain ⟨hw', hs'⟩ := VIRL5.RegionAt.world hreg
  rcases hcase with ⟨a, ha, hav, -⟩ | ⟨a, ds', ha, hav, hds'⟩
  · exact ⟨a, Or.inl ha, hav, hw', hs'⟩
  · have hl := evalL_length hds'
    have hd : ds' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst hd
    exact ⟨a, Or.inr ha, hav, hw', hs'⟩

/-! ## REP over DEFLATE, c steps -/

/-- DEFLATE's contents after c REP steps, relative to the base. -/
def repRel (f : Int → Int) (pd fl la n om : Int) (c : Nat) : Int → Int :=
  Function.update (Function.update
    (fun i => if 2080 + n + om + fl ≤ i ∧ i < 2080 + n + om + fl + c then la else f i) cFILL (fl + c)) cPEND (pd - c)

theorem rep_mem : (mREP, repN) ∈ modes := by simp [modes]

/-- **c DEFLATE REP steps**, each `rep_byte` through `stepS_of_mode`. -/
theorem rep_iter {p : Int} {L : Nat} (hL : 2080 ≤ L) (la n om : Int) : ∀ (c : Nat) (σ : Store) (g : Int → Int) (pd fl : Int),
    World σ p L g → g cMODE = mREP → g cPEND = pd → g cFILL = fl → g cLAST = la → g cN = n → g cOUTMAX = om →
    (c : Int) ≤ pd → 2080 ≤ 2080 + n + om + fl → 2080 + n + om + fl + c ≤ L →
    ∃ σ', iterS p c σ = some σ' ∧ World σ' p L (repRel g pd fl la n om c)
  | 0, σ, g, pd, fl, hw, _, hpd, hfl, _, _, _, _, _, _ =>
    ⟨σ, rfl, world_congr hw (fun i _ _ => by
      unfold repRel
      simp only [Function.update_apply, Nat.cast_zero, add_zero, sub_zero]
      split_ifs with h1 h2 h3 <;> (try subst_vars) <;> first | omega | simp_all)⟩
  | c + 1, σ, g, pd, fl, hw, hm, hpd, hfl, hla, hn, hom, hc, ha0, haL => by
    have hfit := modes_fit (mREP, repN) rep_mem (by decide)
    have hS := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
      (rep_byte hw hL pd fl la n om hpd (by omega) hfl hla hn hom (by omega) (by omega))
    set a : Int := 2080 + n + om + fl with had
    have hw1 := ((hw.store (i := a) (v := la) (by omega) (by omega)).store (i := 10) (v := fl + 1) (by omega) (by omega)).store
      (i := 5) (v := pd - 1) (by omega) (by omega)
    set g1 := Function.update (Function.update (Function.update g a la) 10 (fl + 1)) 5 (pd - 1) with hg1
    have u : ∀ d : Int, d ≠ a → d ≠ 10 → d ≠ 5 → g1 d = g d := by
      intro d h1 h2 h3; simp [hg1, Function.update_apply, h1, h2, h3]
    obtain ⟨σ', hit, hw'⟩ := rep_iter hL la n om c _ g1 (pd - 1) (fl + 1) hw1
      (by rw [u _ (by unfold cMODE; omega) (by unfold cMODE; omega) (by unfold cMODE; omega)]; exact hm)
      (by simp [hg1, cPEND])
      (by show g1 10 = fl + 1; simp [hg1, Function.update_apply])
      (by rw [u _ (by unfold cLAST; omega) (by unfold cLAST; omega) (by unfold cLAST; omega)]; exact hla)
      (by rw [u _ (by unfold cN; omega) (by unfold cN; omega) (by unfold cN; omega)]; exact hn)
      (by rw [u _ (by unfold cOUTMAX; omega) (by unfold cOUTMAX; omega) (by unfold cOUTMAX; omega)]; exact hom)
      (by push_cast at hc ⊢; omega) (by omega) (by push_cast at haL ⊢; omega)
    refine ⟨σ', by simp only [iterS, hS, Option.bind_some]; exact hit, world_congr hw' (fun i _ _ => ?_)⟩
    simp only [repRel, hg1, Function.update_apply, cPEND, cFILL]
    push_cast
    split_ifs <;> omega

/-! ## Refine₅ at REP -/

/-- Two Sole worlds whose contents agree on the region are one store. -/
theorem sole_world_eq' {σ σ' : Store} {p : Int} {L : Nat} {f f' : Int → Int}
    (hw : World σ p L f) (hs : Sole σ p L) (hw' : World σ' p L f') (hs' : Sole σ' p L)
    (h : ∀ i : Int, 0 ≤ i → i < L → f' i = f i) : σ = σ' :=
  sole_world_eq hw hs (world_congr hw' h) hs'

theorem refine_rep (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (σ : Store) (f : Int → Int)
    (hw : World σ p (L0 b.size om) f) (hs : Sole σ p (L0 b.size om)) (hi : Inv b om lit f) (hm : f cMODE = mREP) :
    ∃ j σ', stepS₅ p σ = some σ' ∧ iterS p j σ = some σ' ∧ Sole σ' p (L0 b.size om) ∧
      (f cMODE ≠ mDONE → f cMODE ≠ mREJECT → 1 ≤ j) := by
  have hL0 : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hwf := wf_of_sole hw hs (by omega)
  have hc := hi.2.cur
  rw [hm, facts_rep] at hc
  obtain ⟨hf0, hp0, hfp, hhl, hhd, -, -, -⟩ := hc
  have hn := hi.1.n_eq
  have hom := hi.1.om_eq
  have hlk : modes₅.lookup (f cMODE) = some (repT₅.shift 0) := by rw [hm]; rfl
  have hfit := modes_fit (mREP, repN) rep_mem (by decide)
  by_cases hpd : f cPEND = 0
  · -- the run's end: DEFLATE's own branch, j = 1
    obtain ⟨σL, hstL, hwL, hsL⟩ := stepS₅_reex hw (by omega) hlk (F₀ := 3) (by omega)
      (P := fun σ' => World σ' p (L0 b.size om) (fun i => Function.update (fun a => f (a - p)) (p + cMODE) mLENS (p + i)) ∧
        Sole σ' p (L0 b.size om))
      (fun F hF => by
        obtain ⟨a, h1, h2, h3, h4⟩ := rep5_end_world p (L0 b.size om) f hpd (by omega) hw hs hwf hF
        exact ⟨a, h1, h2, h3, h4⟩)
    have hS := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2 (rep_end hw hL0 hpd)
    have hwD := hw.store (i := 0) (v := 12) (by omega) (by omega)
    have hsD := stepS_sole hs hS
    have e := sole_world_eq' hwL hsL hwD hsD (fun i h0 h1 => by
      simp [Function.update_apply, cMODE, mLENS])
    subst e
    exact ⟨1, _, hstL, by simp [iterS, hS], hsL, fun _ _ => le_refl _⟩
  · -- one chunk: c = min(PEND, 32) DEFLATE steps
    have hpd0 : 0 < f cPEND := by omega
    obtain ⟨c, hcd⟩ : ∃ c : Int, c = min (f cPEND) CS := ⟨_, rfl⟩
    have hc32 : c ≤ 32 := by rw [hcd]; unfold CS; omega
    have hcp : c ≤ f cPEND := by rw [hcd]; omega
    have hc0 : 0 < c := by rw [hcd]; unfold CS; omega
    have hcT : (c.toNat : Int) = c := Int.toNat_of_nonneg (by omega)
    have hbound' : 2080 + (b.size : Int) + om + f cFILL + c ≤ L0 b.size om := by unfold L0; omega
    have hbound : IN + (b.size : Int) + om + f cFILL + min (f cPEND) CS ≤ L0 b.size om := by
      rw [← hcd]; unfold IN; omega
    obtain ⟨σL, hstL, hwL, hsL⟩ := stepS₅_reex hw (by omega) hlk (F₀ := 3 * 32 + 13) (by omega)
      (P := fun σ' => World σ' p (L0 b.size om) (repPostRel p f (f cPEND) (f cFILL) (f cLAST) b.size om) ∧
        Sole σ' p (L0 b.size om))
      (fun F hF => by
        obtain ⟨a, h1, h2, h3, h4⟩ := rep5_chunk_world p (L0 b.size om) f (f cPEND) (f cFILL) (f cLAST) b.size om
          rfl hpd0 rfl rfl hn hom hf0 (by omega) (by omega) hbound hw hs hwf (F := F)
          (by rw [← hcd]; omega)
        exact ⟨a, h1, h2, h3, h4⟩)
    obtain ⟨σD, hit, hwD⟩ := rep_iter hL0 (f cLAST) b.size om c.toNat σ f (f cPEND) (f cFILL) hw hm rfl rfl rfl hn hom
      (by rw [hcT]; exact hcp) (by omega) (by rw [hcT]; exact hbound')
    have hsD := iterS_sole _ σ σD hs hit
    have e := sole_world_eq' hwL hsL hwD hsD (fun i h0 h1 => by
      simp only [repRel, repPostRel, repPost, fillF]
      simp only [← hcd]
      simp only [fillF, Function.update_apply, hcT, cPEND, cFILL, IN, show p + i - p = i by omega]
      split_ifs <;> omega)
    subst e
    exact ⟨c.toNat, _, hstL, hit, hsL, fun _ _ => by omega⟩

end VIRL5
