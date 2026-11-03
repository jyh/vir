/-
  O95 layer L2, Lean arm. The triples inputs/L2-programs.md names for M1–M4, proved from the rules (no unfolding of ⟶₂ in
  M1/M2/M4's positive triples), and M3's and M4's negative facts, proved from runs.
-/
import VIRL2.Regions
import VIRL2.Programs

namespace VIRL2
open VIRL1

theorem ret_rule' {P : Assn} {a v : Atom₂} {Q : Atom₂ → Assn} (hv : a.eval = some v) (hP : ∀ σ, P σ → Q v σ) :
    Triple P (.ret a) Q :=
  conseq hP (fun _ _ h => h) (ret_rule hv)

/-- `{emp} M1 {v. ⌜v = 7⌝}`. -/
theorem M1_triple : Triple Assn.emp M1 (fun v σ => v = ci 7 ∧ σ = Store.empty) := by
  unfold M1
  refine letOp_rule rfl (alloc_axiom 4 (by decide)) (fun v => pre_ex (fun p => pre_pure (fun hv => ?_)))
  subst hv
  simp only [Tm.subst, Atom.subst, Atom.substL]
  refine letOp_rule rfl (store_at p _ _ 2 7 (by simp)) (fun c => pre_pure (fun hc => ?_))
  subst hc
  simp only [Tm.subst, Atom.subst, Atom.substL]
  refine letOp_rule rfl (load_at p _ _ 2 (by simp)) (fun v => pre_pure (fun hv => ?_))
  subst hv
  simp only [Tm.subst, Atom.subst, Atom.substL]
  refine letOp_rule rfl (free_at p _ _) (fun u => pre_pure (fun hu => ?_))
  subst hu
  simp only [Tm.subst]
  refine ret_rule' (v := ci 7) ?_ (fun σ h => ⟨rfl, h⟩)
  simp [Atom.subst, Atom.eval, Function.update_self]

/-! ## The separation-algebra moves the programs need, proved from the definitions. -/
theorem store_empty_union_right (σ : Store) : σ ⊎ Store.empty = σ := by
  simp [Store.empty, Store.union, Finmap.union_empty]

theorem disj_empty_left (σ : Store) : Store.Disj Store.empty σ := ⟨Finmap.disjoint_empty _, Finmap.disjoint_empty _⟩

theorem disj_symm {σ₁ σ₂ : Store} (h : Store.Disj σ₁ σ₂) : Store.Disj σ₂ σ₁ :=
  ⟨Finmap.Disjoint.symm _ _ h.1, Finmap.Disjoint.symm _ _ h.2⟩

theorem union_comm_disj {σ₁ σ₂ : Store} (h : Store.Disj σ₁ σ₂) : σ₁ ⊎ σ₂ = σ₂ ⊎ σ₁ := by
  simp [Store.union, Finmap.union_comm_of_disjoint h.1, Finmap.union_comm_of_disjoint h.2]

theorem emp_sep {R : Assn} {σ} (h : R σ) : (Assn.emp ∗ R) σ :=
  ⟨Store.empty, σ, disj_empty_left σ, (Store.empty_union σ).symm, rfl, h⟩

theorem sep_emp_inv {R : Assn} {σ} (h : ((fun σ => σ = Store.empty) ∗ R) σ) : R σ := by
  obtain ⟨σ₁, σ₂, -, rfl, rfl, h⟩ := h; rwa [Store.empty_union]

theorem sep_comm {P R : Assn} {σ} (h : (P ∗ R) σ) : (R ∗ P) σ := by
  obtain ⟨σ₁, σ₂, hd, rfl, hP, hR⟩ := h
  exact ⟨σ₂, σ₁, disj_symm hd, union_comm_disj hd, hR, hP⟩

theorem sep_pure_left {φ : Prop} {P R : Assn} {σ} (h : ((fun σ => φ ∧ P σ) ∗ R) σ) : φ ∧ (P ∗ R) σ := by
  obtain ⟨σ₁, σ₂, hd, rfl, ⟨hφ, hP⟩, hR⟩ := h; exact ⟨hφ, σ₁, σ₂, hd, rfl, hP, hR⟩

theorem sep_ex_pure_left {α : Type} {φ : α → Prop} {P : α → Assn} {R : Assn} {σ}
    (h : ((fun σ => ∃ x, φ x ∧ P x σ) ∗ R) σ) : ∃ x, φ x ∧ (P x ∗ R) σ := by
  obtain ⟨σ₁, σ₂, hd, rfl, ⟨x, hφ, hP⟩, hR⟩ := h; exact ⟨x, hφ, σ₁, σ₂, hd, rfl, hP, hR⟩

theorem op_conseq {P P' : Assn} {o vs} {Q Q' : Atom₂ → Assn} (hP : ∀ σ, P' σ → P σ) (hQ : ∀ v σ, Q v σ → Q' v σ)
    (h : OpTriple P o vs Q) : OpTriple P' o vs Q' := by
  intro σ σf hp hd hwf
  obtain ⟨v, σq, h₁, h₂, h₃, h₄⟩ := h σ σf (hP σ hp) hd hwf
  exact ⟨v, σq, h₁, h₂, h₃, hQ v σq h₄⟩

theorem pre_conseq {P P' : Assn} {e} {Q : Atom₂ → Assn} (hP : ∀ σ, P' σ → P σ) (h : Triple P e Q) : Triple P' e Q :=
  conseq hP (fun _ _ h => h) h

/-- `{emp} M2 {v. ⌜v = 5⌝}`. Its `store(b, 0, 9)` step is DERIVED BY THE FRAME RULE (`op_frame`) from `store_at` on b's
  region, with region a, already holding 5, as the frame R (inputs/L2-programs.md M2). -/
theorem M2_triple : Triple Assn.emp M2 (fun v σ => v = ci 5 ∧ σ = Store.empty) := by
  unfold M2
  refine letOp_rule rfl (alloc_axiom 2 (by decide)) (fun v => pre_ex (fun a => pre_pure (fun hv => ?_)))
  subst hv; simp only [Tm.subst, Atom.subst, Atom.substL]
  refine pre_conseq (fun σ h => emp_sep h) ?_
  refine letOp_rule rfl (op_frame _ (alloc_axiom 2 (by decide))) (fun v => ?_)
  refine pre_conseq (fun σ h => sep_ex_pure_left h) (pre_ex (fun b => pre_pure (fun hv => ?_)))
  subst hv; simp only [Tm.subst, Atom.subst, Atom.substL]
  refine pre_conseq (fun σ h => sep_comm h) ?_
  refine letOp_rule rfl (op_frame _ (store_at a _ _ 0 5 (by simp))) (fun c => ?_)
  refine pre_conseq (fun σ h => sep_pure_left h) (pre_pure (fun hc => ?_))
  subst hc; simp only [Tm.subst, Atom.subst, Atom.substL]
  -- THE FRAME STEP: store on b, with a's region (holding 5) as the frame.
  refine pre_conseq (fun σ h => sep_comm h) ?_
  refine letOp_rule rfl (op_frame _ (store_at b _ _ 0 9 (by simp))) (fun c => ?_)
  refine pre_conseq (fun σ h => sep_pure_left h) (pre_pure (fun hc => ?_))
  subst hc; simp only [Tm.subst, Atom.subst, Atom.substL]
  refine pre_conseq (fun σ h => sep_comm h) ?_
  refine letOp_rule rfl (op_frame _ (load_at a _ _ 0 (by simp))) (fun x => ?_)
  refine pre_conseq (fun σ h => sep_pure_left h) (pre_pure (fun hx => ?_))
  subst hx; simp only [Tm.subst, Atom.subst, Atom.substL]
  refine letOp_rule rfl (op_frame _ (free_at a _ _)) (fun u => ?_)
  refine pre_conseq (fun σ h => sep_pure_left h) (pre_pure (fun hu => ?_))
  subst hu; simp only [Tm.subst, Atom.subst, Atom.substL]
  refine pre_conseq (fun σ h => sep_emp_inv h) ?_
  refine letOp_rule rfl (free_at b _ _) (fun u => pre_pure (fun hu => ?_))
  subst hu; simp only [Tm.subst]
  refine ret_rule' (v := ci 5) ?_ (fun σ h => ⟨rfl, h⟩)
  simp [Atom.subst, Atom.eval, Function.update_self]

theorem wf_empty : Store.WF Store.empty where
  pos _ _ h := by simp [Store.empty, Finmap.lookup_empty] at h
  disj _ _ _ _ h := by simp [Store.empty, Finmap.lookup_empty] at h
  domH a := by simp [Store.empty, Finmap.lookup_empty, Finmap.notMem_empty]

/-- M3: NO triple holds — `¬ {emp} M3 {v. True}`: from σ₀ it reaches the out-of-bounds load, which FAULTS. -/
theorem M3_no_triple : ¬ Triple Assn.emp M3 (fun _ _ => True) := by
  intro h
  have hs := (h Store.empty Store.empty rfl (disj_empty_left _) (by rw [Store.empty_union]; exact wf_empty)).1
  rw [Store.empty_union] at hs
  apply hs _ (run₂_steps 20 _)
  refine ⟨by rw [M3_stuck]; exact id, fun c' hc => ?_⟩
  have he : run₂ 20 (M3, Store.empty) = ((run₂ 20 (M3, Store.empty)).1, (run₂ 20 (M3, Store.empty)).2) := rfl
  rw [he, M3_stuck] at hc
  obtain ⟨vs, v, σ', h₁, h₂, -⟩ := step₂_letOp_inv hc
  cases h₁
  have hnone : opStep .load [.const (.cap 0), ci 2] (run₂ 20 (M3, Store.empty)).2 = none := rfl
  rw [hnone] at h₂; cases h₂

/-- M4 does not fault and its leak is visible: `{emp} M4 {v. ⌜v = 0⌝ ∗ region(_, 1)}` holds … -/
theorem M4_triple : Triple Assn.emp M4 (fun v σ => v = ci 0 ∧ ∃ p, IsRegion p 1 σ) := by
  unfold M4
  refine letOp_rule rfl (alloc_axiom 1 (by decide)) (fun v => pre_ex (fun p => pre_pure (fun hv => ?_)))
  subst hv; simp only [Tm.subst]
  exact ret_rule' (v := ci 0) rfl (fun σ h => ⟨rfl, p, h.isRegion⟩)

/-- … and `{emp} M4 {v. ⌜v = 0⌝}` does NOT: the region is still live at the `ret`. -/
theorem M4_leak : ¬ Triple Assn.emp M4 (fun v σ => v = ci 0 ∧ σ = Store.empty) := by
  intro h
  have hp := (h Store.empty Store.empty rfl (disj_empty_left _) (by rw [Store.empty_union]; exact wf_empty)).2
  rw [Store.empty_union] at hp
  have he : run₂ 20 (M4, Store.empty) = (.ret (ci 0), (run₂ 20 (M4, Store.empty)).2) := by
    rw [← M4_run]
  have hst := run₂_steps 20 (M4, Store.empty)
  rw [he] at hst
  obtain ⟨v, σq, -, -, hσ, -, -, rfl⟩ := hp _ _ hst
  have hR : ((run₂ 20 (M4, Store.empty)).2.R.lookup 0) = some 1 := rfl
  rw [hσ, Store.empty_union] at hR
  simp [Store.empty, Finmap.lookup_empty] at hR

end VIRL2
