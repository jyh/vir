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

end VIRL2
