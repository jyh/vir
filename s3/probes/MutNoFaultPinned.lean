-- MUTANT (ERRATA-NOCHECK E1, red backwards): NC-P as PINNED, without E1's second conjunct. Expected: word_no_fault FAILS.
/-
  O95 option (iv), OBJECT-NOCHECK NC-W (fork N1 (a), with ERRATA-NOCHECK E1's premise NC-P′). Under compile_refines' premises
  and NC-P′, no word run of the S2 image from its start reaches `.fault`. DERIVED, whole-run, from compile_refines' clauses (1)
  and (3), `src_classify` and the determinism of `stepW`; nothing under compiler/VIRC is edited (amend-26 NC1).
-/
import VIRC.Compose
import VIRC.Converse

namespace S3Mut
open VIRC VIRL1 VIRL2

/-- **NC-P′** (ERRATA-NOCHECK E1): no reachable configuration of the source run faults, and every reached `ret a` has an atom
    that evaluates. Every L2 `Triple` supplies both at a state satisfying its precondition. -/
def NoFaultP (vs : List Atom₂) (e : Tm₂) (σ : Store) : Prop :=
  (∀ c, Steps₂ (instL 0 vs e, σ) c → ¬ Faults c) ∧ True

/-- **word_no_fault (NC-W).** Under compile_refines' premises and NC-P′, no word run from the S2 image's start reaches FAULT. -/
theorem word_no_fault {lay σ m} (Γ₀ : Ctx S₂) (Δ₀ : List Bool) (e : Tm₂) (τ : Ty₂) (vs : List Atom₂) (ρw₀ : List W)
    (hty : HasType₂ Γ₀ Δ₀ e τ) (hw : Tm.wfB Γ₀.length e = true) (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true)
    (hlen : vs.length = Γ₀.length) (hg : Good vs) (hT : (lower2T Γ₀ e []).2.length < 2 ^ 64)
    (he : EnvRel (lower2T Γ₀ e []).2 lay σ Γ₀ (vs.map valOf) ρw₀) (hl : Layout σ lay) (hm : MemRel lay σ m)
    (hP : NoFaultP vs e σ) {k : Nat} {Wf : WSt × WMem}
    (hW : WN (lower2T Γ₀ e []).2 k (.run (lower2T Γ₀ e []).1 ρw₀ [], m) Wf) : Wf.1 ≠ .fault := by
  intro hfault
  obtain ⟨c1, -, c3⟩ := compile_refines Γ₀ Δ₀ e τ vs ρw₀ hty hw hf hok hlen hg hT he hl hm
  obtain ⟨wst, wm⟩ := Wf
  simp only at hfault
  subst hfault
  have hstop : stepW (lower2T Γ₀ e []).2 (.fault, wm) = none := rfl
  -- any run from the start that ends stopped ends at the FAULT state itself
  have same : ∀ {k' W'}, WN (lower2T Γ₀ e []).2 k' (.run (lower2T Γ₀ e []).1 ρw₀ [], m) W' →
      stepW (lower2T Γ₀ e []).2 W' = none → W' = (.fault, wm) := by
    intro k' W' hW' hs'
    obtain ⟨-, hr⟩ := WN.det_stuck hW hstop hW'
    exact (WN.from_stopped hr hs').2.symm
  rcases src_classify (instL 0 vs e, σ) (k + 1) with ⟨c', hn⟩ | ⟨k₀, c', -, hn, hst⟩
  · obtain ⟨k', W', hW', hor⟩ := c3 (k + 1) c' hn
    obtain ⟨hle, -⟩ := WN.det_stuck hW hstop hW'
    rcases hor with h | h
    · omega
    · obtain ⟨wst', wm'⟩ := W'
      simp only at h
      subst h
      exact absurd (same hW' rfl) (by simp)
  · obtain ⟨ce, cσ⟩ := c'
    by_cases hterm : ce.IsTerminal
    · cases ce with
      | ret a =>
        obtain ⟨w, hw'⟩ := Option.isSome_iff_exists.1 (hP.2 a cσ (SrcN.to_steps hn))
        obtain ⟨k', W', hW', hr⟩ := c1 a cσ w (SrcN.to_steps hn) hw'
        rcases hr with ⟨ws, m', rfl, -⟩ | h
        · exact absurd (same hW' rfl) (by simp)
        · obtain ⟨wst', wm'⟩ := W'
          simp only at h
          subst h
          exact absurd (same hW' rfl) (by simp)
      | _ => simp [Tm.IsTerminal] at hterm
    · exact hP.1 _ (SrcN.to_steps hn) ⟨hterm, hst⟩

end S3Mut
