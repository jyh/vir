/-
  O95 compiler, stage S2: the stage theorem `s2_refines` (compiler/DECLARATIONS-S2.md, with the fault clause as corrected in
  STAGE-S2.md BEFORE this file existed). It relates the IR run of S1's image of a typed, accepted program to the word-machine run
  of S2's image of the SAME program, lock-step, for every layout satisfying the premise. The word machine never finishes with an
  unrelated value: it finishes with the related words, or it reaches a declared exit (FAULT, or OVERFLOW where an int left the
  range).
-/
import VIRC.Sim2

namespace VIRC
open VIRL1 VIRL2

theorem WN.trans {tbl : Table} : ∀ {m n s s' s''}, WN tbl m s s' → WN tbl n s' s'' → WN tbl (m + n) s s''
  | _, _, _, _, _, .refl _, h => by simpa using h
  | _, _, _, _, _, .step h₁ h₂, h => by
      have := WN.step h₁ (WN.trans h₂ h); simpa [Nat.add_right_comm] using this

/-- The run simulation: n IR steps are matched by n word steps to a related state, or the word machine stops at OVF within
those n steps. -/
theorem s2_run {T lay τfin} (hT : T.length < 2 ^ 64) : ∀ {n I I' Wst}, SRel T lay τfin I Wst → IRN n I I' →
    ∃ m W', WN T m Wst W' ∧ ((m = n ∧ SRel T lay τfin I' W') ∨ (m ≤ n ∧ W'.1 = .ovf))
  | _, _, _, Wst, h, .refl _ => ⟨0, Wst, .refl _, .inl ⟨rfl, h⟩⟩
  | _, I, _, Wst, h, .step hs hrest => by
      obtain ⟨st, σ⟩ := I
      cases st with
      | done v => simp [stepIR] at hs
      | run c ρ k =>
        rcases sim2_step hT h with ⟨hnone, _⟩ | ⟨I₁, h1, W₁, hW, rel⟩
        · rw [hnone] at hs; cases hs
        · rw [h1] at hs; cases hs
          rcases rel with rel | ovf
          · obtain ⟨m, W', hw, r⟩ := s2_run hT rel hrest
            refine ⟨m + 1, W', .step hW hw, ?_⟩
            rcases r with ⟨rfl, r⟩ | ⟨hle, r⟩
            · exact .inl ⟨rfl, r⟩
            · exact .inr ⟨by omega, r⟩
          · exact ⟨1, W₁, .step hW (.refl _), .inr ⟨by omega, ovf⟩⟩

/-- The initial relation, for a program e typed under the caller's context Γ₀, its parameters in related environments, and a
layout satisfying the premise. The code table is the program's own (`lower2T Γ₀ e []`). -/
theorem s2_init {lay σ m} (Γ₀ : Ctx S₂) (Δ₀ : List Bool) (e : Tm₂) (τ : Ty₂) (ρ₀ : List VIRC.Val) (ρw₀ : List W)
    (hty : HasType₂ Γ₀ Δ₀ e τ) (hw : Tm.wfB Γ₀.length e = true) (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true)
    (he : EnvRel (lower2T Γ₀ e []).2 lay σ Γ₀ ρ₀ ρw₀) (hl : Layout σ lay) (hm : MemRel lay σ m) :
    SRel (lower2T Γ₀ e []).2 lay τ (.run (lowerT e) ρ₀ [], σ) (.run (lower2T Γ₀ e []).1 ρw₀ [], m) :=
  .run ⟨e, Γ₀, Δ₀, [], rfl, rfl, ⟨le_refl _, fun _ _ _ => rfl⟩, hty, hw, fun _ _ => rfl, hf, hok, he⟩ .nil hl hm

/-- **S2.** For a ⊢₂-typed program accepted by C2 and S2's predicate (closed below its caller context Γ₀, no alloc/free, constants
in range), whose code table has fewer than 2⁶⁴ entries, with its caller parameters related (`EnvRel`) and a layout satisfying the
premise (`Layout`, `MemRel`):
(1) an IR run that FINISHES with v is matched by a word run that finishes with words related to v (`VRel`, at the final store),
    or that reaches OVERFLOW;
(2) an IR run that is STUCK is matched by a word run that reaches the FAULT exit or the OVERFLOW exit;
(3) n IR steps are matched by exactly n word steps, or by an earlier stop at OVERFLOW (lock-step; divergence is kept unless an
    int leaves the range).
On no run does the word machine finish with an unrelated value. -/
theorem s2_refines {lay σ m} (Γ₀ : Ctx S₂) (Δ₀ : List Bool) (e : Tm₂) (τ : Ty₂) (ρ₀ : List VIRC.Val) (ρw₀ : List W)
    (hty : HasType₂ Γ₀ Δ₀ e τ) (hw : Tm.wfB Γ₀.length e = true) (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true)
    (hT : (lower2T Γ₀ e []).2.length < 2 ^ 64)
    (he : EnvRel (lower2T Γ₀ e []).2 lay σ Γ₀ ρ₀ ρw₀) (hl : Layout σ lay) (hm : MemRel lay σ m) :
    let T := (lower2T Γ₀ e []).2
    let I₀ : St × Store := (.run (lowerT e) ρ₀ [], σ)
    let W₀ : WSt × WMem := (.run (lower2T Γ₀ e []).1 ρw₀ [], m)
    (∀ n v σ', IRN n I₀ (.done v, σ') →
      ∃ k W', WN T k W₀ W' ∧ ((∃ ws m', W' = (.done ws, m') ∧ VRel T lay σ' τ v ws) ∨ W'.1 = .ovf)) ∧
    (∀ n c ρ k σ', IRN n I₀ (.run c ρ k, σ') → stepIR (.run c ρ k, σ') = none →
      ∃ j W', WN T j W₀ W' ∧ (W'.1 = .fault ∨ W'.1 = .ovf)) ∧
    (∀ n I', IRN n I₀ I' → ∃ k W', WN T k W₀ W' ∧ (k = n ∨ W'.1 = .ovf)) := by
  intro T I₀ W₀
  have h0 := s2_init Γ₀ Δ₀ e τ ρ₀ ρw₀ hty hw hf hok he hl hm
  refine ⟨fun n v σ' hr => ?_, fun n c ρ k σ' hr hst => ?_, fun n I' hr => ?_⟩
  · obtain ⟨j, W', hw', r⟩ := s2_run hT h0 hr
    rcases r with ⟨-, r⟩ | ⟨-, r⟩
    · cases r with
      | done hv => exact ⟨j, _, hw', .inl ⟨_, _, rfl, hv⟩⟩
    · exact ⟨j, W', hw', .inr r⟩
  · obtain ⟨j, W', hw', r⟩ := s2_run hT h0 hr
    rcases r with ⟨-, r⟩ | ⟨-, r⟩
    · rcases sim2_step hT r with ⟨-, W'', h1, h2⟩ | ⟨I₁, h1, -⟩
      · exact ⟨j + 1, W'', by simpa using WN.trans hw' (.step h1 (.refl _)), h2⟩
      · rw [hst] at h1; cases h1
    · exact ⟨j, W', hw', .inr r⟩
  · obtain ⟨j, W', hw', r⟩ := s2_run hT h0 hr
    rcases r with ⟨rfl, -⟩ | ⟨-, r⟩
    · exact ⟨_, W', hw', .inl rfl⟩
    · exact ⟨j, W', hw', .inr r⟩

/-! ## The converse: a word run that FINISHES forces the IR run to finish, with a related value. -/
theorem WN.det_stuck {tbl : Table} : ∀ {n s t}, WN tbl n s t → stepW tbl t = none → ∀ {m u}, WN tbl m s u →
    m ≤ n ∧ WN tbl (n - m) u t
  | _, _, _, .refl _, ht, _, _, hm => by
      cases hm with
      | refl => exact ⟨le_refl _, by simpa using WN.refl _⟩
      | step h _ => rw [ht] at h; cases h
  | _, _, _, .step h₁ h₂, ht, _, _, hm => by
      cases hm with
      | refl => exact ⟨Nat.zero_le _, by simpa using WN.step h₁ h₂⟩
      | step h₁' h₂' =>
        rw [h₁] at h₁'; cases h₁'
        obtain ⟨hle, hr⟩ := WN.det_stuck h₂ ht h₂'
        exact ⟨by omega, by simpa [Nat.add_sub_add_right] using hr⟩

theorem WN.from_stopped {tbl : Table} {k s u} (h : WN tbl k s u) (hs : stepW tbl s = none) : k = 0 ∧ u = s := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step h _ => rw [hs] at h; cases h

/-- An IR run either takes n steps or stops (no step) before. -/
theorem ir_classify (I : St × Store) : ∀ n, (∃ I', IRN n I I') ∨ (∃ j I', j < n ∧ IRN j I I' ∧ stepIR I' = none)
  | 0 => .inl ⟨I, .refl _⟩
  | n + 1 => by
      rcases ir_classify I n with ⟨I', h⟩ | ⟨j, I', hj, h, hs⟩
      · cases hst : stepIR I' with
        | none => exact .inr ⟨n, I', by omega, h, hst⟩
        | some I'' => exact .inl ⟨I'', by simpa using IRN.trans h (.step hst (.refl _))⟩
      · exact .inr ⟨j, I', by omega, h, hs⟩

/-- **S2's converse.** If the word machine FINISHES (`done ws`) from a related start, the IR run finishes with a value related to
ws at the final store: the word machine's answer is always an IR answer. -/
theorem s2_converse {T lay τfin} (hT : T.length < 2 ^ 64) {I₀ : St × Store} {W₀ : WSt × WMem}
    (h0 : SRel T lay τfin I₀ W₀) {k ws m'} (hw : WN T k W₀ (.done ws, m')) :
    ∃ j v σ', IRN j I₀ (.done v, σ') ∧ VRel T lay σ' τfin v ws := by
  have hdone : stepW T (.done ws, m') = none := rfl
  rcases ir_classify I₀ (k + 1) with ⟨I', hI⟩ | ⟨j, I', -, hI, hs⟩
  · -- the IR takes k + 1 steps: the word machine would take k + 1 (impossible past done) or stop at ovf (≠ done)
    obtain ⟨m, W', hW, r⟩ := s2_run hT h0 hI
    rcases r with ⟨rfl, -⟩ | ⟨-, r⟩
    · obtain ⟨hle, -⟩ := WN.det_stuck hw hdone hW; omega
    · obtain ⟨-, hr⟩ := WN.det_stuck hw hdone hW
      obtain ⟨st, mm⟩ := W'
      simp only at r; subst r
      obtain ⟨-, hu⟩ := WN.from_stopped hr rfl
      cases hu
  · obtain ⟨m, W', hW, r⟩ := s2_run hT h0 hI
    obtain ⟨st, σ'⟩ := I'
    rcases r with ⟨-, r⟩ | ⟨-, r⟩
    · cases st with
      | done v =>
        cases r with
        | done hv =>
          rename_i ws' m''
          obtain ⟨-, hr⟩ := WN.det_stuck hw hdone hW
          obtain ⟨-, hu⟩ := WN.from_stopped hr rfl
          simp only [Prod.mk.injEq, WSt.done.injEq] at hu
          obtain ⟨rfl, rfl⟩ := hu
          exact ⟨j, v, σ', hI, hv⟩
      | run c ρ kk =>
        rcases sim2_step hT r with ⟨-, W'', h1, h2⟩ | ⟨I₁, h1, -⟩
        · obtain ⟨-, hr⟩ := WN.det_stuck hw hdone (WN.trans hW (.step h1 (.refl _)))
          obtain ⟨st'', mm⟩ := W''
          obtain ⟨-, hu⟩ := WN.from_stopped hr (by rcases h2 with h2 | h2 <;> (simp only at h2; subst h2; rfl))
          rcases h2 with h2 | h2 <;> (simp only at h2; subst h2; cases hu)
        · rw [hs] at h1; cases h1
    · obtain ⟨-, hr⟩ := WN.det_stuck hw hdone hW
      obtain ⟨st', mm⟩ := W'
      simp only at r; subst r
      obtain ⟨-, hu⟩ := WN.from_stopped hr rfl
      cases hu

end VIRC
