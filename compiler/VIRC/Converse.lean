/-
  O95 compiler, stage S1: the CONVERSE (compiler/DECLARATIONS-S1.md, "Added"). ⟶₂ is deterministic: `stepFn₂` is complete for
  `Step₂`, from L1's `stepFn_complete`, with L2 imported and not edited. The IR is a step FUNCTION. With S1's forward theorem,
  every IR run of `lowerT e` that FINISHES is matched by a ⟶₂ run that finishes with the related value and the same store.
  No other IR outcome can be manufactured: a source run that diverges, faults, or ends in an atom that does not evaluate
  forces the IR either to run forever or to stop in a `run` state.
-/
import VIRC.S1

namespace VIRC
open VIRL1 VIRL2

/-! ## ⟶₂ is deterministic. -/
theorem stepFn₂_letE (τ : Ty₂) (e₁ e₂ : Tm₂) (σ : Store) (h : ∀ a, e₁ ≠ .ret a) :
    stepFn₂ (.letE τ e₁ e₂) σ = (stepFn₂ e₁ σ).map fun c => (.letE τ c.1 e₂, c.2) := by
  cases e₁ with
  | ret a => exact absurd rfl (h a)
  | _ => rfl

theorem pure_complete : ∀ (e : Tm₂) {e' : Tm₂}, Step e e' → ∀ σ, stepFn₂ e σ = some (e', σ)
  | .letE τ e₁ e₂, _, h, σ => by
      cases h with
      | letRet hv => simp [stepFn₂, hv]
      | letStep h' =>
        have ih := pure_complete e₁ h' σ
        rw [stepFn₂_letE _ _ _ _ (fun a ha => by subst ha; cases h'), ih]; rfl
  | .ret _, _, h, _ => by cases h
  | .letOp _ _ _ _, _, h, _ => by cases h
  | .app _ _, _, h, σ => by simp [stepFn₂, stepFn_complete h]
  | .ite _ _ _, _, h, σ => by simp [stepFn₂, stepFn_complete h]
  | .case _ _ _, _, h, σ => by simp [stepFn₂, stepFn_complete h]

theorem step₂_complete : ∀ {c c' : Config}, Step₂ c c' → stepFn₂ c.1 c.2 = some c' := by
  intro c c' h
  induction h with
  | pure h => exact pure_complete _ h _
  | letStep h ih =>
    rename_i τ e₁ e₁' e₂ σ σ'
    rw [stepFn₂_letE _ _ _ _ (fun a ha => by subst ha; exact no_step_ret h), ih]; rfl
  | op hvs hop => simp [stepFn₂, hvs, hop]

theorem step₂_det {c c₁ c₂ : Config} (h₁ : Step₂ c c₁) (h₂ : Step₂ c c₂) : c₁ = c₂ := by
  have := step₂_complete h₁; rw [step₂_complete h₂] at this; exact Option.some.inj this.symm

/-! ## The IR is deterministic, so two runs from one state lie on one path. -/
theorem IRN.from_done {k v σ u} (h : IRN k (.done v, σ) u) : k = 0 ∧ u = (.done v, σ) := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step h _ => simp [stepIR] at h

theorem IRN.det_stuck : ∀ {n s t}, IRN n s t → stepIR t = none → ∀ {m u}, IRN m s u → m ≤ n ∧ IRN (n - m) u t
  | _, _, _, .refl _, ht, _, _, hm => by
      cases hm with
      | refl => exact ⟨le_refl _, by simpa using IRN.refl _⟩
      | step h _ => rw [ht] at h; cases h
  | _, _, _, .step h₁ h₂, ht, _, _, hm => by
      cases hm with
      | refl => exact ⟨Nat.zero_le _, by simpa using IRN.step h₁ h₂⟩
      | step h₁' h₂' =>
        rw [h₁] at h₁'; cases h₁'
        obtain ⟨hle, hr⟩ := IRN.det_stuck h₂ ht h₂'
        exact ⟨by omega, by simpa [Nat.add_sub_add_right] using hr⟩

/-! ## A source run either takes n steps or stops (with no step) before. -/
theorem SrcN.snoc : ∀ {n c c' c''}, SrcN n c c' → Step₂ c' c'' → SrcN (n + 1) c c''
  | _, _, _, _, .refl _, h => .step h (.refl _)
  | _, _, _, _, .step h₁ h₂, h => .step h₁ (SrcN.snoc h₂ h)

theorem SrcN.to_steps : ∀ {n c c'}, SrcN n c c' → Steps₂ c c'
  | _, _, _, .refl _ => .refl _
  | _, _, _, .step h hs => .step h (SrcN.to_steps hs)

theorem src_classify (c : Config) : ∀ n, (∃ c', SrcN n c c') ∨ (∃ k c', k < n ∧ SrcN k c c' ∧ ∀ c'', ¬ Step₂ c' c'')
  | 0 => .inl ⟨c, .refl _⟩
  | n + 1 => by
      rcases src_classify c n with ⟨c', hc'⟩ | ⟨k, c', hk, hc', hs⟩
      · by_cases hst : ∃ c'', Step₂ c' c''
        · obtain ⟨c'', h⟩ := hst; exact .inl ⟨c'', SrcN.snoc hc' h⟩
        · exact .inr ⟨n, c', by omega, hc', fun c'' h => hst ⟨c'', h⟩⟩
      · exact .inr ⟨k, c', by omega, hc', hs⟩

/-- A matched ⟶₂ configuration `ret a` whose atom does not evaluate leaves the IR stuck in a `run` state. -/
theorem match_ret_none {I S} (hm : Match I S) {a : Atom₂} (hS : S.1 = .ret a) (hn : Atom.eval a = none) :
    ∃ c ρ k σ, I = (.run c ρ k, σ) ∧ stepIR I = none := by
  cases hm with
  | mk hg hr hk =>
    obtain ⟨rfl, rfl⟩ := plug_ret _ hS
    cases hk
    cases hr with
    | ret h => exact ⟨_, _, _, _, rfl, by simp only [stepIR, ARel.eval h hg, hn, Option.map_none]⟩

/-- **S1, the converse.** Every IR run of an accepted program that FINISHES is matched by a ⟶₂ run that finishes, with the
related value (`valOf`) and the SAME store. -/
theorem s1_converse (e : Tm₂) (hok : Fragment.ok e = true) (σ : Store) {n v σ'}
    (hI : IRN n (.run (lowerT e) [] [], σ) (.done v, σ')) :
    ∃ a w, Steps₂ (e, σ) (.ret a, σ') ∧ Atom.eval a = some w ∧ valOf w = v := by
  have hdone : stepIR (.done v, σ') = none := rfl
  -- an IR run that reaches a stuck `run` state cannot also finish
  have no_stuck_run : ∀ p c ρ k σ₀, IRN p (.run (lowerT e) [] [], σ) (.run c ρ k, σ₀) →
      stepIR (.run c ρ k, σ₀) = none → False := by
    intro p c ρ k σ₀ hp hst
    obtain ⟨-, hr⟩ := IRN.det_stuck hp hst hI
    obtain ⟨-, hu⟩ := IRN.from_done hr
    cases hu
  rcases src_classify (e, σ) (n + 1) with ⟨c', hc'⟩ | ⟨k, c', -, hc', hs⟩
  · obtain ⟨m, I, hle, hm, -⟩ := sim_n hc' (match_init e hok σ)
    obtain ⟨hle', -⟩ := IRN.det_stuck hI hdone hm
    omega
  · obtain ⟨m, I, -, hm, hmatch⟩ := sim_n hc' (match_init e hok σ)
    obtain ⟨t, σ₀⟩ := c'
    by_cases hret : ∃ a, t = .ret a
    · obtain ⟨a, rfl⟩ := hret
      cases hw : Atom.eval a with
      | some w =>
        have hstep := match_ret hmatch (a := a) rfl hw
        have hrun : IRN (m + 1) (.run (lowerT e) [] [], σ) (.done (valOf w), σ₀) := by
          simpa using IRN.trans hm (.step hstep (.refl _))
        obtain ⟨-, hr⟩ := IRN.det_stuck hI hdone hrun
        obtain ⟨-, hu⟩ := IRN.from_done hr
        simp only [Prod.mk.injEq, St.done.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        exact ⟨a, w, SrcN.to_steps hc', hw, rfl⟩
      | none =>
        obtain ⟨c, ρ, k', σ₁, rfl, hst⟩ := match_ret_none hmatch (a := a) rfl hw
        exact (no_stuck_run m c ρ k' σ₁ hm hst).elim
    · have hf : Faults (t, σ₀) := ⟨by cases t <;> simp_all [Tm.IsTerminal], fun c'' h => hs c'' h⟩
      obtain ⟨n', c, ρ, k', σ₁, h', hst⟩ := match_fault hmatch hf
      exact (no_stuck_run (m + n') c ρ k' σ₁ (IRN.trans hm h') hst).elim

end VIRC
