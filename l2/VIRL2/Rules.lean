/-
  O95 layer L2, Lean arm. OBJECT-L2 §5's structural rules: `ret`, `let x:τ = e₁ in e₂`, and a deterministic PURE head
  step (which covers `if`, `case` and application once the head is known). Each is proved from ⟶₂ by inverting its first step.
-/
import VIRL2.Axioms

namespace VIRL2
open VIRL1

theorem step_ret_none {a : Atom₂} {e'} (h : Step (Tm.ret a) e') : False := by cases h

theorem step₂_ret_none {a : Atom₂} {σ c} (h : Step₂ (Tm.ret a, σ) c) : False := by
  cases h with
  | pure h => exact step_ret_none h

theorem steps₂_ret {a : Atom₂} {σ c} (h : Steps₂ (Tm.ret a, σ) c) : c = (Tm.ret a, σ) := by
  cases h with
  | refl => rfl
  | step h₁ _ => exact (step₂_ret_none h₁).elim

theorem ret_rule {a v : Atom₂} {Q : Atom₂ → Assn} (hv : a.eval = some v) : Triple (Q v) (.ret a) Q := by
  intro σ σf hQ hd hwf
  refine ⟨fun c hc => ?_, fun a' σ' hc => ?_⟩
  · rw [steps₂_ret hc]; exact fun hf => hf.1 trivial
  · have := steps₂_ret hc
    simp only [Prod.mk.injEq, Tm.ret.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨v, σ, hv, hd, rfl, hwf, hQ⟩

theorem step₂_letE_inv {τ e₁ e₂ σ c'} (h : Step₂ (Tm.letE τ e₁ e₂, σ) c') :
    (∃ e₁' σ', Step₂ (e₁, σ) (e₁', σ') ∧ c' = (Tm.letE τ e₁' e₂, σ')) ∨
    (∃ a v, e₁ = .ret a ∧ Atom.eval a = some v ∧ c' = (e₂.subst 0 v, σ)) := by
  cases h with
  | pure hs =>
    cases hs with
    | letRet hv => exact .inr ⟨_, _, rfl, hv, rfl⟩
    | letStep hs => exact .inl ⟨_, _, .pure hs, rfl⟩
  | letStep hs => exact .inl ⟨_, _, hs, rfl⟩

theorem steps₂_letE {τ e₁ e₂ σ c} (h : Steps₂ (Tm.letE τ e₁ e₂, σ) c) :
    (∃ e₁' σ', Steps₂ (e₁, σ) (e₁', σ') ∧ c = (Tm.letE τ e₁' e₂, σ')) ∨
    (∃ a v σ', Steps₂ (e₁, σ) (.ret a, σ') ∧ Atom.eval a = some v ∧ Steps₂ (e₂.subst 0 v, σ') c) := by
  generalize hc₀ : (Tm.letE τ e₁ e₂, σ) = c₀ at h
  induction h generalizing e₁ σ with
  | refl => subst hc₀; exact .inl ⟨e₁, σ, .refl _, rfl⟩
  | step h₁ h₂ ih =>
    subst hc₀
    rcases step₂_letE_inv h₁ with ⟨e₁', σ', hs, rfl⟩ | ⟨a, v, rfl, hv, rfl⟩
    · rcases ih rfl with ⟨e₁'', σ'', hs', rfl⟩ | ⟨a, v, σ'', hs', hv, hc⟩
      · exact .inl ⟨e₁'', σ'', .step hs hs', rfl⟩
      · exact .inr ⟨a, v, σ'', .step hs hs', hv, hc⟩
    · exact .inr ⟨a, v, σ, .refl _, hv, h₂⟩

/-- The `let x:τ = e₁ in e₂` rule. -/
theorem letE_rule {P : Assn} {τ : Ty₂} {e₁ e₂ : Tm₂} {Q R : Atom₂ → Assn} (h₁ : Triple P e₁ Q)
    (h₂ : ∀ v, Triple (Q v) (e₂.subst 0 v) R) : Triple P (.letE τ e₁ e₂) R := by
  intro σ σf hP hd hwf
  obtain ⟨hs₁, hp₁⟩ := h₁ σ σf hP hd hwf
  refine ⟨fun c hc => ?_, fun a σ' hc => ?_⟩
  · rcases steps₂_letE hc with ⟨e₁', σ', hs, rfl⟩ | ⟨a, v, σ', hs, hv, hc'⟩
    · rintro ⟨-, hns⟩
      cases e₁' with
      | ret a =>
        obtain ⟨v, -, hv, -⟩ := hp₁ a σ' hs
        exact hns _ (.pure (.letRet hv))
      | _ =>
        have hnf := hs₁ _ hs
        apply hnf
        refine ⟨fun h => h, fun ⟨e'', σ''⟩ hst => hns _ (.letStep hst)⟩
    · obtain ⟨v', σq, hv', hdq, rfl, hwq, hQ⟩ := hp₁ a σ' hs
      rw [hv] at hv'; cases hv'
      exact (h₂ v σq σf hQ hdq hwq).1 c hc'
  · rcases steps₂_letE hc with ⟨e₁', σ'', hs, heq⟩ | ⟨a', v, σ'', hs, hv, hc'⟩
    · simp at heq
    · obtain ⟨v', σq, hv', hdq, rfl, hwq, hQ⟩ := hp₁ a' σ'' hs
      rw [hv] at hv'; cases hv'
      exact (h₂ v σq σf hQ hdq hwq).2 a σ' hc'

/-- A deterministic PURE head step: if (e, σ) steps only to (e', σ), for every σ, and does step, then e inherits e′'s triple. -/
theorem pure_step_rule {P : Assn} {e e' : Tm₂} {Q : Atom₂ → Assn} (hstep : Step e e')
    (hdet : ∀ σ c, Step₂ (e, σ) c → c = (e', σ)) (h : Triple P e' Q) : Triple P e Q := by
  intro σ σf hP hd hwf
  obtain ⟨hs, hp⟩ := h σ σf hP hd hwf
  refine ⟨fun c hc => ?_, fun a σ' hc => ?_⟩
  · cases hc with
    | refl => exact fun hf => hf.2 _ (.pure hstep)
    | step h₁ h₂ => rw [hdet _ _ h₁] at h₂; exact hs c h₂
  · cases hc with
    | refl => exact (step_ret_none hstep).elim
    | step h₁ h₂ => rw [hdet _ _ h₁] at h₂; exact hp a σ' h₂

end VIRL2
