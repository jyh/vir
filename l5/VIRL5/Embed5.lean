/-
  O95 layer L5, Lean arm (STATUS 317, for bitR): an L2 term that RUNS, under ⟶₂, from every store to `ret w` with the store
  untouched inherits that as a ⊢₅ triple of its embedding ιE (LV3's CE, both directions, plus ⟶₂'s determinism, which is
  DEFLATE's `stepFn₂_complete`). This is how a routine REUSES an existing L2 lemma (DEFLATE's `bit_steps` for `BITc`) instead of
  re-proving it. Also: the k = 0 call of a `fix` (`app`), and `ιA BITc` closed under ⟶₅'s substitution.
-/
import VIRL5.Ops5
import VIRDeflate.Fit

namespace VIRL5
open VIRL1 VIRL2

/-- ⟶₂ is deterministic (DEFLATE's `stepFn₂_complete`: the step function is complete, so two steps agree). -/
theorem step₂_det {c c₁ c₂ : Config} (h₁ : Step₂ c c₁) (h₂ : Step₂ c c₂) : c₁ = c₂ := by
  have a := VIRDeflate.Step.stepFn₂_complete h₁
  have b := VIRDeflate.Step.stepFn₂_complete h₂
  rw [a] at b
  exact Option.some.inj b

/-- `ret` does not step under ⟶₂. -/
theorem step₂_ret_none {a : Atom₂} {σ : Store} {c : Config} (h : Step₂ (.ret a, σ) c) : False := by
  cases h with
  | pure h' => cases h'

/-- In a deterministic run to a configuration with no step, every reachable configuration lies on the way. -/
theorem steps₂_prefix {c d t : Config} (hterm : ∀ c', ¬ Step₂ t c') (h : Steps₂ c d) : Steps₂ c t → Steps₂ d t := by
  induction h with
  | refl => exact id
  | step s _ ih =>
    intro ht
    cases ht with
    | refl => exact absurd s (hterm _)
    | step s' ht' =>
      have e := step₂_det s s'
      subst e
      exact ih ht'

/-- ⟶₅* from an embedded configuration stays embedded, and is an embedded ⟶₂* (ce_bwd, iterated). -/
theorem steps₅_ι_bwd {c d : Config₅} (h : Steps₅ c d) :
    ∀ (e : Tm₂) (σ : Store), c = (ιE e, σ) → ∃ e' σ', Steps₂ (e, σ) (e', σ') ∧ d = (ιE e', σ') := by
  induction h with
  | refl => intro e σ hc; exact ⟨e, σ, .refl _, hc⟩
  | step s _ ih =>
    intro e σ hc
    obtain ⟨e₁, σ₁, s₂, rfl⟩ := ce_bwd s e σ hc
    obtain ⟨e', σ', hs, rfl⟩ := ih e₁ σ₁ rfl
    exact ⟨e', σ', .step s₂ hs, rfl⟩

/-- **The embedding rule.** An L2 term that runs from every store to `ret w` (w a value), leaving the store as it was, is a ⊢₅
  triple of its embedding for ANY precondition P: it returns ιA w, hands nothing back, and P still holds. -/
theorem embed_rule₅ {P : Assn} {t : Tm₂} {w : Atom₂} (hw : Atom.eval w = some w)
    (hs : ∀ σ, Steps₂ (t, σ) (.ret w, σ)) :
    Triple₅ P (ιE t) (fun r qs σ => r = ιA w ∧ qs = [] ∧ P σ) := by
  intro σ σf hP hd hwf
  have hpath := hs (σ ⊎ σf)
  have hterm : ∀ c', ¬ Step₂ (.ret w, σ ⊎ σf) c' := fun c' h => step₂_ret_none h
  refine ⟨fun c hc => ?_, fun a σ' hc => ?_, fun a ds σ' hc => ?_⟩
  · obtain ⟨e', σ', hs', rfl⟩ := steps₅_ι_bwd hc t _ rfl
    have hrest := steps₂_prefix hterm hs' hpath
    rintro ⟨hnt, hno⟩
    cases hrest with
    | refl => exact hnt (by simp [ιE, Tm₅.IsTerminal])
    | step s _ => exact hno _ (ce_fwd s)
  · obtain ⟨e', σ'', hs', heq⟩ := steps₅_ι_bwd hc t _ rfl
    cases e' <;> simp [ιE] at heq
    rename_i a₀
    obtain ⟨rfl, rfl⟩ := heq
    have hrest := steps₂_prefix hterm hs' hpath
    cases hrest with
    | refl => exact ⟨ιA w, σ, by rw [eval_ι, hw]; rfl, hd, rfl, hwf, rfl, rfl, hP⟩
    | step s _ => exact absurd s (fun h => step₂_ret_none h)
  · obtain ⟨e', σ'', hs', heq⟩ := steps₅_ι_bwd hc t _ rfl
    cases e' <;> simp [ιE] at heq

/-- The k = 0 call of a `fix` (plain `app`): it unrolls to the body with the argument and the fix substituted. -/
theorem appFix_rule₅ {P : Assn} {a₁ a₂ : Atom₅} {τ₁ τ₂ : Ty₅} {e : Tm₅} {v : Atom₅} {Q : Atom₅ → List Atom₅ → Assn}
    (h₁ : a₁.eval = some (.fix τ₁ 0 τ₂ e)) (h₂ : a₂.eval = some v)
    (h : Triple₅ P ((e.subst 0 v).subst 0 (.fix τ₁ 0 τ₂ e)) Q) : Triple₅ P (.app a₁ a₂) Q := by
  refine pure_step_rule₅ (fun σ => .appFix h₁ h₂) (fun σ c hc => ?_) h
  cases hc with
  | appLam h₁' _ => rw [h₁] at h₁'; cases h₁'
  | appFix h₁' h₂' => rw [h₁] at h₁'; cases h₁'; rw [h₂] at h₂'; cases h₂'; rfl

open VIRDeflate.Step in
/-- `ιA BITc` is closed: no ⟶₅ substitution touches it. -/
@[simp] theorem ιBITc_subst (k : Nat) (v : Atom₅) : (ιA BITc).subst k v = ιA BITc := by
  simp [BITc, STRIPc, STRIP, POW, ιA, ιE, ιL, ιT, Atom₅.subst, Tm₅.subst, Atom₅.substL, Atom.subst, Tm.subst, Atom.substL,
    ple, plt, psub, pmul, padd]

end VIRL5
