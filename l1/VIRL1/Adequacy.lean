/-
  O95 layer L1, Lean arm. STEP 6b, ADEQUACY (OBJECT-L1 §6): if ⟦e⟧ is defined with value v, then e ⟶* ret a with ⟨a⟩ = v.
  Built after L1 closed (amend-13 W7: scored when built). By induction on the fixpoint's approximations; no typing is needed.
-/
import VIRL1.Denot

namespace VIRL1
variable {S : Sig}

theorem Steps.trans {e₁ e₂ e₃ : Tm S} (h₁ : Steps e₁ e₂) (h₂ : Steps e₂ e₃) : Steps e₁ e₃ := by
  induction h₁ with
  | refl => exact h₂
  | step s _ ih => exact .step s (ih h₂)

theorem Steps.letE {τ} {e₁ e₁' e₂ : Tm S} (h : Steps e₁ e₁') : Steps (.letE τ e₁ e₂) (.letE τ e₁' e₂) := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.letStep s) ih

theorem approx_adequate : ∀ (i : Nat) (e : Tm S) {v}, v ∈ Part.Fix.approx (Φo (S := S)) i e →
    ∃ a, Steps e (.ret a) ∧ a.eval = some v
  | 0, _, _, hv => absurd hv (Part.notMem_none _)
  | i + 1, e, v, hv => by
    simp only [Part.Fix.approx] at hv
    change v ∈ Φ _ e at hv
    cases e with
    | letE τ e₁ e₂ =>
      simp only [Φ, Part.mem_bind_iff] at hv
      obtain ⟨w, hw, hv⟩ := hv
      obtain ⟨a₁, hs₁, ha₁⟩ := approx_adequate i e₁ hw
      obtain ⟨a, hs, ha⟩ := approx_adequate i _ hv
      exact ⟨a, (Steps.letE hs₁).trans (.step (.letRet ha₁) hs), ha⟩
    | _ =>
      simp only [Φ] at hv
      generalize hh : head _ = hd at hv
      cases hd with
      | val w =>
        simp only [Head.run, Part.mem_some_iff] at hv; subst hv
        first
        | (simp only [head] at hh; split at hh <;> cases hh; exact ⟨_, .refl _, ‹_›⟩)
        | (simp only [head] at hh; split at hh <;> cases hh)
        | (simp only [head] at hh; split at hh <;> (try split at hh) <;> cases hh)
        | simp [head] at hh
      | go e' =>
        obtain ⟨a, hs, ha⟩ := approx_adequate i e' hv
        exact ⟨a, .step (head_go_step hh) hs, ha⟩
      | stuck => simp [Head.run] at hv

/-- ADEQUACY: v ∈ ⟦e⟧ implies e ⟶* ret a with ⟨a⟩ = v. With `den_of_steps` (soundness), the two directions together say
  that the denotation and the small-step semantics define the same partial function on closed expressions. -/
theorem adequacy {e : Tm S} {v} (hv : v ∈ den e) : ∃ a, Steps e (.ret a) ∧ a.eval = some v := by
  obtain ⟨i, hi⟩ := (Part.Fix.mem_iff (Φo (S := S)) e v).mp hv
  exact approx_adequate i e hi

/-- The two directions as one statement. -/
theorem den_iff_steps {e : Tm S} {v} : v ∈ den e ↔ ∃ a, Steps e (.ret a) ∧ a.eval = some v :=
  ⟨adequacy, fun ⟨_, hs, ha⟩ => by rw [den_of_steps hs ha]; exact Part.mem_some _⟩

end VIRL1
