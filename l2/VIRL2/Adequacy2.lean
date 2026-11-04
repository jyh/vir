/-
  O95 layer L2, Lean arm. ADEQUACY of ⟦·⟧₂ against ⟶₂ (OBJECT-L2 §6): (v, σ′) ∈ ⟦e⟧₂ σ implies ⟨e, σ⟩ ⟶₂* ⟨ret a, σ′⟩ with
  ⟨a⟩ = v. By induction on the fixpoint's approximations, as L1's; L1's `head_go_step` is reused at Σ₂. No typing is needed.
-/
import VIRL2.Denot2

namespace VIRL2
open VIRL1

theorem Steps₂.trans {c₁ c₂ c₃ : Config} (h₁ : Steps₂ c₁ c₂) (h₂ : Steps₂ c₂ c₃) : Steps₂ c₁ c₃ := by
  induction h₁ with
  | refl => exact h₂
  | step s _ ih => exact .step s (ih h₂)

theorem Steps₂.letE {τ} {e₁ e₁' e₂ : Tm₂} {σ σ'} (h : Steps₂ (e₁, σ) (e₁', σ')) :
    Steps₂ (.letE τ e₁ e₂, σ) (.letE τ e₁' e₂, σ') := by
  generalize hc : (e₁, σ) = c at h
  generalize hc' : (e₁', σ') = c' at h
  induction h generalizing e₁ σ with
  | refl => subst hc; cases hc'; exact .refl _
  | step s _ ih =>
    subst hc
    rename_i c₂ _
    obtain ⟨e₂', σ₂⟩ := c₂
    exact .step (.letStep s) (ih rfl hc')

def Φ₂o : Dom₂ →o Dom₂ := ⟨Φ₂, Φ₂_cont.monotone⟩

theorem approx_adequate₂ : ∀ (i : Nat) (c : Config) {r}, r ∈ Part.Fix.approx Φ₂o i c →
    ∃ a, Steps₂ c (.ret a, r.2) ∧ a.eval = some r.1
  | 0, _, _, hv => absurd hv (Part.notMem_none _)
  | i + 1, ⟨e, σ⟩, r, hv => by
    simp only [Part.Fix.approx] at hv
    change r ∈ Φ₂ _ (e, σ) at hv
    cases e with
    | letE τ e₁ e₂ =>
      simp only [Φ₂, Part.mem_bind_iff] at hv
      obtain ⟨w, hw, hv⟩ := hv
      obtain ⟨a₁, hs₁, ha₁⟩ := approx_adequate₂ i _ hw
      obtain ⟨a, hs, ha⟩ := approx_adequate₂ i _ hv
      exact ⟨a, (Steps₂.letE hs₁).trans (.step (.pure (.letRet ha₁)) hs), ha⟩
    | letOp o as τ e =>
      simp only [Φ₂, opRun] at hv
      split at hv
      · next vs hvs =>
        split at hv
        · next v σ' hop =>
          obtain ⟨a, hs, ha⟩ := approx_adequate₂ i _ hv
          exact ⟨a, .step (.op hvs hop) hs, ha⟩
        · exact absurd hv (Part.notMem_none _)
      · exact absurd hv (Part.notMem_none _)
    | _ =>
      simp only [Φ₂] at hv
      generalize hh : head _ = hd at hv
      cases hd with
      | val w =>
        simp only [headRun₂, Part.mem_some_iff] at hv; subst hv
        first
        | (simp only [head] at hh; split at hh <;> cases hh; exact ⟨_, .refl _, ‹_›⟩)
        | (simp only [head] at hh; split at hh <;> cases hh)
        | (simp only [head] at hh; split at hh <;> (try split at hh) <;> cases hh)
        | simp [head] at hh
      | go e' =>
        obtain ⟨a, hs, ha⟩ := approx_adequate₂ i _ hv
        exact ⟨a, .step (.pure (head_go_step hh)) hs, ha⟩
      | stuck => simp [headRun₂] at hv

/-- ADEQUACY: (v, σ′) ∈ ⟦e⟧₂ σ implies ⟨e, σ⟩ ⟶₂* ⟨ret a, σ′⟩ with ⟨a⟩ = v. -/
theorem adequacy₂ {c : Config} {v σ'} (hv : (v, σ') ∈ den₂ c) : ∃ a, Steps₂ c (.ret a, σ') ∧ a.eval = some v := by
  obtain ⟨i, hi⟩ := (Part.Fix.mem_iff Φ₂o c (v, σ')).mp hv
  exact approx_adequate₂ i c hi

/-- The two directions as one statement. -/
theorem den₂_iff_steps {c : Config} {v σ'} : (v, σ') ∈ den₂ c ↔ ∃ a, Steps₂ c (.ret a, σ') ∧ a.eval = some v :=
  ⟨adequacy₂, fun ⟨_, hs, ha⟩ => by rw [den₂_of_steps hs ha]; exact Part.mem_some _⟩

end VIRL2
