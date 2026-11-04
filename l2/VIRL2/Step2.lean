/-
  O95 layer L2, Lean arm. OBJECT-L2 §3: ⟶₂ on configurations ⟨e, σ⟩, DEFINED (never primitive; L1-E2 applies).
  L1's rules are lifted with σ unchanged by reusing L1's `Step` at Σ₂ VERBATIM (`pure`); the context rule is re-stated for
  configurations (`letStep`), because an O₂ step inside a `let` changes σ; one rule fires an O₂ operation (`op`), through
  `opStep` (Store.lean). A FAULT is a configuration with no step that is not `ret`.
-/
import VIRL2.Store

namespace VIRL2
open VIRL1

abbrev Config := Tm₂ × Store

inductive Step₂ : Config → Config → Prop where
  | pure {e e' σ} : Step e e' → Step₂ (e, σ) (e', σ)
  | letStep {τ e₁ e₁' e₂ σ σ'} : Step₂ (e₁, σ) (e₁', σ') → Step₂ (.letE τ e₁ e₂, σ) (.letE τ e₁' e₂, σ')
  | op {o as τ e vs v σ σ'} : Atom.evalL as = some vs → opStep o vs σ = some (v, σ') →
      Step₂ (.letOp o as τ e, σ) (e.subst 0 v, σ')

/-- ⟶₂*. -/
inductive Steps₂ : Config → Config → Prop where
  | refl (c) : Steps₂ c c
  | step {c c' c''} : Step₂ c c' → Steps₂ c' c'' → Steps₂ c c''

/-- A configuration FAULTS when it is not terminal and has no step (OBJECT-L2 §2). -/
def Faults (c : Config) : Prop := ¬ c.1.IsTerminal ∧ ∀ c', ¬ Step₂ c c'

/-! ## A step FUNCTION, for running the acceptance programs; proved to agree with `Step₂` (Programs use it, Step2 states it). -/
def stepFn₂ : Tm₂ → Store → Option Config
  | .letE τ (.ret a) e₂, σ => (Atom.eval a).map fun v => (e₂.subst 0 v, σ)
  | .letE τ e₁ e₂, σ => (stepFn₂ e₁ σ).map fun c => (.letE τ c.1 e₂, c.2)
  | .letOp o as _ e, σ => (Atom.evalL as).bind fun vs => (opStep o vs σ).map fun (v, σ') => (e.subst 0 v, σ')
  | e, σ => (stepFn e).map fun e' => (e', σ)

/-- Run at most n steps. -/
def run₂ : Nat → Config → Config
  | 0, c => c
  | n + 1, c => match stepFn₂ c.1 c.2 with
    | some c' => run₂ n c'
    | none => c

theorem stepFn₂_sound : ∀ {e : Tm₂} {σ : Store} {c' : Config}, stepFn₂ e σ = some c' → Step₂ (e, σ) c'
  | .letE τ (.ret a) e₂, σ, c', h => by
      simp only [stepFn₂, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h; exact .pure (.letRet hv)
  | .letE τ (.letE τ' e₁ e₃) e₂, σ, c', h => by
      simp only [stepFn₂, Option.map_eq_some_iff] at h
      obtain ⟨⟨e₁', σ'⟩, h₁, rfl⟩ := h; exact .letStep (stepFn₂_sound h₁)
  | .letE τ (.letOp o as τ' e₁) e₂, σ, c', h => by
      simp only [stepFn₂, Option.map_eq_some_iff] at h
      obtain ⟨⟨e₁', σ'⟩, h₁, rfl⟩ := h; exact .letStep (stepFn₂_sound (by simpa only [stepFn₂, Option.map_eq_some_iff, Option.bind_eq_some_iff] using h₁))
  | .letE τ (.app a₁ a₂) e₂, σ, c', h => by
      simp only [stepFn₂, Option.map_eq_some_iff] at h
      obtain ⟨⟨e₁', σ'⟩, h₁, rfl⟩ := h; exact .letStep (stepFn₂_sound (by simpa only [stepFn₂, Option.map_eq_some_iff, Option.bind_eq_some_iff] using h₁))
  | .letE τ (.ite a e₁ e₃) e₂, σ, c', h => by
      simp only [stepFn₂, Option.map_eq_some_iff] at h
      obtain ⟨⟨e₁', σ'⟩, h₁, rfl⟩ := h; exact .letStep (stepFn₂_sound (by simpa only [stepFn₂, Option.map_eq_some_iff, Option.bind_eq_some_iff] using h₁))
  | .letE τ (.case a e₁ e₃) e₂, σ, c', h => by
      simp only [stepFn₂, Option.map_eq_some_iff] at h
      obtain ⟨⟨e₁', σ'⟩, h₁, rfl⟩ := h; exact .letStep (stepFn₂_sound (by simpa only [stepFn₂, Option.map_eq_some_iff, Option.bind_eq_some_iff] using h₁))
  | .letOp o as τ e, σ, c', h => by
      simp only [stepFn₂, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨vs, hvs, ⟨v, σ'⟩, hop, rfl⟩ := h; exact .op hvs hop
  | .ret a, σ, c', h => by simp [stepFn₂, stepFn] at h
  | .app a₁ a₂, σ, c', h => by
      simp only [stepFn₂, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h; exact .pure (stepFn_sound he)
  | .ite a e₁ e₂, σ, c', h => by
      simp only [stepFn₂, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h; exact .pure (stepFn_sound he)
  | .case a e₁ e₂, σ, c', h => by
      simp only [stepFn₂, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h; exact .pure (stepFn_sound he)

theorem run₂_steps : ∀ (n : Nat) (c : Config), Steps₂ c (run₂ n c)
  | 0, c => .refl c
  | n + 1, c => by
      unfold run₂
      split
      · next c' h => exact .step (stepFn₂_sound h) (run₂_steps n c')
      · exact .refl c

end VIRL2
