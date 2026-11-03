/-
  O95 layer L1, Lean arm. STEP 6: the denotation is the meaning (OBJECT-L1 §6).
  ONE least fixed point over one value domain (closed values): `den = Part.fix Φ` (E3: mathlib's `Part.fix`, no fuel).
  Required here: Φ's continuity (the side condition, W6b), the UNFOLDING EQUATION, SOUNDNESS of ⟶ against `den`, and
  SEMANTIC TYPE SOUNDNESS (⊢ e : τ ⇒ every value in `den e` is a value of type τ).
-/
import VIRL1.Safety
import Mathlib.Control.LawfulFix

namespace VIRL1
open OmegaCompletePartialOrder
variable {S : Sig} {E : ESig S}

/-- What an expression that is not a `let` does in one unfolding: a value, a continuation, or nothing. E-independent. -/
inductive Head (S : Sig) where
  | val (v : Atom S)
  | go (e : Tm S)
  | stuck

/-- OBJECT-L1 §6's Φ, the non-`let` clauses. -/
def head : Tm S → Head S
  | .ret a => match a.eval with
    | some v => .val v
    | none => .stuck
  | .app a₁ a₂ => match a₁.eval, a₂.eval with
    | some (.lam _ b), some v => .go (b.subst 0 v)
    | some (.fix τ₁ τ₂ b), some v => .go ((b.subst 0 v).subst 0 (.fix τ₁ τ₂ b))
    | _, _ => .stuck
  | .ite a e₁ e₂ => match a.eval with
    | some (.const c) => match S.toBool c with
      | some true => .go e₁
      | some false => .go e₂
      | none => .stuck
    | _ => .stuck
  | _ => .stuck

def Head.run (D : Tm S → Part (Atom S)) : Head S → Part (Atom S)
  | .val v => Part.some v
  | .go e => D e
  | .stuck => Part.none

/-- Φ (OBJECT-L1 §6): one level of the language. -/
def Φ (D : Tm S → Part (Atom S)) : Tm S → Part (Atom S)
  | .letE _ e₁ e₂ => (D e₁).bind fun v => D (e₂.subst 0 v)
  | e => (head e).run D

theorem Φ_cont : ωScottContinuous (Φ (S := S)) := by
  apply ωScottContinuous.of_apply₂
  intro e
  cases e with
  | letE τ e₁ e₂ =>
    exact ContinuousHom.ωScottContinuous.bind (ωScottContinuous.apply e₁)
      (ωScottContinuous.of_apply₂ fun v => ωScottContinuous.apply (e₂.subst 0 v))
  | _ =>
    simp only [Φ]
    cases head _ with
    | val v => exact ωScottContinuous.const
    | go e' => exact ωScottContinuous.apply e'
    | stuck => exact ωScottContinuous.const

/-- The denotation ⟦·⟧ on closed expressions: the least fixed point of Φ. -/
noncomputable def den : Tm S → Part (Atom S) := Part.fix Φ

/-- THE UNFOLDING EQUATION ⟦·⟧ = Φ(⟦·⟧). -/
theorem den_unfold : (den : Tm S → Part (Atom S)) = Φ den := Part.fix_eq_of_ωScottContinuous Φ_cont

theorem den_eq (e : Tm S) : den e = Φ den e := congrFun den_unfold e

/-! ## Soundness of the small-step semantics against ⟦·⟧ -/
theorem head_ret {a : Atom S} {v} (h : a.eval = some v) : head (.ret a) = .val v := by simp [head, h]

theorem den_ret {a : Atom S} {v} (h : a.eval = some v) : den (.ret a) = Part.some v := by
  rw [den_eq]; simp [Φ, head_ret h, Head.run]

theorem soundness {e e' : Tm S} (hs : Step e e') : den e = den e' := by
  induction hs with
  | letRet ha => rw [den_eq]; simp [Φ, den_ret ha]
  | letStep _ ih => rw [den_eq, den_eq (.letE _ _ _)]; simp only [Φ, ih]
  | appLam h₁ h₂ => rw [den_eq]; simp [Φ, head, h₁, h₂, Head.run]
  | appFix h₁ h₂ => rw [den_eq]; simp [Φ, head, h₁, h₂, Head.run]
  | iteT ha hb => rw [den_eq]; simp [Φ, head, ha, hb, Head.run]
  | iteF ha hb => rw [den_eq]; simp [Φ, head, ha, hb, Head.run]

theorem soundness_steps {e e' : Tm S} (hs : Steps e e') : den e = den e' := by
  induction hs with
  | refl => rfl
  | step s _ ih => exact (soundness s).trans ih

/-- e ⟶* ret a implies ⟦e⟧ = ⌊⟨a⟩⌋. -/
theorem den_of_steps {e : Tm S} {a v} (hs : Steps e (.ret a)) (h : a.eval = some v) : den e = Part.some v :=
  (soundness_steps hs).trans (den_ret h)

/-! ## Semantic type soundness, by the approximation characterisation of the least fixed point -/
/-- Φ bundled as a monotone map, so that mathlib's `Part.Fix` lemmas apply. -/
def Φo : (Tm S → Part (Atom S)) →o (Tm S → Part (Atom S)) := ⟨Φ, Φ_cont.monotone⟩

theorem head_go_step {e e' : Tm S} (h : head e = .go e') : Step e e' := by
  cases e with
  | app a₁ a₂ =>
    simp only [head] at h
    split at h
    · next b v h₁ h₂ => cases h; exact .appLam h₁ h₂
    · next τ₁ τ₂ b v h₁ h₂ => cases h; exact .appFix h₁ h₂
    · cases h
  | ite a e₁ e₂ =>
    simp only [head] at h
    split at h
    · next c hc =>
      split at h
      · cases h; exact .iteT hc ‹_›
      · cases h; exact .iteF hc ‹_›
      · cases h
    · cases h
  | ret a => simp only [head] at h; split at h <;> cases h
  | letE => simp [head] at h
  | letOp => simp [head] at h

theorem approx_typed (hS : S.Lawful) : ∀ (i : Nat) (e : Tm S) {τ v}, HasType E [] e τ →
    v ∈ Part.Fix.approx (Φo (S := S)) i e → v.IsValue ∧ HasTypeA E [] v τ
  | 0, _, _, _, _, hv => absurd hv (Part.notMem_none _)
  | i + 1, e, τ, v, h, hv => by
    simp only [Part.Fix.approx] at hv
    change v ∈ Φ _ e at hv
    cases e with
    | letE τ₁ e₁ e₂ =>
      cases h with | letE h₁ h₂ =>
      simp only [Φ, Part.mem_bind_iff] at hv
      obtain ⟨w, hw, hv⟩ := hv
      exact approx_typed hS i _ (HasType.subst0 h₂ (approx_typed hS i e₁ h₁ hw).2) hv
    | _ =>
      simp only [Φ] at hv
      generalize hh : head _ = hd at hv
      cases hd with
      | val w =>
        simp only [Head.run, Part.mem_some_iff] at hv; subst hv
        first
        | (simp only [head] at hh; split at hh <;> cases hh
           cases h with | ret ha => exact Atom.eval_typed hS ha ‹_›)
        | (simp only [head] at hh; split at hh <;> cases hh)
        | (simp only [head] at hh; split at hh <;> (try split at hh) <;> cases hh)
        | simp [head] at hh
      | go e' => exact approx_typed hS i e' (preservation hS (head_go_step hh) h) hv
      | stuck => simp [Head.run] at hv

/-- SEMANTIC TYPE SOUNDNESS: ⊢ e : τ implies every value in ⟦e⟧ is a value of type τ. -/
theorem den_typed (hS : S.Lawful) {e : Tm S} {τ v} (h : HasType E [] e τ) (hv : v ∈ den e) :
    v.IsValue ∧ HasTypeA E [] v τ := by
  obtain ⟨i, hi⟩ := (Part.Fix.mem_iff (Φo (S := S)) e v).mp hv
  exact approx_typed hS i e h hi

end VIRL1
