/-
  O95 layer L2, Lean arm. OBJECT-L2 §6: the meaning ⟦e⟧₂ : Store → (Val × Store)⊥ as ONE least fixed point Φ₂ — mathlib's
  `Part.fix`, OBJECT-L1 §6's form with a store (amend-16 Y8: no fuel, no second fixpoint mechanism). A FAULT is ⊥: an O₂
  operation whose `opStep` is `none` denotes `Part.none` (fault ∉ Val). L1's `head` is REUSED at Σ₂ for the non-`let` clauses.
  Here: Φ₂'s continuity (the side condition, beside L1's W6b), the unfolding equation, and soundness of ⟶₂ against ⟦·⟧₂.
-/
import VIRL2.Step2
import Mathlib.Control.LawfulFix

namespace VIRL2
open VIRL1 OmegaCompletePartialOrder

abbrev Dom₂ := Config → Part (Atom₂ × Store)

def headRun₂ (D : Dom₂) (σ : Store) : Head S₂ → Part (Atom₂ × Store)
  | .val v => Part.some (v, σ)
  | .go e => D (e, σ)
  | .stuck => Part.none

/-- The O₂ clause: evaluate the operands, run the operation, continue; a FAULT (or a stuck operand) is ⊥. -/
def opRun (D : Dom₂) (o : Op) (as : List Atom₂) (e : Tm₂) (σ : Store) : Part (Atom₂ × Store) :=
  match Atom.evalL as with
  | some vs => match opStep o vs σ with
    | some (v, σ') => D (e.subst 0 v, σ')
    | none => Part.none
  | none => Part.none

/-- Φ₂ (OBJECT-L2 §6): one level of the language with a store. -/
def Φ₂ (D : Dom₂) : Dom₂
  | (.letE _ e₁ e₂, σ) => (D (e₁, σ)).bind fun r => D (e₂.subst 0 r.1, r.2)
  | (.letOp o as _ e, σ) => opRun D o as e σ
  | (e, σ) => headRun₂ D σ (head e)

theorem Φ₂_cont : ωScottContinuous Φ₂ := by
  apply ωScottContinuous.of_apply₂
  rintro ⟨e, σ⟩
  cases e with
  | letE τ e₁ e₂ =>
    exact ContinuousHom.ωScottContinuous.bind (ωScottContinuous.apply (e₁, σ))
      (ωScottContinuous.of_apply₂ fun r => ωScottContinuous.apply (e₂.subst 0 r.1, r.2))
  | letOp o as τ e =>
    simp only [Φ₂, opRun]
    rcases hvs : Atom.evalL as with _ | vs <;> simp only [hvs]
    · exact ωScottContinuous.const
    · rcases hop : opStep o vs σ with _ | ⟨v, σ'⟩ <;> simp only [hop]
      · exact ωScottContinuous.const
      · exact ωScottContinuous.apply _
  | _ =>
    simp only [Φ₂]
    cases head _ with
    | val v => exact ωScottContinuous.const
    | go e' => exact ωScottContinuous.apply _
    | stuck => exact ωScottContinuous.const

/-- ⟦·⟧₂: the least fixed point of Φ₂. -/
noncomputable def den₂ : Dom₂ := Part.fix Φ₂

/-- THE UNFOLDING EQUATION ⟦·⟧₂ = Φ₂(⟦·⟧₂). -/
theorem den₂_unfold : den₂ = Φ₂ den₂ := Part.fix_eq_of_ωScottContinuous Φ₂_cont

theorem den₂_eq (c : Config) : den₂ c = Φ₂ den₂ c := congrFun den₂_unfold c

theorem den₂_ret {a v : Atom₂} {σ} (h : a.eval = some v) : den₂ (.ret a, σ) = Part.some (v, σ) := by
  rw [den₂_eq]; simp [Φ₂, head, h, headRun₂]

/-- L1's steps leave the store alone and preserve ⟦·⟧₂. -/
theorem soundness_pure {e e' : Tm₂} (hs : Step e e') : ∀ σ, den₂ (e, σ) = den₂ (e', σ) := by
  induction hs with
  | letRet ha => intro σ; rw [den₂_eq]; simp [Φ₂, den₂_ret ha]
  | letStep _ ih => intro σ; rw [den₂_eq, den₂_eq (.letE _ _ _, σ)]; simp only [Φ₂, ih σ]
  | appLam h₁ h₂ => intro σ; rw [den₂_eq]; simp [Φ₂, head, h₁, h₂, headRun₂]
  | appFix h₁ h₂ => intro σ; rw [den₂_eq]; simp [Φ₂, head, h₁, h₂, headRun₂]
  | @iteT a e₁ e₂ c ha hb =>
    intro σ; have hb' : Const.toBool c = some true := hb
    rw [den₂_eq]; simp [Φ₂, head, ha, hb', headRun₂]
  | @iteF a e₁ e₂ c ha hb =>
    intro σ; have hb' : Const.toBool c = some false := hb
    rw [den₂_eq]; simp [Φ₂, head, ha, hb', headRun₂]
  | caseL ha => intro σ; rw [den₂_eq]; simp [Φ₂, head, ha, headRun₂]
  | caseR ha => intro σ; rw [den₂_eq]; simp [Φ₂, head, ha, headRun₂]

/-- SOUNDNESS of ⟶₂ against ⟦·⟧₂. -/
theorem soundness₂ {c c' : Config} (hs : Step₂ c c') : den₂ c = den₂ c' := by
  induction hs with
  | pure h => exact soundness_pure h _
  | letStep _ ih => rw [den₂_eq, den₂_eq (.letE _ _ _, _)]; simp only [Φ₂, ih]
  | op h₁ h₂ => rw [den₂_eq]; simp [Φ₂, opRun, h₁, h₂]

theorem soundness₂_steps {c c' : Config} (hs : Steps₂ c c') : den₂ c = den₂ c' := by
  induction hs with
  | refl => rfl
  | step s _ ih => exact (soundness₂ s).trans ih

/-- ⟨e, σ⟩ ⟶₂* ⟨ret a, σ′⟩ implies ⟦e⟧₂ σ = ⌊(⟨a⟩, σ′)⌋. -/
theorem den₂_of_steps {c : Config} {a v σ'} (hs : Steps₂ c (.ret a, σ')) (h : a.eval = some v) :
    den₂ c = Part.some (v, σ') :=
  (soundness₂_steps hs).trans (den₂_ret h)

/-- A FAULT at an O₂ operation denotes ⊥. -/
theorem den₂_fault {o as τ e σ vs} (hvs : Atom.evalL as = some vs) (h : opStep o vs σ = none) :
    den₂ (.letOp o as τ e, σ) = Part.none := by
  rw [den₂_eq]; simp [Φ₂, opRun, hvs, h]

end VIRL2
