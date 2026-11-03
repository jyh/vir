/-
  O95 layer L1, Lean arm. STEP 3: atom evaluation and the small-step CBV relation, DEFINED (OBJECT-L1 §3).
-/
import VIRL1.Syntax

namespace VIRL1
variable {S : Sig}

/-- The constants of a list of values, if every one is a constant. -/
def constsOf : List (Atom S) → Option (List S.C)
  | [] => some []
  | .const c :: vs => (constsOf vs).map (c :: ·)
  | _ :: _ => none

mutual
/-- Atom evaluation ⟨a⟩ (OBJECT-L1 §3): a partial function on raw syntax, total on well-typed closed atoms (Safety.lean). -/
def Atom.eval : Atom S → Option (Atom S)
  | .var _ => none
  | .const c => some (.const c)
  | .prim p as => (Atom.evalL as).bind fun vs => (constsOf vs).bind fun cs => (S.pInterp p cs).map .const
  | .lam τ e => some (.lam τ e)
  | .fix τ₁ τ₂ e => some (.fix τ₁ τ₂ e)
  | .pair a₁ a₂ => (Atom.eval a₁).bind fun v₁ => (Atom.eval a₂).map fun v₂ => .pair v₁ v₂
  | .fst a => (Atom.eval a).bind fun v => match v with
    | .pair v₁ _ => some v₁
    | _ => none
  | .snd a => (Atom.eval a).bind fun v => match v with
    | .pair _ v₂ => some v₂
    | _ => none
  | .inl τ a => (Atom.eval a).map (.inl τ)
  | .inr τ a => (Atom.eval a).map (.inr τ)
def Atom.evalL : List (Atom S) → Option (List (Atom S))
  | [] => some []
  | a :: as => (Atom.eval a).bind fun v => (Atom.evalL as).map (v :: ·)
end

/-- One CBV step (OBJECT-L1 §3), on closed expressions. `letOp` has no rule: O₁ = ∅ in L1. -/
inductive Step : Tm S → Tm S → Prop where
  | letRet {τ a v e₂} : Atom.eval a = some v → Step (.letE τ (.ret a) e₂) (e₂.subst 0 v)
  | letStep {τ e₁ e₁' e₂} : Step e₁ e₁' → Step (.letE τ e₁ e₂) (.letE τ e₁' e₂)
  | appLam {a₁ a₂ τ e v} : Atom.eval a₁ = some (.lam τ e) → Atom.eval a₂ = some v → Step (.app a₁ a₂) (e.subst 0 v)
  | appFix {a₁ a₂ τ₁ τ₂ e v} : Atom.eval a₁ = some (.fix τ₁ τ₂ e) → Atom.eval a₂ = some v →
      Step (.app a₁ a₂) ((e.subst 0 v).subst 0 (.fix τ₁ τ₂ e))
  | iteT {a e₁ e₂ c} : Atom.eval a = some (.const c) → S.toBool c = some true → Step (.ite a e₁ e₂) e₁
  | iteF {a e₁ e₂ c} : Atom.eval a = some (.const c) → S.toBool c = some false → Step (.ite a e₁ e₂) e₂
  | caseL {a e₁ e₂ τ v} : Atom.eval a = some (.inl τ v) → Step (.case a e₁ e₂) (e₁.subst 0 v)
  | caseR {a e₁ e₂ τ v} : Atom.eval a = some (.inr τ v) → Step (.case a e₁ e₂) (e₂.subst 0 v)

/-- The reflexive-transitive closure ⟶*. -/
inductive Steps : Tm S → Tm S → Prop where
  | refl (e) : Steps e e
  | step {e e' e''} : Step e e' → Steps e' e'' → Steps e e''

/-- A terminal expression is `ret a` (OBJECT-L1 §3). -/
def Tm.IsTerminal : Tm S → Prop
  | .ret _ => True
  | _ => False

/-! ## A step FUNCTION, for running the acceptance programs by kernel reduction; proved to agree with `Step`. -/
def stepFn : Tm S → Option (Tm S)
  | .letE τ (.ret a) e₂ => (Atom.eval a).map fun v => e₂.subst 0 v
  | .letE τ e₁ e₂ => (stepFn e₁).map fun e₁' => .letE τ e₁' e₂
  | .app a₁ a₂ =>
    match Atom.eval a₁, Atom.eval a₂ with
    | some (.lam _ e), some v => some (e.subst 0 v)
    | some (.fix τ₁ τ₂ e), some v => some ((e.subst 0 v).subst 0 (.fix τ₁ τ₂ e))
    | _, _ => none
  | .ite a e₁ e₂ =>
    match Atom.eval a with
    | some (.const c) => match S.toBool c with
      | some true => some e₁
      | some false => some e₂
      | none => none
    | _ => none
  | .case a e₁ e₂ =>
    match Atom.eval a with
    | some (.inl _ v) => some (e₁.subst 0 v)
    | some (.inr _ v) => some (e₂.subst 0 v)
    | _ => none
  | _ => none

theorem stepFn_sound : ∀ {e e' : Tm S}, stepFn e = some e' → Step e e'
  | .letE τ (.ret a) e₂, e', h => by
      simp only [stepFn, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h; exact .letRet hv
  | .letE τ (.letE τ' e₁ e₃) e₂, e', h => by
      simp only [stepFn, Option.map_eq_some_iff] at h
      obtain ⟨e₁', h₁, rfl⟩ := h; exact .letStep (stepFn_sound h₁)
  | .letE τ (.letOp o as τ' e₁) e₂, e', h => by
      simp only [stepFn, Option.map_eq_some_iff] at h
      obtain ⟨e₁', h₁, rfl⟩ := h; exact .letStep (stepFn_sound h₁)
  | .letE τ (.app a₁ a₂) e₂, e', h => by
      simp only [stepFn, Option.map_eq_some_iff] at h
      obtain ⟨e₁', h₁, rfl⟩ := h; exact .letStep (stepFn_sound h₁)
  | .letE τ (.ite a e₁ e₃) e₂, e', h => by
      simp only [stepFn, Option.map_eq_some_iff] at h
      obtain ⟨e₁', h₁, rfl⟩ := h; exact .letStep (stepFn_sound h₁)
  | .letE τ (.case a e₁ e₃) e₂, e', h => by
      simp only [stepFn, Option.map_eq_some_iff] at h
      obtain ⟨e₁', h₁, rfl⟩ := h; exact .letStep (stepFn_sound h₁)
  | .case a e₁ e₂, e', h => by
      simp only [stepFn] at h
      split at h
      · next τ v hv => cases h; exact .caseL hv
      · next τ v hv => cases h; exact .caseR hv
      · cases h
  | .app a₁ a₂, e', h => by
      simp only [stepFn] at h
      split at h
      · next e v h₁ h₂ => cases h; exact .appLam h₁ h₂
      · next τ₁ τ₂ e v h₁ h₂ => cases h; exact .appFix h₁ h₂
      · cases h
  | .ite a e₁ e₂, e', h => by
      simp only [stepFn] at h
      split at h
      · next c hc =>
        split at h
        · cases h; exact .iteT hc ‹_›
        · cases h; exact .iteF hc ‹_›
        · cases h
      · cases h
  | .ret _, _, h => by simp [stepFn] at h
  | .letOp .., _, h => by simp [stepFn] at h

/-- Run up to `n` steps with `stepFn`. -/
def run : Nat → Tm S → Tm S
  | 0, e => e
  | n + 1, e => match stepFn e with
    | some e' => run n e'
    | none => e

theorem run_steps : ∀ (n : Nat) (e : Tm S), Steps e (run n e)
  | 0, e => .refl e
  | n + 1, e => by
      simp only [run]
      split
      · next e' h => exact .step (stepFn_sound h) (run_steps n e')
      · exact .refl e

end VIRL1
