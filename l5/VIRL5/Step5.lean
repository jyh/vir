/-
  O95 layer L5, Lean arm (amend-24; DECLARATIONS-LEAN, ⟶₅). L2's step on configurations ⟨e, σ⟩, RESTATED for Tm₅ (part of
  `L5.syntaxCopy`), with L1's CBV rules folded in (L2 lifts L1's `Step` verbatim, which cannot see Tm₅), plus THE THREE:
  * `appK` of a λ/fix lending k capabilities substitutes the argument and the k capability VALUES into the body
    (`substAll`, the binder order of Syntax.lean: c_k = #0 … x = #k, and f = #(k+1) for fix);
  * `letK τ j (retK a ds) e₂` substitutes the result and the j capabilities handed back into e₂;
  * `letK` steps under its first term, as `letE` does.
  No return frame (Addendum 1 (3)), no fuel, no step index: `fix` is L1's unfolding. A FAULT is a configuration with no step
  that is not terminal; `ret a` and `retK a ds` are the terminal forms.
-/
import VIRL5.Typing5
import VIRL2.Step2

namespace VIRL5
open VIRL1 VIRL2

/-- The constants of a list of values, if every one is a constant (L1's `constsOf`, over Atom₅). -/
def constsOf₅ : List Atom₅ → Option (List Const)
  | [] => some []
  | .const c :: vs => (constsOf₅ vs).map (c :: ·)
  | _ :: _ => none

mutual
def Atom₅.eval : Atom₅ → Option Atom₅
  | .var _ => none
  | .const c => some (.const c)
  | .prim p as => (Atom₅.evalL as).bind fun vs => (constsOf₅ vs).bind fun cs => (pInterp p cs).map .const
  | .lam τ k e => some (.lam τ k e)
  | .fix τ₁ k τ₂ e => some (.fix τ₁ k τ₂ e)
  | .pair a₁ a₂ => (Atom₅.eval a₁).bind fun v₁ => (Atom₅.eval a₂).map fun v₂ => .pair v₁ v₂
  | .fst a => (Atom₅.eval a).bind fun v => match v with
    | .pair v₁ _ => some v₁
    | _ => none
  | .snd a => (Atom₅.eval a).bind fun v => match v with
    | .pair _ v₂ => some v₂
    | _ => none
  | .inl τ a => (Atom₅.eval a).map (.inl τ)
  | .inr τ a => (Atom₅.eval a).map (.inr τ)
def Atom₅.evalL : List Atom₅ → Option (List Atom₅)
  | [] => some []
  | a :: as => (Atom₅.eval a).bind fun v => (Atom₅.evalL as).map (v :: ·)
end

/-- A value that is an L2 constant, lowered to L2 (L4's `lowerV`, over Atom₅). -/
def lowerV : Atom₅ → Option Atom₂
  | .const c => some (.const c)
  | _ => none

/-- One O₂ operation on VALUES: L2's `opStep` itself, on the lowered operands (as L4 did), its result raised by ι. -/
def opStep₅ (o : Op) (vs : List Atom₅) (σ : Store) : Option (Atom₅ × Store) :=
  (vs.mapM lowerV).bind fun ws => (opStep o ws σ).map fun p => (ιA p.1, p.2)

abbrev Config₅ := Tm₅ × Store

inductive Step₅ : Config₅ → Config₅ → Prop where
  | letRet {τ a v e₂ σ} : Atom₅.eval a = some v → Step₅ (.letE τ (.ret a) e₂, σ) (e₂.subst 0 v, σ)
  | letStep {τ e₁ e₁' e₂ σ σ'} : Step₅ (e₁, σ) (e₁', σ') → Step₅ (.letE τ e₁ e₂, σ) (.letE τ e₁' e₂, σ')
  | op {o as τ e vs v σ σ'} : Atom₅.evalL as = some vs → opStep₅ o vs σ = some (v, σ') →
      Step₅ (.letOp o as τ e, σ) (e.subst 0 v, σ')
  | appLam {a₁ a₂ τ e v σ} : Atom₅.eval a₁ = some (.lam τ 0 e) → Atom₅.eval a₂ = some v →
      Step₅ (.app a₁ a₂, σ) (e.subst 0 v, σ)
  | appFix {a₁ a₂ τ₁ τ₂ e v σ} : Atom₅.eval a₁ = some (.fix τ₁ 0 τ₂ e) → Atom₅.eval a₂ = some v →
      Step₅ (.app a₁ a₂, σ) ((e.subst 0 v).subst 0 (.fix τ₁ 0 τ₂ e), σ)
  | iteT {a e₁ e₂ c σ} : Atom₅.eval a = some (.const c) → Const.toBool c = some true → Step₅ (.ite a e₁ e₂, σ) (e₁, σ)
  | iteF {a e₁ e₂ c σ} : Atom₅.eval a = some (.const c) → Const.toBool c = some false → Step₅ (.ite a e₁ e₂, σ) (e₂, σ)
  | caseL {a e₁ e₂ τ v σ} : Atom₅.eval a = some (.inl τ v) → Step₅ (.case a e₁ e₂, σ) (e₁.subst 0 v, σ)
  | caseR {a e₁ e₂ τ v σ} : Atom₅.eval a = some (.inr τ v) → Step₅ (.case a e₁ e₂, σ) (e₂.subst 0 v, σ)
  -- THE THREE (L5-E1):
  | appKLam {a₁ a₂ cs τ k e v qs σ} : Atom₅.eval a₁ = some (.lam τ k e) → Atom₅.eval a₂ = some v →
      Atom₅.evalL cs = some qs → qs.length = k → Step₅ (.appK a₁ a₂ cs, σ) (Tm₅.substAll (v :: qs) e, σ)
  | appKFix {a₁ a₂ cs τ₁ k τ₂ e v qs σ} : Atom₅.eval a₁ = some (.fix τ₁ k τ₂ e) → Atom₅.eval a₂ = some v →
      Atom₅.evalL cs = some qs → qs.length = k →
      Step₅ (.appK a₁ a₂ cs, σ) (Tm₅.substAll (.fix τ₁ k τ₂ e :: v :: qs) e, σ)
  | letKRet {τ j a ds e₂ v qs σ} : Atom₅.eval a = some v → Atom₅.evalL ds = some qs → qs.length = j →
      Step₅ (.letK τ j (.retK a ds) e₂, σ) (Tm₅.substAll (v :: qs) e₂, σ)
  | letKRet0 {τ a e₂ v σ} : Atom₅.eval a = some v → Step₅ (.letK τ 0 (.ret a) e₂, σ) (e₂.subst 0 v, σ)
  | letKStep {τ j e₁ e₁' e₂ σ σ'} : Step₅ (e₁, σ) (e₁', σ') → Step₅ (.letK τ j e₁ e₂, σ) (.letK τ j e₁' e₂, σ')

/-- ⟶₅*. -/
inductive Steps₅ : Config₅ → Config₅ → Prop where
  | refl (c) : Steps₅ c c
  | step {c c' c''} : Step₅ c c' → Steps₅ c' c'' → Steps₅ c c''

def Tm₅.IsTerminal : Tm₅ → Prop
  | .ret _ | .retK _ _ => True
  | _ => False

def Faults₅ (c : Config₅) : Prop := ¬ c.1.IsTerminal ∧ ∀ c', ¬ Step₅ c c'

end VIRL5
