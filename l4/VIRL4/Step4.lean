/-
  O95 layer L4, Lean arm (amend-21). OBJECT-L4 H3 (a): ⟶₄, small-step INTERLEAVING, a RELATION, scheduler-free.
  `par e₁ e₂` steps either side; `par (ret a₁) (ret a₂)` joins to `ret (v₁, v₂)`. `acquire` on a HELD lock has NO step:
  such a configuration is BLOCKED, never FAULTED (Faults₄ excludes it; deadlock is outside partial correctness, Q8).
  The pure rules are L1's, RESTATED for Tm₄ (L1's `Step` is over `Tm S` and cannot see `par`): this file's pure half is
  part of the `L4.syntaxCopy` line. The L2 operations go through L2's own `opStep`, unchanged (Q1).
-/
import VIRL4.Syntax

namespace VIRL4
open VIRL1 VIRL2

/-- A lock's state: the base of the ONE region it guards (H2 (a)), free or held. -/
inductive LockSt | free (p : Int) | held (p : Int)
  deriving DecidableEq, Repr

/-- Store₄ = L2's store plus the lock table; a lock's id is its index. -/
structure Store₄ where
  σ : Store
  locks : List LockSt

/-! ## Atom evaluation (L1's, restated over Σ₄). -/
def Const₄.toL1 : Const₄ → Option L1.Const
  | .c2 c => Const.toL1 c
  | .lockv _ => none

def constsOf₄ : List Atom₄ → Option (List L1.Const)
  | [] => some []
  | .const c :: vs => (Const₄.toL1 c).bind fun c₁ => (constsOf₄ vs).map (c₁ :: ·)
  | _ :: _ => none

mutual
def Atom₄.eval : Atom₄ → Option Atom₄
  | .var _ => none
  | .const c => some (.const c)
  | .prim p as => (Atom₄.evalL as).bind fun vs => (constsOf₄ vs).bind fun cs =>
      (L1.Prim.interp p cs).map fun c => .const (.c2 (Const.ofL1 c))
  | .lam τ e => some (.lam τ e)
  | .fix τ₁ τ₂ e => some (.fix τ₁ τ₂ e)
  | .pair a₁ a₂ => (Atom₄.eval a₁).bind fun v₁ => (Atom₄.eval a₂).map fun v₂ => .pair v₁ v₂
  | .fst a => (Atom₄.eval a).bind fun v => match v with
    | .pair v₁ _ => some v₁
    | _ => none
  | .snd a => (Atom₄.eval a).bind fun v => match v with
    | .pair _ v₂ => some v₂
    | _ => none
  | .inl τ a => (Atom₄.eval a).map (.inl τ)
  | .inr τ a => (Atom₄.eval a).map (.inr τ)
def Atom₄.evalL : List Atom₄ → Option (List Atom₄)
  | [] => some []
  | a :: as => (Atom₄.eval a).bind fun v => (Atom₄.evalL as).map (v :: ·)
end

def Const₄.toBool : Const₄ → Option Bool
  | .c2 (.bool b) => some b
  | _ => none

/-! ## The operations. O₂'s through L2's `opStep` on the lowered constants; the three lock operations here. -/
def lowerV : Atom₄ → Option Atom₂
  | .const (.c2 c) => some (.const c)
  | _ => none

def raiseV : Atom₂ → Atom₄
  | .const c => .const (.c2 c)
  | _ => .const (.c2 .unit)          -- never reached: `opStep` returns constants only

def capv (p : Int) : Atom₄ := .const (.c2 (.cap p))
def lockv (l : Nat) : Atom₄ := .const (.lockv l)
def unitv : Atom₄ := .const (.c2 .unit)

def opStep₄ : Op₄ → List Atom₄ → Store₄ → Option (Atom₄ × Store₄)
  | .o2 o, vs, s => (vs.mapM lowerV).bind fun ws => (opStep o ws s.σ).map fun (v, σ') => (raiseV v, ⟨σ', s.locks⟩)
  | .newlock, [.const (.c2 (.cap p))], s => some (lockv s.locks.length, ⟨s.σ, s.locks ++ [.free p]⟩)
  | .acquire, [.const (.lockv l)], s => match s.locks[l]? with
    | some (.free p) => some (capv p, ⟨s.σ, s.locks.set l (.held p)⟩)
    | _ => none
  | .release, [.const (.lockv l), .const (.c2 (.cap p))], s => match s.locks[l]? with
    | some (.held q) => if p = q then some (unitv, ⟨s.σ, s.locks.set l (.free q)⟩) else none
    | _ => none
  | _, _, _ => none

abbrev Config₄ := Tm₄ × Store₄

/-- ⟶₄. -/
inductive Step₄ : Config₄ → Config₄ → Prop where
  | letRet {τ a v e₂ s} : Atom₄.eval a = some v → Step₄ (.letE τ (.ret a) e₂, s) (e₂.subst 0 v, s)
  | letStep {τ e₁ e₁' e₂ s s'} : Step₄ (e₁, s) (e₁', s') → Step₄ (.letE τ e₁ e₂, s) (.letE τ e₁' e₂, s')
  | appLam {a₁ a₂ τ e v s} : Atom₄.eval a₁ = some (.lam τ e) → Atom₄.eval a₂ = some v →
      Step₄ (.app a₁ a₂, s) (e.subst 0 v, s)
  | appFix {a₁ a₂ τ₁ τ₂ e v s} : Atom₄.eval a₁ = some (.fix τ₁ τ₂ e) → Atom₄.eval a₂ = some v →
      Step₄ (.app a₁ a₂, s) ((e.subst 0 v).subst 0 (.fix τ₁ τ₂ e), s)
  | iteT {a e₁ e₂ c s} : Atom₄.eval a = some (.const c) → Const₄.toBool c = some true → Step₄ (.ite a e₁ e₂, s) (e₁, s)
  | iteF {a e₁ e₂ c s} : Atom₄.eval a = some (.const c) → Const₄.toBool c = some false → Step₄ (.ite a e₁ e₂, s) (e₂, s)
  | caseL {a e₁ e₂ τ v s} : Atom₄.eval a = some (.inl τ v) → Step₄ (.case a e₁ e₂, s) (e₁.subst 0 v, s)
  | caseR {a e₁ e₂ τ v s} : Atom₄.eval a = some (.inr τ v) → Step₄ (.case a e₁ e₂, s) (e₂.subst 0 v, s)
  | op {o as τ e vs v s s'} : Atom₄.evalL as = some vs → opStep₄ o vs s = some (v, s') →
      Step₄ (.letOp o as τ e, s) (e.subst 0 v, s')
  | parL {e₁ e₁' e₂ s s'} : Step₄ (e₁, s) (e₁', s') → Step₄ (.par e₁ e₂, s) (.par e₁' e₂, s')
  | parR {e₁ e₂ e₂' s s'} : Step₄ (e₂, s) (e₂', s') → Step₄ (.par e₁ e₂, s) (.par e₁ e₂', s')
  | parDone {a₁ a₂ v₁ v₂ s} : Atom₄.eval a₁ = some v₁ → Atom₄.eval a₂ = some v₂ →
      Step₄ (.par (.ret a₁) (.ret a₂), s) (.ret (.pair v₁ v₂), s)

/-- ⟶₄*. -/
inductive Steps₄ : Config₄ → Config₄ → Prop where
  | refl (c) : Steps₄ c c
  | step {c c' c''} : Step₄ c c' → Steps₄ c' c'' → Steps₄ c c''

def Tm₄.IsTerminal : Tm₄ → Prop
  | .ret _ => True
  | _ => False

/-- A thread WAITS when its next act is `acquire` of a held lock; a `par` waits when every live side waits. -/
inductive Waits : Tm₄ → Store₄ → Prop where
  | acq {l p τ e s} : s.locks[l]? = some (.held p) → Waits (.letOp .acquire [.const (.lockv l)] τ e) s
  | letW {τ e₁ e₂ s} : Waits e₁ s → Waits (.letE τ e₁ e₂) s
  | parBoth {e₁ e₂ s} : Waits e₁ s → Waits e₂ s → Waits (.par e₁ e₂) s
  | parL {e₁ a s} : Waits e₁ s → Waits (.par e₁ (.ret a)) s
  | parR {a e₂ s} : Waits e₂ s → Waits (.par (.ret a) e₂) s

/-- BLOCKED: no step, and the reason is a held lock (a deadlock, or a wait no thread will end). -/
def Blocked₄ (c : Config₄) : Prop := (∀ c', ¬ Step₄ c c') ∧ Waits c.1 c.2

/-- A FAULT: not terminal, no step, and NOT blocked. Partial correctness excludes these only. -/
def Faults₄ (c : Config₄) : Prop := ¬ c.1.IsTerminal ∧ (∀ c', ¬ Step₄ c c') ∧ ¬ Waits c.1 c.2

end VIRL4
