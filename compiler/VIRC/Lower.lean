/-
  O95 compiler, stage S1: the compiler function L2 → IR. It is structural: S1 erases types, replaces substitution by an
  environment and turns closed function atoms into code values. A program outside C2 is REJECTED (`compileS1 = none`).
-/
import VIRC.IRSem

namespace VIRC
open VIRL1 VIRL2

mutual
def lowerA : Atom₂ → Opd
  | .var n => .var n
  | .const c => .const c
  | .prim p as => .prim p (lowerL as)
  | .lam _ e => .code false (lowerT e)
  | .fix _ _ e => .code true (lowerT e)
  | .pair a₁ a₂ => .pair (lowerA a₁) (lowerA a₂)
  | .fst a => .fst (lowerA a)
  | .snd a => .snd (lowerA a)
  | .inl _ a => .inl (lowerA a)
  | .inr _ a => .inr (lowerA a)
def lowerL : List Atom₂ → List Opd
  | [] => []
  | a :: as => lowerA a :: lowerL as
def lowerT : Tm₂ → Code
  | .ret a => .ret (lowerA a)
  | .letE _ e₁ e₂ => .letE (lowerT e₁) (lowerT e₂)
  | .letOp o as _ e => .letOp o (lowerL as) (lowerT e)
  | .app a₁ a₂ => .app (lowerA a₁) (lowerA a₂)
  | .ite a e₁ e₂ => .ite (lowerA a) (lowerT e₁) (lowerT e₂)
  | .case a e₁ e₂ => .case (lowerA a) (lowerT e₁) (lowerT e₂)
end

/-- Stage S1. `none` = REJECTED by C2's checked predicate. -/
def compileS1 (e : Tm₂) : Option Code := if Fragment.ok e then some (lowerT e) else none

/-- The IR image of an L2 value (a non-value atom goes to `junk`, which no IR rule matches). -/
def valOf : Atom₂ → Val
  | .const c => .const c
  | .lam _ e => .code false (lowerT e)
  | .fix _ _ e => .code true (lowerT e)
  | .pair a₁ a₂ => .pair (valOf a₁) (valOf a₂)
  | .inl _ a => .inl (valOf a)
  | .inr _ a => .inr (valOf a)
  | _ => .junk

end VIRC
