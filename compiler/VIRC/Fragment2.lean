/-
  O95 compiler, stage S2: the S2 predicate, checked. S2-A (a): no `alloc` or `free` (regions come from the caller). C4 (b):
  every integer CONSTANT is in [−2⁶³, 2⁶³). Constants outside it are REJECTED at compile time, never wrapped. Like C2, it
  is a `Bool` that the compiler evaluates.
-/
import VIRC.Flatten

namespace VIRC
open VIRL1 VIRL2

mutual
def Atom.ok2 : Atom₂ → Bool
  | .var _ => true
  | .const (.int n) => inRange n
  | .const _ => true
  | .prim _ as => Atom.ok2L as
  | .lam _ e => Tm.ok2 e
  | .fix _ _ e => Tm.ok2 e
  | .pair a₁ a₂ => Atom.ok2 a₁ && Atom.ok2 a₂
  | .fst a => Atom.ok2 a
  | .snd a => Atom.ok2 a
  | .inl _ a => Atom.ok2 a
  | .inr _ a => Atom.ok2 a
def Atom.ok2L : List Atom₂ → Bool
  | [] => true
  | a :: as => Atom.ok2 a && Atom.ok2L as
def Tm.ok2 : Tm₂ → Bool
  | .ret a => Atom.ok2 a
  | .letE _ e₁ e₂ => Tm.ok2 e₁ && Tm.ok2 e₂
  | .letOp .alloc _ _ _ => false
  | .letOp .free _ _ _ => false
  | .letOp _ as _ e => Atom.ok2L as && Tm.ok2 e
  | .app a₁ a₂ => Atom.ok2 a₁ && Atom.ok2 a₂
  | .ite a e₁ e₂ => Atom.ok2 a && Tm.ok2 e₁ && Tm.ok2 e₂
  | .case a e₁ e₂ => Atom.ok2 a && Tm.ok2 e₁ && Tm.ok2 e₂
end

/-- The compiler's S2 acceptance test (C2 and S2's predicate, both by evaluation). -/
def Fragment2.ok (e : Tm₂) : Bool := Fragment.ok e && Tm.ok2 e

theorem rejects_alloc : Fragment2.ok (.letOp .alloc [.const (.int 4)] tcap (.ret (.const .unit)) : Tm₂) = false := by
  decide

theorem rejects_big_const : Fragment2.ok (.ret (.const (.int (2 ^ 63))) : Tm₂) = false := by decide

end VIRC
