/-
  O95 layer L2 (OBJECT-L2), Lean arm (amend-16). §1: the signature Σ₂ as an INSTANCE of L1's `Sig` and `ESig`.
  B₂ = {int, bool, unit, cap}; the constants are L1's, `()`, and the runtime-only capabilities ⟨p⟩; P₂ = P₁ (L1's `Prim`,
  interpreted through L1's own `Prim.interp`); O₂ = {alloc, load, store, free} with OBJECT-L2 §1's arities.
  Nothing here edits L1: every L1 name is imported (W8 / Y2).
-/
import VIRL1

namespace VIRL2
open VIRL1

inductive BTy | int | bool | unit | cap
  deriving DecidableEq, Repr

inductive Const | int (n : Int) | bool (b : Bool) | unit | cap (p : Int)
  deriving DecidableEq, Repr

/-- O₂, the four region operations (OBJECT-L2 §1). -/
inductive Op | alloc | load | store | free
  deriving DecidableEq, Repr

def BTy.ofL1 : L1.BTy → BTy
  | .int => .int
  | .bool => .bool

def Const.ofL1 : L1.Const → Const
  | .int n => .int n
  | .bool b => .bool b

def Const.toL1 : Const → Option L1.Const
  | .int n => some (.int n)
  | .bool b => some (.bool b)
  | _ => none

def Const.ty : Const → BTy
  | .int _ => .int
  | .bool _ => .bool
  | .unit => .unit
  | .cap _ => .cap

/-- P₂ = P₁: a pure operator reads its arguments as L1 constants and answers through L1's interpretation. -/
def pInterp (p : L1.Prim) (cs : List Const) : Option Const :=
  (cs.mapM Const.toL1).bind fun cs₁ => (L1.Prim.interp p cs₁).map Const.ofL1

def Const.toBool : Const → Option Bool
  | .bool b => some b
  | _ => none

/-- Σ₂. Reducible, so `S₂.B` is `BTy` to instance search. -/
@[reducible] def S₂ : Sig where
  B := BTy
  C := Const
  P := L1.Prim
  O := Op
  cTy := Const.ty
  pArgs p := (L1.Prim.args p).map BTy.ofL1
  pRes p := BTy.ofL1 (L1.Prim.res p)
  pInterp := pInterp
  boolTy := .bool
  toBool := Const.toBool

abbrev Ty₂ := Ty S₂.B
abbrev Tm₂ := Tm S₂
abbrev Atom₂ := Atom S₂

def tint : Ty₂ := .base BTy.int
def tbool : Ty₂ := .base BTy.bool
def tunit : Ty₂ := .base BTy.unit
def tcap : Ty₂ := .base BTy.cap

/-- O₂'s arities (OBJECT-L1 §1's effect binder, at OBJECT-L2 §1's table). -/
def Op.args : Op → List Ty₂
  | .alloc => [tint]
  | .load => [tcap, tint]
  | .store => [tcap, tint, tint]
  | .free => [tcap]

def Op.res : Op → Ty₂
  | .alloc => tcap
  | .load => tint
  | .store => tcap
  | .free => tunit

def E₂ : ESig S₂ where
  oArgs := Op.args
  oRes := Op.res

theorem lawful : S₂.Lawful where
  pTotal := by
    intro p cs h
    cases p <;>
    first
    | (rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨_, _⟩⟩⟩ <;>
       simp [S₂, L1.Prim.args, BTy.ofL1] at h <;>
       (try cases c₁) <;> (try cases c₂) <;>
       simp_all [S₂, Const.ty, pInterp, Const.toL1, L1.Prim.interp, L1.Prim.res, Const.ofL1, BTy.ofL1])
  boolCanon := by
    intro c h
    cases c with
    | bool b => exact ⟨b, rfl⟩
    | _ => simp [S₂, Const.ty] at h

end VIRL2
