/-
  O95 layer L1, Lean arm. The L1 INSTANCE Σ₁ of OBJECT-L1 §1: B₁ = {int, bool}, the constants ℤ ⊎ 𝔹, P₁ = the nine pure
  operators of the table, O₁ = ∅. Every operator is DEFINED by its interpretation (W1: no axiom, no opaque).
-/
import VIRL1.Denot

namespace VIRL1.L1

inductive BTy | int | bool
  deriving DecidableEq, Repr

inductive Const | int (n : Int) | bool (b : Bool)
  deriving DecidableEq, Repr

inductive Prim | add | sub | mul | lt | le | eq | and | or | not
  deriving DecidableEq, Repr

def Const.ty : Const → BTy
  | .int _ => .int
  | .bool _ => .bool

def Prim.args : Prim → List BTy
  | .add | .sub | .mul | .lt | .le | .eq => [.int, .int]
  | .and | .or => [.bool, .bool]
  | .not => [.bool]

def Prim.res : Prim → BTy
  | .add | .sub | .mul => .int
  | .lt | .le | .eq | .and | .or | .not => .bool

def Prim.interp : Prim → List Const → Option Const
  | .add, [.int a, .int b] => some (.int (a + b))
  | .sub, [.int a, .int b] => some (.int (a - b))
  | .mul, [.int a, .int b] => some (.int (a * b))
  | .lt, [.int a, .int b] => some (.bool (decide (a < b)))
  | .le, [.int a, .int b] => some (.bool (decide (a ≤ b)))
  | .eq, [.int a, .int b] => some (.bool (decide (a = b)))
  | .and, [.bool a, .bool b] => some (.bool (a && b))
  | .or, [.bool a, .bool b] => some (.bool (a || b))
  | .not, [.bool a] => some (.bool (!a))
  | _, _ => none

def Const.toBool : Const → Option Bool
  | .bool b => some b
  | .int _ => none

/-- Σ₁. -/
def S₁ : Sig where
  B := BTy
  C := Const
  P := Prim
  O := Empty
  cTy := Const.ty
  pArgs := Prim.args
  pRes := Prim.res
  pInterp := Prim.interp
  boolTy := .bool
  toBool := Const.toBool

/-- O₁ = ∅, so the effect arities are vacuous. -/
def E₁ : ESig S₁ where
  oArgs := fun o => nomatch o
  oRes := fun o => nomatch o

theorem lawful : S₁.Lawful where
  pTotal := by
    intro p cs h
    cases p <;>
    first
    | (rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨_, _⟩⟩⟩ <;> simp [S₁, Prim.args] at h <;>
       (try cases c₁) <;> (try cases c₂) <;> simp_all [S₁, Const.ty, Prim.interp, Prim.res])
  boolCanon := by
    intro c h
    cases c with
    | int n => simp [S₁, Const.ty] at h
    | bool b => exact ⟨b, rfl⟩

theorem noOps : S₁.O → False := fun o => nomatch o

/-! ## The L1 theorems at Σ₁ (OBJECT-L1 §§4–6), restated with no hypothesis about Σ left over. -/
abbrev Tm₁ := Tm S₁
abbrev Ty₁ := Ty S₁.B

theorem progress₁ (e : Tm₁) {τ} (h : HasType E₁ [] e τ) : e.IsTerminal ∨ ∃ e', Step e e' := progress lawful noOps e h
theorem preservation₁ {e e' : Tm₁} {τ} (hs : Step e e') (h : HasType E₁ [] e τ) : HasType E₁ [] e' τ :=
  preservation lawful hs h
theorem safety₁ {e e' : Tm₁} {τ} (h : HasType E₁ [] e τ) (hs : Steps e e') : e'.IsTerminal ∨ ∃ e'', Step e' e'' :=
  safety lawful noOps h hs
theorem den_typed₁ {e : Tm₁} {τ v} (h : HasType E₁ [] e τ) (hv : v ∈ den e) : v.IsValue ∧ HasTypeA E₁ [] v τ :=
  den_typed lawful h hv

end VIRL1.L1
