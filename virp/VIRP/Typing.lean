/-
  O95 VIR program, Lean arm. STEP 4: the static semantics. Contexts are `List (Option Ty)`, index 0 innermost; a slot
  becomes `none` when its LINEAR (`tok`) or AFFINE (`slice`) variable is consumed. Atoms BORROW (they never consume): a guard
  may read `has_tokens(st, p)` and `len(b)`; `let_lin{dec_tokens(st, p); …}` and `return{(st, …)}` CONSUME the token,
  `advance{b; …}` MOVES the slice. A token must be consumed before `return` (no `some tok` left); `drop` aborts and may
  discard anything. Runtime literals (`tok`, `sl`) are typed in any context and consume nothing (`Use.val`).
-/
import VIRP.Semantics

namespace VIRP

abbrev Ctx := List (Option Ty)

/-- Atom typing (borrowing). -/
inductive ATy : Ctx → Atom → Ty → Prop where
  | var {Γ n τ} : Γ[n]? = some (some τ) → ATy Γ (.var n) τ
  | lit {Γ i} : ATy Γ (.lit i) .int
  | bool {Γ b} : ATy Γ (.bool b) .bool
  | sl {Γ o} : ATy Γ (.sl o) .slice
  | tok {Γ} : ATy Γ .tok .tok
  | magic {Γ} : ATy Γ .magic .int
  | len {Γ a} : ATy Γ a .slice → ATy Γ (.len a) .int
  | ge {Γ a b} : ATy Γ a .int → ATy Γ b .int → ATy Γ (.ge a b) .bool
  | eq {Γ a b} : ATy Γ a .int → ATy Γ b .int → ATy Γ (.eq a b) .bool
  | and {Γ a b} : ATy Γ a .bool → ATy Γ b .bool → ATy Γ (.and a b) .bool
  | canAccess {Γ p t} : ATy Γ p .int → ATy Γ t .int → ATy Γ (.canAccess p t) .bool
  | hasTokens {Γ s p} : ATy Γ s .tok → ATy Γ p .int → ATy Γ (.hasTokens s p) .bool

/-- Consuming an operand: a variable's slot is marked used; a closed (runtime) operand consumes nothing. -/
inductive Use : Ctx → Atom → Ty → Ctx → Prop where
  | var {Γ n τ} : Γ[n]? = some (some τ) → Use Γ (.var n) τ (Γ.set n none)
  | val {Γ a τ} : ATy [] a τ → Use Γ a τ Γ

/-- Expression typing. -/
inductive HasType : Ctx → Tm → Prop where
  | letLinDec {Γ Γ' s p e} : Use Γ s .tok Γ' → ATy Γ p .int → HasType (some .tok :: Γ') e →
      HasType Γ (.letLinDec s p e)
  | advance {Γ Γ' b i e} : Use Γ b .slice Γ' → HasType (some .slice :: Γ') e → HasType Γ (.advance b i e)
  | readU32 {Γ b j e} : ATy Γ b .slice → HasType (some .int :: Γ) e → HasType Γ (.readU32 b j e)
  | guard {Γ c ok err} : ATy Γ c .bool → HasType Γ ok → HasType Γ err → HasType Γ (.guard c ok err)
  | ret {Γ Γ' s b} : Use Γ s .tok Γ' → ATy Γ' b .slice → some .tok ∉ Γ' → HasType Γ (.ret s b)
  | drop {Γ c} : HasType Γ (.drop c)

/-- Values and their types. -/
inductive VTy : Val → Ty → Prop where
  | int {i} : VTy (.int i) .int
  | bool {b} : VTy (.bool b) .bool
  | sl {o} : VTy (.sl o) .slice
  | tok : VTy .tok .tok

/-- An environment realises a context: every live slot holds a value of its type. -/
def EnvOK (Γ : Ctx) (env : List Val) : Prop :=
  ∀ (n : Nat) (τ : Ty), Γ[n]? = some (some τ) → ∃ v, env[n]? = some v ∧ VTy v τ

end VIRP
