/-
  O95 layer L2, Lean arm. OBJECT-L2 §4: ⊢₂, typing with a LINEAR context. `Γ ; Δ ⊢₂ e : τ` where Γ is L1's `Ctx` at Σ₂ and
  Δ is a USAGE MASK over Γ (l2/DECLARATIONS-LEAN.md): `Δ[n] = true` = the capability at index n is available.
  A NEW mutual inductive beside L1's `HasType`, because §4 checks a λ/fix body with Δ = ∅ UNDER ⊢₂ (an `alloc` inside a λ
  must be linear too); L1's `HasType` is reached by the embedding theorem (§4's last clause), never edited.
  Atoms never mention a capability: a variable whose type mentions `cap` is used only as an O₂ operand or by `ret`.
-/
import VIRL2.Step2

namespace VIRL2
open VIRL1

/-- A type mentions `cap`. -/
def hasCap : Ty₂ → Bool
  | .base b => decide (b = BTy.cap)
  | .arr t u | .prod t u | .sum t u => hasCap t || hasCap u

/-- Every entry of the mask is `false` (Δ = ∅). -/
def Mask.empty (Δ : List Bool) : Prop := ∀ n : Nat, Δ[n]? ≠ some true

/-- Δ = Δ₁ ⊎ Δ₂, pointwise: every available capability goes to exactly one side. -/
inductive Split : List Bool → List Bool → List Bool → Prop where
  | nil : Split [] [] []
  | left {Δ Δ₁ Δ₂} : Split Δ Δ₁ Δ₂ → Split (true :: Δ) (true :: Δ₁) (false :: Δ₂)
  | right {Δ Δ₁ Δ₂} : Split Δ Δ₁ Δ₂ → Split (true :: Δ) (false :: Δ₁) (true :: Δ₂)
  | none {Δ Δ₁ Δ₂} : Split Δ Δ₁ Δ₂ → Split (false :: Δ) (false :: Δ₁) (false :: Δ₂)

/-- Δ holds exactly the capability at index n. -/
def Mask.only (Δ : List Bool) (n : Nat) : Prop := Δ[n]? = some true ∧ ∀ m : Nat, m ≠ n → Δ[m]? ≠ some true

mutual
/-- Atoms at ⊢₂: L1's atom rules, with no capability anywhere (no `cap`-typed variable, no ⟨p⟩, no `cap` in a λ/fix type),
  and λ/fix bodies checked by ⊢₂ with Δ = ∅. -/
inductive HasTypeA₂ : Ctx S₂ → Atom₂ → Ty₂ → Prop where
  | var {Γ n τ} : Γ[n]? = some τ → hasCap τ = false → HasTypeA₂ Γ (.var n) τ
  | int {Γ n} : HasTypeA₂ Γ (.const (.int n)) tint
  | bool {Γ b} : HasTypeA₂ Γ (.const (.bool b)) tbool
  | unit {Γ} : HasTypeA₂ Γ (.const .unit) tunit
  | prim {Γ p as} : HasTypeL₂ Γ as ((S₂.pArgs p).map .base) → HasTypeA₂ Γ (.prim p as) (.base (S₂.pRes p))
  | lam {Γ τ₁ τ₂ e Δ} : hasCap τ₁ = false → hasCap τ₂ = false → Mask.empty Δ → Δ.length = Γ.length + 1 →
      HasType₂ (τ₁ :: Γ) Δ e τ₂ → HasTypeA₂ Γ (.lam τ₁ e) (.arr τ₁ τ₂)
  | fix {Γ τ₁ τ₂ e Δ} : hasCap τ₁ = false → hasCap τ₂ = false → Mask.empty Δ → Δ.length = Γ.length + 2 →
      HasType₂ (τ₁ :: .arr τ₁ τ₂ :: Γ) Δ e τ₂ → HasTypeA₂ Γ (.fix τ₁ τ₂ e) (.arr τ₁ τ₂)
  | pair {Γ a₁ a₂ τ₁ τ₂} : HasTypeA₂ Γ a₁ τ₁ → HasTypeA₂ Γ a₂ τ₂ → HasTypeA₂ Γ (.pair a₁ a₂) (.prod τ₁ τ₂)
  | fst {Γ a τ₁ τ₂} : HasTypeA₂ Γ a (.prod τ₁ τ₂) → HasTypeA₂ Γ (.fst a) τ₁
  | snd {Γ a τ₁ τ₂} : HasTypeA₂ Γ a (.prod τ₁ τ₂) → HasTypeA₂ Γ (.snd a) τ₂
  | inl {Γ a τ₁ τ₂} : hasCap τ₂ = false → HasTypeA₂ Γ a τ₁ → HasTypeA₂ Γ (.inl τ₂ a) (.sum τ₁ τ₂)
  | inr {Γ a τ₁ τ₂} : hasCap τ₁ = false → HasTypeA₂ Γ a τ₂ → HasTypeA₂ Γ (.inr τ₁ a) (.sum τ₁ τ₂)
inductive HasTypeL₂ : Ctx S₂ → List Atom₂ → List Ty₂ → Prop where
  | nil {Γ} : HasTypeL₂ Γ [] []
  | cons {Γ a as τ τs} : HasTypeA₂ Γ a τ → HasTypeL₂ Γ as τs → HasTypeL₂ Γ (a :: as) (τ :: τs)
/-- Expressions at ⊢₂ (OBJECT-L2 §4). `Δ.length = Γ.length` is kept by every rule from the root. -/
inductive HasType₂ : Ctx S₂ → List Bool → Tm₂ → Ty₂ → Prop where
  | ret {Γ Δ a τ} : Mask.empty Δ → HasTypeA₂ Γ a τ → HasType₂ Γ Δ (.ret a) τ
  | retCap {Γ Δ n} : Γ[n]? = some tcap → Mask.only Δ n → HasType₂ Γ Δ (.ret (.var n)) tcap
  | letE {Γ Δ Δ₁ Δ₂ τ₁ τ₂ e₁ e₂} : Split Δ Δ₁ Δ₂ → (τ₁ = tcap ∨ hasCap τ₁ = false) →
      HasType₂ Γ Δ₁ e₁ τ₁ → HasType₂ (τ₁ :: Γ) (decide (τ₁ = tcap) :: Δ₂) e₂ τ₂ → HasType₂ Γ Δ (.letE τ₁ e₁ e₂) τ₂
  | alloc {Γ Δ a e τ} : HasTypeA₂ Γ a tint → HasType₂ (tcap :: Γ) (true :: Δ) e τ →
      HasType₂ Γ Δ (.letOp .alloc [a] tcap e) τ
  | load {Γ Δ n a e τ} : Γ[n]? = some tcap → Δ[n]? = some true → HasTypeA₂ Γ a tint →
      HasType₂ (tint :: Γ) (false :: Δ) e τ → HasType₂ Γ Δ (.letOp .load [.var n, a] tint e) τ
  | store {Γ Δ n a₁ a₂ e τ} : Γ[n]? = some tcap → Δ[n]? = some true → HasTypeA₂ Γ a₁ tint → HasTypeA₂ Γ a₂ tint →
      HasType₂ (tcap :: Γ) (true :: Δ.set n false) e τ → HasType₂ Γ Δ (.letOp .store [.var n, a₁, a₂] tcap e) τ
  | free {Γ Δ n e τ} : Γ[n]? = some tcap → Δ[n]? = some true →
      HasType₂ (tunit :: Γ) (false :: Δ.set n false) e τ → HasType₂ Γ Δ (.letOp .free [.var n] tunit e) τ
  | app {Γ Δ a₁ a₂ τ₁ τ₂} : Mask.empty Δ → HasTypeA₂ Γ a₁ (.arr τ₁ τ₂) → HasTypeA₂ Γ a₂ τ₁ →
      HasType₂ Γ Δ (.app a₁ a₂) τ₂
  | ite {Γ Δ a e₁ e₂ τ} : HasTypeA₂ Γ a tbool → HasType₂ Γ Δ e₁ τ → HasType₂ Γ Δ e₂ τ → HasType₂ Γ Δ (.ite a e₁ e₂) τ
  | case {Γ Δ a e₁ e₂ τ₁ τ₂ τ} : HasTypeA₂ Γ a (.sum τ₁ τ₂) → HasType₂ (τ₁ :: Γ) (false :: Δ) e₁ τ →
      HasType₂ (τ₂ :: Γ) (false :: Δ) e₂ τ → HasType₂ Γ Δ (.case a e₁ e₂) τ
end

end VIRL2
