/-
  O95 layer L2, Lean arm. Y5's invariant: RUNTIME typing `RT Γ Δ Ω e τ`. ⊢₂ types SOURCE programs, whose capability operands
  are variables; a running configuration also has capability CONSTANTS ⟨p⟩, substituted by an O₂ step. RT is ⊢₂ with one
  more operand form: ⟨p⟩ for a base p in Ω, the list of regions the term OWNS (consumed by `store`/`free`, split by `let`,
  empty at a `ret` of a non-capability). Every source typing is a runtime typing with Ω = [] (`RT.ofTyped`).
  Plan (STAGE-L2-LEAN): substitution of a closed value (RT.subst, a ⟨p⟩ at a true-mask position), progress up to an INDEX
  fault (errata L2-E1, L2-E2), preservation with ownership of exactly Ω's regions, then the bounds-tolerant triple.
-/
import VIRL2.Subst2

namespace VIRL2
open VIRL1

inductive RT : Ctx S₂ → List Bool → List Int → Tm₂ → Ty₂ → Prop where
  | ret {Γ Δ a τ} : Mask.empty Δ → HasTypeA₂ Γ a τ → RT Γ Δ [] (.ret a) τ
  | retCap {Γ Δ n} : Γ[n]? = some tcap → Mask.only Δ n → RT Γ Δ [] (.ret (.var n)) tcap
  | retCapC {Γ Δ p} : Mask.empty Δ → RT Γ Δ [p] (.ret (.const (.cap p))) tcap
  | letE {Γ Δ Δ₁ Δ₂ Ω Ω₁ Ω₂ τ₁ τ₂ e₁ e₂} : Split Δ Δ₁ Δ₂ → Ω.Perm (Ω₁ ++ Ω₂) → (τ₁ = tcap ∨ hasCap τ₁ = false) →
      RT Γ Δ₁ Ω₁ e₁ τ₁ → RT (τ₁ :: Γ) (decide (τ₁ = tcap) :: Δ₂) Ω₂ e₂ τ₂ → RT Γ Δ Ω (.letE τ₁ e₁ e₂) τ₂
  | alloc {Γ Δ Ω a e τ} : HasTypeA₂ Γ a tint → RT (tcap :: Γ) (true :: Δ) Ω e τ → RT Γ Δ Ω (.letOp .alloc [a] tcap e) τ
  | load {Γ Δ Ω n a e τ} : Γ[n]? = some tcap → Δ[n]? = some true → HasTypeA₂ Γ a tint →
      RT (tint :: Γ) (false :: Δ) Ω e τ → RT Γ Δ Ω (.letOp .load [.var n, a] tint e) τ
  | loadC {Γ Δ Ω p a e τ} : p ∈ Ω → HasTypeA₂ Γ a tint →
      RT (tint :: Γ) (false :: Δ) Ω e τ → RT Γ Δ Ω (.letOp .load [.const (.cap p), a] tint e) τ
  | store {Γ Δ Ω n a₁ a₂ e τ} : Γ[n]? = some tcap → Δ[n]? = some true → HasTypeA₂ Γ a₁ tint → HasTypeA₂ Γ a₂ tint →
      RT (tcap :: Γ) (true :: Δ.set n false) Ω e τ → RT Γ Δ Ω (.letOp .store [.var n, a₁, a₂] tcap e) τ
  | storeC {Γ Δ Ω p a₁ a₂ e τ} : p ∈ Ω → HasTypeA₂ Γ a₁ tint → HasTypeA₂ Γ a₂ tint →
      RT (tcap :: Γ) (true :: Δ) (Ω.erase p) e τ → RT Γ Δ Ω (.letOp .store [.const (.cap p), a₁, a₂] tcap e) τ
  | free {Γ Δ Ω n e τ} : Γ[n]? = some tcap → Δ[n]? = some true →
      RT (tunit :: Γ) (false :: Δ.set n false) Ω e τ → RT Γ Δ Ω (.letOp .free [.var n] tunit e) τ
  | freeC {Γ Δ Ω p e τ} : p ∈ Ω → RT (tunit :: Γ) (false :: Δ) (Ω.erase p) e τ →
      RT Γ Δ Ω (.letOp .free [.const (.cap p)] tunit e) τ
  | app {Γ Δ a₁ a₂ τ₁ τ₂} : Mask.empty Δ → HasTypeA₂ Γ a₁ (.arr τ₁ τ₂) → HasTypeA₂ Γ a₂ τ₁ → RT Γ Δ [] (.app a₁ a₂) τ₂
  | ite {Γ Δ Ω a e₁ e₂ τ} : HasTypeA₂ Γ a tbool → RT Γ Δ Ω e₁ τ → RT Γ Δ Ω e₂ τ → RT Γ Δ Ω (.ite a e₁ e₂) τ
  | case {Γ Δ Ω a e₁ e₂ τ₁ τ₂ τ} : HasTypeA₂ Γ a (.sum τ₁ τ₂) → RT (τ₁ :: Γ) (false :: Δ) Ω e₁ τ →
      RT (τ₂ :: Γ) (false :: Δ) Ω e₂ τ → RT Γ Δ Ω (.case a e₁ e₂) τ

/-- Every source typing is a runtime typing that owns nothing. -/
theorem RT.ofTyped : ∀ {Γ Δ e τ}, HasType₂ Γ Δ e τ → RT Γ Δ [] e τ
  | _, _, _, _, .ret hΔ h => .ret hΔ h
  | _, _, _, _, .retCap hΓ hΔ => .retCap hΓ hΔ
  | _, _, _, _, .letE hs hc h₁ h₂ => .letE hs (by simp) hc (RT.ofTyped h₁) (RT.ofTyped h₂)
  | _, _, _, _, .alloc ha h => .alloc ha (RT.ofTyped h)
  | _, _, _, _, .load hΓ hΔ ha h => .load hΓ hΔ ha (RT.ofTyped h)
  | _, _, _, _, .store hΓ hΔ h₁ h₂ h => .store hΓ hΔ h₁ h₂ (RT.ofTyped h)
  | _, _, _, _, .free hΓ hΔ h => .free hΓ hΔ (RT.ofTyped h)
  | _, _, _, _, .app hΔ h₁ h₂ => .app hΔ h₁ h₂
  | _, _, _, _, .ite h h₁ h₂ => .ite h (RT.ofTyped h₁) (RT.ofTyped h₂)
  | _, _, _, _, .case h h₁ h₂ => .case h (RT.ofTyped h₁) (RT.ofTyped h₂)

/-- An INDEX fault (errata L2-E1, L2-E2): stuck at a `load`/`store` whose index is out of range for a LIVE region, or at an
  `alloc` whose size is non-positive; or such a fault in a `let`'s head. -/
inductive IndexFault : Config → Prop where
  | load {p i a τ e σ} {n : Nat} : Atom.eval (S := S₂) a = some (.const (Const.int i)) → σ.R.lookup p = some n → ¬ (0 ≤ i ∧ i < (n : Int)) →
      IndexFault (.letOp .load [.const (.cap p), a] τ e, σ)
  | store {p i a₁ a₂ τ e σ} {n : Nat} : Atom.eval (S := S₂) a₁ = some (.const (Const.int i)) → σ.R.lookup p = some n → ¬ (0 ≤ i ∧ i < (n : Int)) →
      IndexFault (.letOp .store [.const (.cap p), a₁, a₂] τ e, σ)
  | alloc {a k τ e σ} : Atom.eval (S := S₂) a = some (.const (Const.int k)) → k ≤ 0 → IndexFault (.letOp .alloc [a] τ e, σ)
  | letE {τ e₁ e₂ σ} : IndexFault (e₁, σ) → IndexFault (.letE τ e₁ e₂, σ)

end VIRL2
