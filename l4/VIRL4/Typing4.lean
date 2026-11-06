/-
  O95 layer L4, Lean arm (amend-21). ⊢₄ = ⊢₂'s rules, RESTATED for Tm₄ (L2's `HasType₂` is over Tm₂ and cannot see `par`;
  part of `L4.syntaxCopy`), PLUS FOUR (OBJECT-L4 §2): `newlock` consumes a capability, `acquire` returns one, `release`
  consumes one, `par` SPLITS Δ three ways (e₁ · e₂ · the body) and binds the two results one variable each (erratum L4-E1).
  `lock` is NON-linear: a lock-typed variable is an ordinary atom (H2 (a)). Lock handles ⟨ℓ⟩ are runtime-only, as ⟨p⟩ is in L2.
-/
import VIRL4.CE

namespace VIRL4
open VIRL1 VIRL2

abbrev Ctx₄ := List Ty₄

/-- A type mentions `cap` (a `lock` is not linear). -/
def hasCap₄ : Ty₄ → Bool
  | .base b => decide (b = BTy₄.cap)
  | .arr t u | .prod t u | .sum t u => hasCap₄ t || hasCap₄ u

def t4bool : Ty₄ := .base .bool

mutual
inductive HasTypeA₄ : Ctx₄ → Atom₄ → Ty₄ → Prop where
  | var {Γ n τ} : Γ[n]? = some τ → hasCap₄ τ = false → HasTypeA₄ Γ (.var n) τ
  | int {Γ n} : HasTypeA₄ Γ (.const (.c2 (.int n))) t4int
  | bool {Γ b} : HasTypeA₄ Γ (.const (.c2 (.bool b))) t4bool
  | unit {Γ} : HasTypeA₄ Γ (.const (.c2 .unit)) t4unit
  | prim {Γ p as} : HasTypeL₄ Γ as ((L1.Prim.args p).map fun b => .base (BTy₄.ofB2 (BTy.ofL1 b))) →
      HasTypeA₄ Γ (.prim p as) (.base (BTy₄.ofB2 (BTy.ofL1 (L1.Prim.res p))))
  | lam {Γ τ₁ τ₂ e Δ} : hasCap₄ τ₁ = false → hasCap₄ τ₂ = false → Mask.empty Δ → Δ.length = Γ.length + 1 →
      HasType₄ (τ₁ :: Γ) Δ e τ₂ → HasTypeA₄ Γ (.lam τ₁ e) (.arr τ₁ τ₂)
  | fix {Γ τ₁ τ₂ e Δ} : hasCap₄ τ₁ = false → hasCap₄ τ₂ = false → Mask.empty Δ → Δ.length = Γ.length + 2 →
      HasType₄ (τ₁ :: .arr τ₁ τ₂ :: Γ) Δ e τ₂ → HasTypeA₄ Γ (.fix τ₁ τ₂ e) (.arr τ₁ τ₂)
  | pair {Γ a₁ a₂ τ₁ τ₂} : HasTypeA₄ Γ a₁ τ₁ → HasTypeA₄ Γ a₂ τ₂ → HasTypeA₄ Γ (.pair a₁ a₂) (.prod τ₁ τ₂)
  | fst {Γ a τ₁ τ₂} : HasTypeA₄ Γ a (.prod τ₁ τ₂) → HasTypeA₄ Γ (.fst a) τ₁
  | snd {Γ a τ₁ τ₂} : HasTypeA₄ Γ a (.prod τ₁ τ₂) → HasTypeA₄ Γ (.snd a) τ₂
  | inl {Γ a τ₁ τ₂} : hasCap₄ τ₂ = false → HasTypeA₄ Γ a τ₁ → HasTypeA₄ Γ (.inl τ₂ a) (.sum τ₁ τ₂)
  | inr {Γ a τ₁ τ₂} : hasCap₄ τ₁ = false → HasTypeA₄ Γ a τ₂ → HasTypeA₄ Γ (.inr τ₁ a) (.sum τ₁ τ₂)
inductive HasTypeL₄ : Ctx₄ → List Atom₄ → List Ty₄ → Prop where
  | nil {Γ} : HasTypeL₄ Γ [] []
  | cons {Γ a as τ τs} : HasTypeA₄ Γ a τ → HasTypeL₄ Γ as τs → HasTypeL₄ Γ (a :: as) (τ :: τs)
inductive HasType₄ : Ctx₄ → List Bool → Tm₄ → Ty₄ → Prop where
  | ret {Γ Δ a τ} : Mask.empty Δ → HasTypeA₄ Γ a τ → HasType₄ Γ Δ (.ret a) τ
  | retCap {Γ Δ n} : Γ[n]? = some t4cap → Mask.only Δ n → HasType₄ Γ Δ (.ret (.var n)) t4cap
  | letE {Γ Δ Δ₁ Δ₂ τ₁ τ₂ e₁ e₂} : Split Δ Δ₁ Δ₂ → (τ₁ = t4cap ∨ hasCap₄ τ₁ = false) →
      HasType₄ Γ Δ₁ e₁ τ₁ → HasType₄ (τ₁ :: Γ) (decide (τ₁ = t4cap) :: Δ₂) e₂ τ₂ → HasType₄ Γ Δ (.letE τ₁ e₁ e₂) τ₂
  | alloc {Γ Δ a e τ} : HasTypeA₄ Γ a t4int → HasType₄ (t4cap :: Γ) (true :: Δ) e τ →
      HasType₄ Γ Δ (.letOp (.o2 .alloc) [a] t4cap e) τ
  | load {Γ Δ n a e τ} : Γ[n]? = some t4cap → Δ[n]? = some true → HasTypeA₄ Γ a t4int →
      HasType₄ (t4int :: Γ) (false :: Δ) e τ → HasType₄ Γ Δ (.letOp (.o2 .load) [.var n, a] t4int e) τ
  | store {Γ Δ n a₁ a₂ e τ} : Γ[n]? = some t4cap → Δ[n]? = some true → HasTypeA₄ Γ a₁ t4int → HasTypeA₄ Γ a₂ t4int →
      HasType₄ (t4cap :: Γ) (true :: Δ.set n false) e τ → HasType₄ Γ Δ (.letOp (.o2 .store) [.var n, a₁, a₂] t4cap e) τ
  | free {Γ Δ n e τ} : Γ[n]? = some t4cap → Δ[n]? = some true →
      HasType₄ (t4unit :: Γ) (false :: Δ.set n false) e τ → HasType₄ Γ Δ (.letOp (.o2 .free) [.var n] t4unit e) τ
  | app {Γ Δ a₁ a₂ τ₁ τ₂} : Mask.empty Δ → HasTypeA₄ Γ a₁ (.arr τ₁ τ₂) → HasTypeA₄ Γ a₂ τ₁ →
      HasType₄ Γ Δ (.app a₁ a₂) τ₂
  | ite {Γ Δ a e₁ e₂ τ} : HasTypeA₄ Γ a t4bool → HasType₄ Γ Δ e₁ τ → HasType₄ Γ Δ e₂ τ → HasType₄ Γ Δ (.ite a e₁ e₂) τ
  | case {Γ Δ a e₁ e₂ τ₁ τ₂ τ} : HasTypeA₄ Γ a (.sum τ₁ τ₂) → HasType₄ (τ₁ :: Γ) (false :: Δ) e₁ τ →
      HasType₄ (τ₂ :: Γ) (false :: Δ) e₂ τ → HasType₄ Γ Δ (.case a e₁ e₂) τ
  -- THE FOUR (OBJECT-L4 §2), each of a shape §4 already has:
  | newlock {Γ Δ n e τ} : Γ[n]? = some t4cap → Δ[n]? = some true →
      HasType₄ (t4lock :: Γ) (false :: Δ.set n false) e τ → HasType₄ Γ Δ (.letOp .newlock [.var n] t4lock e) τ
  | acquire {Γ Δ a e τ} : HasTypeA₄ Γ a t4lock → HasType₄ (t4cap :: Γ) (true :: Δ) e τ →
      HasType₄ Γ Δ (.letOp .acquire [a] t4cap e) τ
  | release {Γ Δ a n e τ} : HasTypeA₄ Γ a t4lock → Γ[n]? = some t4cap → Δ[n]? = some true →
      HasType₄ (t4unit :: Γ) (false :: Δ.set n false) e τ → HasType₄ Γ Δ (.letOp .release [a, .var n] t4unit e) τ
  | par {Γ Δ Δ₁ Δ' Δ₂ Δ₀ τ₁ τ₂ e₁ e₂ e τ} : Split Δ Δ₁ Δ' → Split Δ' Δ₂ Δ₀ →
      (τ₁ = t4cap ∨ hasCap₄ τ₁ = false) → (τ₂ = t4cap ∨ hasCap₄ τ₂ = false) →
      HasType₄ Γ Δ₁ e₁ τ₁ → HasType₄ Γ Δ₂ e₂ τ₂ →
      HasType₄ (τ₂ :: τ₁ :: Γ) (decide (τ₂ = t4cap) :: decide (τ₁ = t4cap) :: Δ₀) e τ →
      HasType₄ Γ Δ (.par τ₁ τ₂ e₁ e₂ e) τ
end

/-! ## CE's typing clause, the ⊢₂ → ⊢₄ direction: an L2 typing IS an L4 typing through ι. -/

theorem ofB2_inj : Function.Injective BTy₄.ofB2 := by
  intro a b h; cases a <;> cases b <;> first | rfl | cases h

theorem ofTy2_inj : Function.Injective Ty₄.ofTy2 := by
  intro a
  induction a with
  | base b => intro t h; cases t <;> simp [Ty₄.ofTy2] at h; exact congrArg _ (ofB2_inj h)
  | arr _ _ ih₁ ih₂ => intro t h; cases t <;> simp [Ty₄.ofTy2] at h; rw [ih₁ h.1, ih₂ h.2]
  | prod _ _ ih₁ ih₂ => intro t h; cases t <;> simp [Ty₄.ofTy2] at h; rw [ih₁ h.1, ih₂ h.2]
  | sum _ _ ih₁ ih₂ => intro t h; cases t <;> simp [Ty₄.ofTy2] at h; rw [ih₁ h.1, ih₂ h.2]

theorem hasCap_ι : ∀ τ : Ty₂, hasCap₄ (Ty₄.ofTy2 τ) = hasCap τ
  | .base b => by cases b <;> rfl
  | .arr t u | .prod t u | .sum t u => by simp [hasCap₄, hasCap, Ty₄.ofTy2, hasCap_ι t, hasCap_ι u]

theorem cap_ι (τ : Ty₂) : (Ty₄.ofTy2 τ = t4cap) ↔ (τ = tcap) :=
  ⟨fun h => ofTy2_inj (by rw [h]; rfl), fun h => by rw [h]; rfl⟩

theorem getElem?_ι {Γ : Ctx S₂} {n : Nat} {τ : Ty₂} (h : Γ[n]? = some τ) :
    (Γ.map Ty₄.ofTy2)[n]? = some (Ty₄.ofTy2 τ) := by
  simp [h]

theorem dec_ι (τ : Ty₂) : decide (Ty₄.ofTy2 τ = t4cap) = decide (τ = tcap) := decide_eq_decide.mpr (cap_ι τ)

theorem capor_ι {τ : Ty₂} (h : τ = tcap ∨ hasCap τ = false) : Ty₄.ofTy2 τ = t4cap ∨ hasCap₄ (Ty₄.ofTy2 τ) = false := by
  rcases h with h | h
  · exact .inl ((cap_ι τ).mpr h)
  · exact .inr (by rw [hasCap_ι]; exact h)

mutual
theorem typeA_ι {Γ : Ctx S₂} {a : Atom₂} {τ : Ty₂} :
    HasTypeA₂ Γ a τ → HasTypeA₄ (Γ.map Ty₄.ofTy2) (ιA a) (Ty₄.ofTy2 τ)
  | .var h hc => .var (getElem?_ι h) (by rw [hasCap_ι]; exact hc)
  | .int => .int
  | .bool => .bool
  | .unit => .unit
  | .prim h => by
      have hl := typeL_ι h
      simp only [List.map_map] at hl
      exact .prim hl
  | .lam h₁ h₂ hΔ hl he => .lam (by rw [hasCap_ι]; exact h₁) (by rw [hasCap_ι]; exact h₂) hΔ (by simp [hl]) (type_ι he)
  | .fix h₁ h₂ hΔ hl he => .fix (by rw [hasCap_ι]; exact h₁) (by rw [hasCap_ι]; exact h₂) hΔ (by simp [hl]) (type_ι he)
  | .pair h₁ h₂ => .pair (typeA_ι h₁) (typeA_ι h₂)
  | .fst h => .fst (typeA_ι h)
  | .snd h => .snd (typeA_ι h)
  | .inl hc h => .inl (by rw [hasCap_ι]; exact hc) (typeA_ι h)
  | .inr hc h => .inr (by rw [hasCap_ι]; exact hc) (typeA_ι h)
theorem typeL_ι {Γ : Ctx S₂} {as : List Atom₂} {τs : List Ty₂} :
    HasTypeL₂ Γ as τs → HasTypeL₄ (Γ.map Ty₄.ofTy2) (ιL as) (τs.map Ty₄.ofTy2)
  | .nil => .nil
  | .cons h hs => .cons (typeA_ι h) (typeL_ι hs)
theorem type_ι {Γ : Ctx S₂} {Δ : List Bool} {e : Tm₂} {τ : Ty₂} :
    HasType₂ Γ Δ e τ → HasType₄ (Γ.map Ty₄.ofTy2) Δ (ιT e) (Ty₄.ofTy2 τ)
  | .ret hΔ h => .ret hΔ (typeA_ι h)
  | .retCap h hΔ => .retCap (getElem?_ι h) hΔ
  | .letE (τ₁ := τ₁) hs hc h₁ h₂ => by
      have k := type_ι h₂
      rw [← dec_ι] at k
      exact .letE hs (capor_ι hc) (type_ι h₁) k
  | .alloc h he => .alloc (typeA_ι h) (type_ι he)
  | .load hn hΔ h he => .load (getElem?_ι hn) hΔ (typeA_ι h) (type_ι he)
  | .store hn hΔ h₁ h₂ he => .store (getElem?_ι hn) hΔ (typeA_ι h₁) (typeA_ι h₂) (type_ι he)
  | .free hn hΔ he => .free (getElem?_ι hn) hΔ (type_ι he)
  | .app hΔ h₁ h₂ => .app hΔ (typeA_ι h₁) (typeA_ι h₂)
  | .ite h h₁ h₂ => .ite (typeA_ι h) (type_ι h₁) (type_ι h₂)
  | .case h h₁ h₂ => .case (typeA_ι h) (type_ι h₁) (type_ι h₂)
end

end VIRL4
