/-
  O95 layer L5, Lean arm (amend-24; l5/DECLARATIONS-LEAN.md and its Addendum 1). ⊢₅ = ⊢₂'s rules RESTATED for Tm₅ (L2's
  `HasType₂` is over Tm₂ and cannot see the new formers; part of `L5.syntaxCopy`), with the judgement carrying k, the number of
  capabilities the term hands back (Addendum 1 (2)), PLUS the L1′ rules of erratum L5-E1:
  * `lam`/`fix` at τ₁ →[k] τ₂: the body is checked with the k lent capabilities in Γ and Δ = exactly those, at (τ₂, k);
  * `retK a ds`: Δ = exactly the ds (distinct capability variables), a cap-free, at (τ, |ds|);
  * `appK a₁ a₂ cs`: a TAIL call lending cs = exactly Δ, at the callee's (τ₂, k);
  * `letK τ j e₁ e₂`: Δ SPLITS; e₁ at (τ, j) on its part; e₂ gets the rest plus the j capabilities handed back.
  Everything else, including `ret`'s Δ = ∅ (no leak) and the k = 0 L2 `app`, is L2's.
-/
import VIRL5.Syntax

namespace VIRL5
open VIRL1 VIRL2

abbrev Ctx₅ := List Ty₅

/-- The capability variables `ns` are DISTINCT, each a `cap` in Γ, and they are EXACTLY the live entries of Δ. -/
def CapsExact (Γ : Ctx₅) (Δ : List Bool) (ns : List Nat) : Prop :=
  ns.Nodup ∧ (∀ n ∈ ns, Γ[n]? = some t5cap) ∧ ∀ n, (Δ[n]? = some true ↔ n ∈ ns)

mutual
inductive HasTypeA₅ : Ctx₅ → Atom₅ → Ty₅ → Prop where
  | var {Γ n τ} : Γ[n]? = some τ → τ.hasCap = false → HasTypeA₅ Γ (.var n) τ
  | int {Γ n} : HasTypeA₅ Γ (.const (.int n)) t5int
  | bool {Γ b} : HasTypeA₅ Γ (.const (.bool b)) t5bool
  | unit {Γ} : HasTypeA₅ Γ (.const .unit) t5unit
  | prim {Γ p as} : HasTypeL₅ Γ as ((L1.Prim.args p).map fun b => .base (BTy.ofL1 b)) →
      HasTypeA₅ Γ (.prim p as) (.base (BTy.ofL1 (L1.Prim.res p)))
  | lam {Γ τ₁ k τ₂ e Δ₀} : τ₁.hasCap = false → τ₂.hasCap = false → Mask.empty Δ₀ → Δ₀.length = Γ.length + 1 →
      HasType₅ (List.replicate k t5cap ++ τ₁ :: Γ) (List.replicate k true ++ Δ₀) e τ₂ k →
      HasTypeA₅ Γ (.lam τ₁ k e) (.arr τ₁ k τ₂)
  | fix {Γ τ₁ k τ₂ e Δ₀} : τ₁.hasCap = false → τ₂.hasCap = false → Mask.empty Δ₀ → Δ₀.length = Γ.length + 2 →
      HasType₅ (List.replicate k t5cap ++ τ₁ :: .arr τ₁ k τ₂ :: Γ) (List.replicate k true ++ Δ₀) e τ₂ k →
      HasTypeA₅ Γ (.fix τ₁ k τ₂ e) (.arr τ₁ k τ₂)
  | pair {Γ a₁ a₂ τ₁ τ₂} : HasTypeA₅ Γ a₁ τ₁ → HasTypeA₅ Γ a₂ τ₂ → HasTypeA₅ Γ (.pair a₁ a₂) (.prod τ₁ τ₂)
  | fst {Γ a τ₁ τ₂} : HasTypeA₅ Γ a (.prod τ₁ τ₂) → HasTypeA₅ Γ (.fst a) τ₁
  | snd {Γ a τ₁ τ₂} : HasTypeA₅ Γ a (.prod τ₁ τ₂) → HasTypeA₅ Γ (.snd a) τ₂
  | inl {Γ a τ₁ τ₂} : τ₂.hasCap = false → HasTypeA₅ Γ a τ₁ → HasTypeA₅ Γ (.inl τ₂ a) (.sum τ₁ τ₂)
  | inr {Γ a τ₁ τ₂} : τ₁.hasCap = false → HasTypeA₅ Γ a τ₂ → HasTypeA₅ Γ (.inr τ₁ a) (.sum τ₁ τ₂)
inductive HasTypeL₅ : Ctx₅ → List Atom₅ → List Ty₅ → Prop where
  | nil {Γ} : HasTypeL₅ Γ [] []
  | cons {Γ a as τ τs} : HasTypeA₅ Γ a τ → HasTypeL₅ Γ as τs → HasTypeL₅ Γ (a :: as) (τ :: τs)
inductive HasType₅ : Ctx₅ → List Bool → Tm₅ → Ty₅ → Nat → Prop where
  | ret {Γ Δ a τ} : Mask.empty Δ → HasTypeA₅ Γ a τ → HasType₅ Γ Δ (.ret a) τ 0
  | retCap {Γ Δ n} : Γ[n]? = some t5cap → Mask.only Δ n → HasType₅ Γ Δ (.ret (.var n)) t5cap 0
  | letE {Γ Δ Δ₁ Δ₂ τ₁ τ₂ e₁ e₂ k} : Split Δ Δ₁ Δ₂ → (τ₁ = t5cap ∨ τ₁.hasCap = false) →
      HasType₅ Γ Δ₁ e₁ τ₁ 0 → HasType₅ (τ₁ :: Γ) (decide (τ₁ = t5cap) :: Δ₂) e₂ τ₂ k → HasType₅ Γ Δ (.letE τ₁ e₁ e₂) τ₂ k
  | alloc {Γ Δ a e τ k} : HasTypeA₅ Γ a t5int → HasType₅ (t5cap :: Γ) (true :: Δ) e τ k →
      HasType₅ Γ Δ (.letOp .alloc [a] t5cap e) τ k
  | load {Γ Δ n a e τ k} : Γ[n]? = some t5cap → Δ[n]? = some true → HasTypeA₅ Γ a t5int →
      HasType₅ (t5int :: Γ) (false :: Δ) e τ k → HasType₅ Γ Δ (.letOp .load [.var n, a] t5int e) τ k
  | store {Γ Δ n a₁ a₂ e τ k} : Γ[n]? = some t5cap → Δ[n]? = some true → HasTypeA₅ Γ a₁ t5int → HasTypeA₅ Γ a₂ t5int →
      HasType₅ (t5cap :: Γ) (true :: Δ.set n false) e τ k → HasType₅ Γ Δ (.letOp .store [.var n, a₁, a₂] t5cap e) τ k
  | free {Γ Δ n e τ k} : Γ[n]? = some t5cap → Δ[n]? = some true →
      HasType₅ (t5unit :: Γ) (false :: Δ.set n false) e τ k → HasType₅ Γ Δ (.letOp .free [.var n] t5unit e) τ k
  | app {Γ Δ a₁ a₂ τ₁ τ₂} : Mask.empty Δ → HasTypeA₅ Γ a₁ (.arr τ₁ 0 τ₂) → HasTypeA₅ Γ a₂ τ₁ →
      HasType₅ Γ Δ (.app a₁ a₂) τ₂ 0
  | ite {Γ Δ a e₁ e₂ τ k} : HasTypeA₅ Γ a t5bool → HasType₅ Γ Δ e₁ τ k → HasType₅ Γ Δ e₂ τ k →
      HasType₅ Γ Δ (.ite a e₁ e₂) τ k
  | case {Γ Δ a e₁ e₂ τ₁ τ₂ τ k} : HasTypeA₅ Γ a (.sum τ₁ τ₂) → HasType₅ (τ₁ :: Γ) (false :: Δ) e₁ τ k →
      HasType₅ (τ₂ :: Γ) (false :: Δ) e₂ τ k → HasType₅ Γ Δ (.case a e₁ e₂) τ k
  -- THE THREE (erratum L5-E1; DECLARATIONS-LEAN Addendum 1 (3)):
  | retK {Γ Δ a τ ns} : τ.hasCap = false → HasTypeA₅ Γ a τ → CapsExact Γ Δ ns →
      HasType₅ Γ Δ (.retK a (ns.map .var)) τ ns.length
  | appK {Γ Δ a₁ a₂ τ₁ τ₂ ns} : HasTypeA₅ Γ a₁ (.arr τ₁ ns.length τ₂) → HasTypeA₅ Γ a₂ τ₁ → CapsExact Γ Δ ns →
      HasType₅ Γ Δ (.appK a₁ a₂ (ns.map .var)) τ₂ ns.length
  | letK {Γ Δ Δ₁ Δ₂ τ₁ τ₂ j e₁ e₂ k} : Split Δ Δ₁ Δ₂ → τ₁.hasCap = false →
      HasType₅ Γ Δ₁ e₁ τ₁ j →
      HasType₅ (List.replicate j t5cap ++ τ₁ :: Γ) (List.replicate j true ++ false :: Δ₂) e₂ τ₂ k →
      HasType₅ Γ Δ (.letK τ₁ j e₁ e₂) τ₂ k
end

/-- The derived lending call of the declarations: `let x:τ₂, c₁′ … c_k′ ⇐ a₁ a₂ [c₁ … c_k] in e`. -/
def Tm₅.callK (τ₂ : Ty₅) (a₁ a₂ : Atom₅) (cs : List Atom₅) (e : Tm₅) : Tm₅ := .letK τ₂ cs.length (.appK a₁ a₂ cs) e

/-! ## CE's typing clause, the ⊢₂ → ⊢₅ direction (LV3): an L2 typing IS an L5 typing at k = 0, through ι. -/

theorem cap_ι (τ : Ty₂) : (ιT τ = t5cap) ↔ (τ = tcap) :=
  ⟨fun h => ιT_injective (by rw [h]; rfl), fun h => by rw [h]; rfl⟩

theorem getElem?_ι {Γ : Ctx S₂} {n : Nat} {τ : Ty₂} (h : Γ[n]? = some τ) : (Γ.map ιT)[n]? = some (ιT τ) := by
  simp [h]

theorem dec_ι (τ : Ty₂) : decide (ιT τ = t5cap) = decide (τ = tcap) := decide_eq_decide.mpr (cap_ι τ)

theorem capor_ι {τ : Ty₂} (h : τ = tcap ∨ hasCap τ = false) : ιT τ = t5cap ∨ (ιT τ).hasCap = false := by
  rcases h with h | h
  · exact .inl ((cap_ι τ).mpr h)
  · exact .inr (by rw [ιT_hasCap]; exact h)

mutual
theorem typeA_ι {Γ : Ctx S₂} {a : Atom₂} {τ : Ty₂} :
    HasTypeA₂ Γ a τ → HasTypeA₅ (Γ.map ιT) (ιA a) (ιT τ)
  | .var h hc => .var (getElem?_ι h) (by rw [ιT_hasCap]; exact hc)
  | .int => .int
  | .bool => .bool
  | .unit => .unit
  | .prim h => by
      have hl := typeL_ι h
      simp only [List.map_map] at hl
      exact .prim hl
  | .lam h₁ h₂ hΔ hl he =>
      .lam (k := 0) (by rw [ιT_hasCap]; exact h₁) (by rw [ιT_hasCap]; exact h₂) hΔ (by simp [hl]) (type_ι he)
  | .fix h₁ h₂ hΔ hl he =>
      .fix (k := 0) (by rw [ιT_hasCap]; exact h₁) (by rw [ιT_hasCap]; exact h₂) hΔ (by simp [hl]) (type_ι he)
  | .pair h₁ h₂ => .pair (typeA_ι h₁) (typeA_ι h₂)
  | .fst h => .fst (typeA_ι h)
  | .snd h => .snd (typeA_ι h)
  | .inl hc h => .inl (by rw [ιT_hasCap]; exact hc) (typeA_ι h)
  | .inr hc h => .inr (by rw [ιT_hasCap]; exact hc) (typeA_ι h)
theorem typeL_ι {Γ : Ctx S₂} {as : List Atom₂} {τs : List Ty₂} :
    HasTypeL₂ Γ as τs → HasTypeL₅ (Γ.map ιT) (ιL as) (τs.map ιT)
  | .nil => .nil
  | .cons h hs => .cons (typeA_ι h) (typeL_ι hs)
theorem type_ι {Γ : Ctx S₂} {Δ : List Bool} {e : Tm₂} {τ : Ty₂} :
    HasType₂ Γ Δ e τ → HasType₅ (Γ.map ιT) Δ (ιE e) (ιT τ) 0
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

end VIRL5
