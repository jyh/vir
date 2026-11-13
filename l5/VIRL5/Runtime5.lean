/-
  O95 layer L5, Lean arm (amend-24 LV4; DECLARATIONS-LEAN "semantic typing is proved as L2's Y5 was, SYNTACTICALLY"). RUNTIME
  typing `RT₅ Γ Δ Ω e τ k`: ⊢₅ with one more operand form, ⟨p⟩ for a base p in Ω, the regions the term OWNS (L2's `RT`, restated).
  The L1′ rules carry a capability LIST whose members are variables (accounted by Δ, as `CapsExact`) or constants ⟨p⟩ (accounted
  by Ω, as a permutation): `CapsRT`. A running `appK`/`retK` lends or hands back exactly those; `letK` splits Δ and Ω.
  Every source typing is a runtime typing that owns nothing (`RT₅.ofTyped`).
-/
import VIRL5.Subst5
import VIRL5.Step5

namespace VIRL5
open VIRL1 VIRL2

/-- The capability variables of a list (its `.var` members, in order). -/
def capVars : List Atom₅ → List Nat
  | [] => []
  | .var n :: ds => n :: capVars ds
  | _ :: ds => capVars ds

/-- The capability constants of a list (its ⟨p⟩ members, in order). -/
def capPtrs : List Atom₅ → List Int
  | [] => []
  | .const (.cap p) :: ds => p :: capPtrs ds
  | _ :: ds => capPtrs ds

/-- Each member is a capability variable or a capability constant. -/
def CapForm (d : Atom₅) : Prop := (∃ n, d = .var n) ∨ ∃ p, d = .const (.cap p)

/-- A runtime capability list: its variables are exactly Δ (as `CapsExact`), its constants are exactly Ω (up to order). -/
def CapsRT (Γ : Ctx₅) (Δ : List Bool) (Ω : List Int) (ds : List Atom₅) : Prop :=
  (∀ d ∈ ds, CapForm d) ∧ CapsExact Γ Δ (capVars ds) ∧ Ω.Perm (capPtrs ds)

inductive RT₅ : Ctx₅ → List Bool → List Int → Tm₅ → Ty₅ → Nat → Prop where
  | ret {Γ Δ a τ} : Mask.empty Δ → HasTypeA₅ Γ a τ → RT₅ Γ Δ [] (.ret a) τ 0
  | retCap {Γ Δ n} : Γ[n]? = some t5cap → Mask.only Δ n → RT₅ Γ Δ [] (.ret (.var n)) t5cap 0
  | retCapC {Γ Δ p} : Mask.empty Δ → RT₅ Γ Δ [p] (.ret (.const (.cap p))) t5cap 0
  | letE {Γ Δ Δ₁ Δ₂ Ω Ω₁ Ω₂ τ₁ τ₂ e₁ e₂ k} : Split Δ Δ₁ Δ₂ → Ω.Perm (Ω₁ ++ Ω₂) → (τ₁ = t5cap ∨ τ₁.hasCap = false) →
      RT₅ Γ Δ₁ Ω₁ e₁ τ₁ 0 → RT₅ (τ₁ :: Γ) (decide (τ₁ = t5cap) :: Δ₂) Ω₂ e₂ τ₂ k → RT₅ Γ Δ Ω (.letE τ₁ e₁ e₂) τ₂ k
  | alloc {Γ Δ Ω a e τ k} : HasTypeA₅ Γ a t5int → RT₅ (t5cap :: Γ) (true :: Δ) Ω e τ k →
      RT₅ Γ Δ Ω (.letOp .alloc [a] t5cap e) τ k
  | load {Γ Δ Ω n a e τ k} : Γ[n]? = some t5cap → Δ[n]? = some true → HasTypeA₅ Γ a t5int →
      RT₅ (t5int :: Γ) (false :: Δ) Ω e τ k → RT₅ Γ Δ Ω (.letOp .load [.var n, a] t5int e) τ k
  | loadC {Γ Δ Ω p a e τ k} : p ∈ Ω → HasTypeA₅ Γ a t5int →
      RT₅ (t5int :: Γ) (false :: Δ) Ω e τ k → RT₅ Γ Δ Ω (.letOp .load [.const (.cap p), a] t5int e) τ k
  | store {Γ Δ Ω n a₁ a₂ e τ k} : Γ[n]? = some t5cap → Δ[n]? = some true → HasTypeA₅ Γ a₁ t5int → HasTypeA₅ Γ a₂ t5int →
      RT₅ (t5cap :: Γ) (true :: Δ.set n false) Ω e τ k → RT₅ Γ Δ Ω (.letOp .store [.var n, a₁, a₂] t5cap e) τ k
  | storeC {Γ Δ Ω p a₁ a₂ e τ k} : p ∈ Ω → HasTypeA₅ Γ a₁ t5int → HasTypeA₅ Γ a₂ t5int →
      RT₅ (t5cap :: Γ) (true :: Δ) (Ω.erase p) e τ k → RT₅ Γ Δ Ω (.letOp .store [.const (.cap p), a₁, a₂] t5cap e) τ k
  | free {Γ Δ Ω n e τ k} : Γ[n]? = some t5cap → Δ[n]? = some true →
      RT₅ (t5unit :: Γ) (false :: Δ.set n false) Ω e τ k → RT₅ Γ Δ Ω (.letOp .free [.var n] t5unit e) τ k
  | freeC {Γ Δ Ω p e τ k} : p ∈ Ω → RT₅ (t5unit :: Γ) (false :: Δ) (Ω.erase p) e τ k →
      RT₅ Γ Δ Ω (.letOp .free [.const (.cap p)] t5unit e) τ k
  | app {Γ Δ a₁ a₂ τ₁ τ₂} : Mask.empty Δ → HasTypeA₅ Γ a₁ (.arr τ₁ 0 τ₂) → HasTypeA₅ Γ a₂ τ₁ →
      RT₅ Γ Δ [] (.app a₁ a₂) τ₂ 0
  | ite {Γ Δ Ω a e₁ e₂ τ k} : HasTypeA₅ Γ a t5bool → RT₅ Γ Δ Ω e₁ τ k → RT₅ Γ Δ Ω e₂ τ k → RT₅ Γ Δ Ω (.ite a e₁ e₂) τ k
  | case {Γ Δ Ω a e₁ e₂ τ₁ τ₂ τ k} : HasTypeA₅ Γ a (.sum τ₁ τ₂) → RT₅ (τ₁ :: Γ) (false :: Δ) Ω e₁ τ k →
      RT₅ (τ₂ :: Γ) (false :: Δ) Ω e₂ τ k → RT₅ Γ Δ Ω (.case a e₁ e₂) τ k
  -- THE THREE, at runtime:
  | retK {Γ Δ Ω a τ ds} : τ.hasCap = false → HasTypeA₅ Γ a τ → CapsRT Γ Δ Ω ds →
      RT₅ Γ Δ Ω (.retK a ds) τ ds.length
  | appK {Γ Δ Ω a₁ a₂ τ₁ τ₂ ds} : HasTypeA₅ Γ a₁ (.arr τ₁ ds.length τ₂) → HasTypeA₅ Γ a₂ τ₁ → CapsRT Γ Δ Ω ds →
      RT₅ Γ Δ Ω (.appK a₁ a₂ ds) τ₂ ds.length
  | letK {Γ Δ Δ₁ Δ₂ Ω Ω₁ Ω₂ τ₁ τ₂ j e₁ e₂ k} : Split Δ Δ₁ Δ₂ → Ω.Perm (Ω₁ ++ Ω₂) → τ₁.hasCap = false →
      RT₅ Γ Δ₁ Ω₁ e₁ τ₁ j →
      RT₅ (List.replicate j t5cap ++ τ₁ :: Γ) (List.replicate j true ++ false :: Δ₂) Ω₂ e₂ τ₂ k →
      RT₅ Γ Δ Ω (.letK τ₁ j e₁ e₂) τ₂ k

theorem capVars_vars : ∀ ns : List Nat, capVars (ns.map Atom₅.var) = ns
  | [] => rfl
  | n :: ns => by simp [capVars, capVars_vars ns]

theorem capPtrs_vars : ∀ ns : List Nat, capPtrs (ns.map Atom₅.var) = []
  | [] => rfl
  | n :: ns => by simp [capPtrs, capPtrs_vars ns]

theorem CapsRT.ofExact {Γ : Ctx₅} {Δ : List Bool} {ns : List Nat} (h : CapsExact Γ Δ ns) : CapsRT Γ Δ [] (ns.map .var) :=
  ⟨fun d hd => by obtain ⟨n, -, rfl⟩ := List.mem_map.1 hd; exact .inl ⟨n, rfl⟩,
   by rw [capVars_vars]; exact h, by rw [capPtrs_vars]⟩

/-- Every source typing is a runtime typing that owns nothing. -/
theorem RT₅.ofTyped : ∀ {Γ Δ e τ k}, HasType₅ Γ Δ e τ k → RT₅ Γ Δ [] e τ k
  | _, _, _, _, _, .ret hΔ h => .ret hΔ h
  | _, _, _, _, _, .retCap hΓ hΔ => .retCap hΓ hΔ
  | _, _, _, _, _, .letE hs hc h₁ h₂ => .letE hs (by simp) hc (RT₅.ofTyped h₁) (RT₅.ofTyped h₂)
  | _, _, _, _, _, .alloc ha h => .alloc ha (RT₅.ofTyped h)
  | _, _, _, _, _, .load hΓ hΔ ha h => .load hΓ hΔ ha (RT₅.ofTyped h)
  | _, _, _, _, _, .store hΓ hΔ h₁ h₂ h => .store hΓ hΔ h₁ h₂ (RT₅.ofTyped h)
  | _, _, _, _, _, .free hΓ hΔ h => .free hΓ hΔ (RT₅.ofTyped h)
  | _, _, _, _, _, .app hΔ h₁ h₂ => .app hΔ h₁ h₂
  | _, _, _, _, _, .ite h h₁ h₂ => .ite h (RT₅.ofTyped h₁) (RT₅.ofTyped h₂)
  | _, _, _, _, _, .case h h₁ h₂ => .case h (RT₅.ofTyped h₁) (RT₅.ofTyped h₂)
  | _, _, _, _, _, .retK (ns := ns) hc h hx => by
      have := RT₅.retK hc h (CapsRT.ofExact hx); rwa [List.length_map] at this
  | _, _, _, _, _, .appK (ns := ns) h₁ h₂ hx => by
      rw [← List.length_map (f := Atom₅.var)] at h₁
      have := RT₅.appK h₁ h₂ (CapsRT.ofExact hx); rwa [List.length_map] at this
  | _, _, _, _, _, .letK hs hc h₁ h₂ => .letK hs (by simp) hc (RT₅.ofTyped h₁) (RT₅.ofTyped h₂)

theorem CapsRT.perm {Γ : Ctx₅} {Δ : List Bool} {Ω Ω' : List Int} {ds : List Atom₅} (hp : Ω.Perm Ω') (h : CapsRT Γ Δ Ω ds) :
    CapsRT Γ Δ Ω' ds :=
  ⟨h.1, h.2.1, hp.symm.trans h.2.2⟩

/-- RT₅ is invariant under permuting what it owns. -/
theorem RT₅.perm : ∀ {Γ Δ Ω Ω' e τ k}, Ω.Perm Ω' → RT₅ Γ Δ Ω e τ k → RT₅ Γ Δ Ω' e τ k
  | _, _, _, _, _, _, _, hp, .ret hΔ h => by rw [List.perm_nil.1 hp.symm]; exact .ret hΔ h
  | _, _, _, _, _, _, _, hp, .retCap hΓ hΔ => by rw [List.perm_nil.1 hp.symm]; exact .retCap hΓ hΔ
  | _, _, _, _, _, _, _, hp, .retCapC hΔ => by rw [List.perm_singleton.1 hp.symm]; exact .retCapC hΔ
  | _, _, _, _, _, _, _, hp, .letE hs hp' hc h₁ h₂ => .letE hs (hp.symm.trans hp') hc h₁ h₂
  | _, _, _, _, _, _, _, hp, .alloc ha h => .alloc ha (RT₅.perm hp h)
  | _, _, _, _, _, _, _, hp, .load hΓ hΔ ha h => .load hΓ hΔ ha (RT₅.perm hp h)
  | _, _, _, _, _, _, _, hp, .loadC hm ha h => .loadC (hp.subset hm) ha (RT₅.perm hp h)
  | _, _, _, _, _, _, _, hp, .store hΓ hΔ h₁ h₂ h => .store hΓ hΔ h₁ h₂ (RT₅.perm hp h)
  | _, _, _, _, _, _, _, hp, .storeC hm h₁ h₂ h => .storeC (hp.subset hm) h₁ h₂ (RT₅.perm (hp.erase _) h)
  | _, _, _, _, _, _, _, hp, .free hΓ hΔ h => .free hΓ hΔ (RT₅.perm hp h)
  | _, _, _, _, _, _, _, hp, .freeC hm h => .freeC (hp.subset hm) (RT₅.perm (hp.erase _) h)
  | _, _, _, _, _, _, _, hp, .app hΔ h₁ h₂ => by rw [List.perm_nil.1 hp.symm]; exact .app hΔ h₁ h₂
  | _, _, _, _, _, _, _, hp, .ite h h₁ h₂ => .ite h (RT₅.perm hp h₁) (RT₅.perm hp h₂)
  | _, _, _, _, _, _, _, hp, .case h h₁ h₂ => .case h (RT₅.perm hp h₁) (RT₅.perm hp h₂)
  | _, _, _, _, _, _, _, hp, .retK hc h hx => .retK hc h (hx.perm hp)
  | _, _, _, _, _, _, _, hp, .appK h₁ h₂ hx => .appK h₁ h₂ (hx.perm hp)
  | _, _, _, _, _, _, _, hp, .letK hs hp' hc h₁ h₂ => .letK hs (hp.symm.trans hp') hc h₁ h₂

/-- An INDEX fault (errata L2-E1, L2-E2, carried up): L2's, over Tm₅, and under `letK`'s head as under `letE`'s. -/
inductive IndexFault₅ : Config₅ → Prop where
  | load {p i a τ e σ} {n : Nat} : Atom₅.eval a = some (.const (Const.int i)) → σ.R.lookup p = some n →
      ¬ (0 ≤ i ∧ i < (n : Int)) → IndexFault₅ (.letOp .load [.const (.cap p), a] τ e, σ)
  | store {p i a₁ a₂ τ e σ} {n : Nat} : Atom₅.eval a₁ = some (.const (Const.int i)) → σ.R.lookup p = some n →
      ¬ (0 ≤ i ∧ i < (n : Int)) → IndexFault₅ (.letOp .store [.const (.cap p), a₁, a₂] τ e, σ)
  | alloc {a k τ e σ} : Atom₅.eval a = some (.const (Const.int k)) → k ≤ 0 → IndexFault₅ (.letOp .alloc [a] τ e, σ)
  | letE {τ e₁ e₂ σ} : IndexFault₅ (e₁, σ) → IndexFault₅ (.letE τ e₁ e₂, σ)
  | letK {τ j e₁ e₂ σ} : IndexFault₅ (e₁, σ) → IndexFault₅ (.letK τ j e₁ e₂, σ)

end VIRL5
