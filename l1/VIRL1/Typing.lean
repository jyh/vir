/-
  O95 layer L1, Lean arm. STEP 4: the static semantics (OBJECT-L1 §4), for an ARBITRARY signature.
  E2: typing is a `Prop`-valued mutual inductive. Contexts are lists, index 0 innermost (de Bruijn).
  Required here: uniqueness, weakening, the substitution lemma (atoms and expressions).
  Every proof recurses STRUCTURALLY ON THE TERM (data) and inverts the derivation.
-/
import VIRL1.Semantics

namespace VIRL1
variable {S : Sig} (E : ESig S)

abbrev Ctx (S : Sig) := List (Ty S.B)

mutual
inductive HasTypeA : Ctx S → Atom S → Ty S.B → Prop where
  | var {Γ n τ} : Γ[n]? = some τ → HasTypeA Γ (.var n) τ
  | const {Γ c} : HasTypeA Γ (.const c) (.base (S.cTy c))
  | prim {Γ p as} : HasTypeL Γ as ((S.pArgs p).map .base) → HasTypeA Γ (.prim p as) (.base (S.pRes p))
  | lam {Γ τ₁ τ₂ e} : HasType (τ₁ :: Γ) e τ₂ → HasTypeA Γ (.lam τ₁ e) (.arr τ₁ τ₂)
  | fix {Γ τ₁ τ₂ e} : HasType (τ₁ :: .arr τ₁ τ₂ :: Γ) e τ₂ → HasTypeA Γ (.fix τ₁ τ₂ e) (.arr τ₁ τ₂)
  | pair {Γ a₁ a₂ τ₁ τ₂} : HasTypeA Γ a₁ τ₁ → HasTypeA Γ a₂ τ₂ → HasTypeA Γ (.pair a₁ a₂) (.prod τ₁ τ₂)
  | fst {Γ a τ₁ τ₂} : HasTypeA Γ a (.prod τ₁ τ₂) → HasTypeA Γ (.fst a) τ₁
  | snd {Γ a τ₁ τ₂} : HasTypeA Γ a (.prod τ₁ τ₂) → HasTypeA Γ (.snd a) τ₂
  | inl {Γ a τ₁ τ₂} : HasTypeA Γ a τ₁ → HasTypeA Γ (.inl τ₂ a) (.sum τ₁ τ₂)
  | inr {Γ a τ₁ τ₂} : HasTypeA Γ a τ₂ → HasTypeA Γ (.inr τ₁ a) (.sum τ₁ τ₂)
inductive HasTypeL : Ctx S → List (Atom S) → List (Ty S.B) → Prop where
  | nil {Γ} : HasTypeL Γ [] []
  | cons {Γ a as τ τs} : HasTypeA Γ a τ → HasTypeL Γ as τs → HasTypeL Γ (a :: as) (τ :: τs)
inductive HasType : Ctx S → Tm S → Ty S.B → Prop where
  | ret {Γ a τ} : HasTypeA Γ a τ → HasType Γ (.ret a) τ
  | letE {Γ τ₁ τ₂ e₁ e₂} : HasType Γ e₁ τ₁ → HasType (τ₁ :: Γ) e₂ τ₂ → HasType Γ (.letE τ₁ e₁ e₂) τ₂
  | letOp {Γ o as e τ'} : HasTypeL Γ as (E.oArgs o) → HasType (E.oRes o :: Γ) e τ' →
      HasType Γ (.letOp o as (E.oRes o) e) τ'
  | app {Γ a₁ a₂ τ₁ τ₂} : HasTypeA Γ a₁ (.arr τ₁ τ₂) → HasTypeA Γ a₂ τ₁ → HasType Γ (.app a₁ a₂) τ₂
  | ite {Γ a e₁ e₂ τ} : HasTypeA Γ a (.base S.boolTy) → HasType Γ e₁ τ → HasType Γ e₂ τ → HasType Γ (.ite a e₁ e₂) τ
  | case {Γ a e₁ e₂ τ₁ τ₂ τ} : HasTypeA Γ a (.sum τ₁ τ₂) → HasType (τ₁ :: Γ) e₁ τ → HasType (τ₂ :: Γ) e₂ τ →
      HasType Γ (.case a e₁ e₂) τ
end

variable {E}

/-! ## Uniqueness of typing (syntax-directed: every binder is annotated). -/
mutual
theorem HasTypeA.unique : ∀ {Γ : Ctx S} (a : Atom S) {τ τ'}, HasTypeA E Γ a τ → HasTypeA E Γ a τ' → τ = τ'
  | _, .var n, _, _, .var h, .var h' => Option.some.inj (h.symm.trans h')
  | _, .const _, _, _, .const, .const => rfl
  | _, .prim _ _, _, _, .prim _, .prim _ => rfl
  | _, .lam _ e, _, _, .lam h, .lam h' => by rw [HasType.unique e h h']
  | _, .fix _ _ _, _, _, .fix _, .fix _ => rfl
  | _, .pair a₁ a₂, _, _, .pair h₁ h₂, .pair h₁' h₂' => by
      rw [HasTypeA.unique a₁ h₁ h₁', HasTypeA.unique a₂ h₂ h₂']
  | _, .fst a, _, _, .fst h, .fst h' => by
      have := HasTypeA.unique a h h'; cases this; rfl
  | _, .snd a, _, _, .snd h, .snd h' => by
      have := HasTypeA.unique a h h'; cases this; rfl
  | _, .inl _ a, _, _, .inl h, .inl h' => by rw [HasTypeA.unique a h h']
  | _, .inr _ a, _, _, .inr h, .inr h' => by rw [HasTypeA.unique a h h']
theorem HasType.unique : ∀ {Γ : Ctx S} (e : Tm S) {τ τ'}, HasType E Γ e τ → HasType E Γ e τ' → τ = τ'
  | _, .ret a, _, _, .ret h, .ret h' => HasTypeA.unique a h h'
  | _, .letE _ _ e₂, _, _, .letE _ h, .letE _ h' => HasType.unique e₂ h h'
  | _, .letOp _ _ _ e, _, _, .letOp _ h, .letOp _ h' => HasType.unique e h h'
  | _, .app a₁ _, _, _, .app h _, .app h' _ => by
      have := HasTypeA.unique a₁ h h'; cases this; rfl
  | _, .ite _ e₁ _, _, _, .ite _ h _, .ite _ h' _ => HasType.unique e₁ h h'
  | _, .case a e₁ _, _, _, .case ha h _, .case ha' h' _ => by
      have := HasTypeA.unique a ha ha'; cases this; exact HasType.unique e₁ h h'
end

/-! ## Weakening at the OUTER end of the context (no shift is needed: indices of the inner part are unchanged). -/
mutual
theorem HasTypeA.weaken : ∀ {Γ : Ctx S} (a : Atom S) {τ} (Δ : Ctx S), HasTypeA E Γ a τ → HasTypeA E (Γ ++ Δ) a τ
  | _, .var n, _, Δ, .var h => .var (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h)
  | _, .const _, _, _, .const => .const
  | _, .prim _ as, _, Δ, .prim h => .prim (HasTypeL.weaken as Δ h)
  | _, .lam _ e, _, Δ, .lam h => .lam (HasType.weaken e Δ h)
  | _, .fix _ _ e, _, Δ, .fix h => .fix (HasType.weaken e Δ h)
  | _, .pair a₁ a₂, _, Δ, .pair h₁ h₂ => .pair (HasTypeA.weaken a₁ Δ h₁) (HasTypeA.weaken a₂ Δ h₂)
  | _, .fst a, _, Δ, .fst h => .fst (HasTypeA.weaken a Δ h)
  | _, .snd a, _, Δ, .snd h => .snd (HasTypeA.weaken a Δ h)
  | _, .inl _ a, _, Δ, .inl h => .inl (HasTypeA.weaken a Δ h)
  | _, .inr _ a, _, Δ, .inr h => .inr (HasTypeA.weaken a Δ h)
theorem HasTypeL.weaken : ∀ {Γ : Ctx S} (as : List (Atom S)) {τs} (Δ : Ctx S), HasTypeL E Γ as τs → HasTypeL E (Γ ++ Δ) as τs
  | _, [], _, _, .nil => .nil
  | _, a :: as, _, Δ, .cons h hs => .cons (HasTypeA.weaken a Δ h) (HasTypeL.weaken as Δ hs)
theorem HasType.weaken : ∀ {Γ : Ctx S} (e : Tm S) {τ} (Δ : Ctx S), HasType E Γ e τ → HasType E (Γ ++ Δ) e τ
  | _, .ret a, _, Δ, .ret h => .ret (HasTypeA.weaken a Δ h)
  | _, .letE _ e₁ e₂, _, Δ, .letE h₁ h₂ => .letE (HasType.weaken e₁ Δ h₁) (HasType.weaken e₂ Δ h₂)
  | _, .letOp _ as _ e, _, Δ, .letOp h₁ h₂ => .letOp (HasTypeL.weaken as Δ h₁) (HasType.weaken e Δ h₂)
  | _, .app a₁ a₂, _, Δ, .app h₁ h₂ => .app (HasTypeA.weaken a₁ Δ h₁) (HasTypeA.weaken a₂ Δ h₂)
  | _, .ite a e₁ e₂, _, Δ, .ite h h₁ h₂ => .ite (HasTypeA.weaken a Δ h) (HasType.weaken e₁ Δ h₁) (HasType.weaken e₂ Δ h₂)
  | _, .case a e₁ e₂, _, Δ, .case h h₁ h₂ => .case (HasTypeA.weaken a Δ h) (HasType.weaken e₁ Δ h₁) (HasType.weaken e₂ Δ h₂)
end

/-- A closed value types in every context. -/
theorem HasTypeA.closed {v : Atom S} {τ} (Γ : Ctx S) (h : HasTypeA E [] v τ) : HasTypeA E Γ v τ := by
  simpa using HasTypeA.weaken v Γ h

/-! ## The substitution lemma (OBJECT-L1 §4), at any depth `Δ.length`, for a closed value. -/
theorem lookup_subst {Δ Γ : Ctx S} {τ σ : Ty S.B} {n : Nat} (h : (Δ ++ τ :: Γ)[n]? = some σ) (hn : ¬ n < Δ.length)
    (hk : ¬ n = Δ.length) : (Δ ++ Γ)[n - 1]? = some σ := by
  have h1 : Δ.length < n := by omega
  rw [List.getElem?_append_right (by omega)] at h ⊢
  obtain ⟨m, rfl⟩ : ∃ m, n = Δ.length + 1 + m := ⟨n - Δ.length - 1, by omega⟩
  simp only [show Δ.length + 1 + m - Δ.length = m + 1 by omega, List.getElem?_cons_succ] at h
  simpa [show Δ.length + 1 + m - 1 - Δ.length = m by omega] using h

mutual
theorem HasTypeA.subst : ∀ (a : Atom S) {Δ Γ : Ctx S} {τ τ' v}, HasTypeA E (Δ ++ τ :: Γ) a τ' → HasTypeA E [] v τ →
    HasTypeA E (Δ ++ Γ) (a.subst Δ.length v) τ'
  | .var n, Δ, Γ, τ, τ', v, .var h, hv => by
      simp only [Atom.subst]
      split
      · next hn => exact .var (by rw [List.getElem?_append_left hn] at h ⊢; exact h)
      · next hn =>
        split
        · next hk =>
          subst hk
          rw [List.getElem?_append_right (by omega)] at h
          simp at h; subst h; exact HasTypeA.closed _ hv
        · next hk => exact .var (lookup_subst h hn hk)
  | .const _, _, _, _, _, _, .const, _ => .const
  | .prim _ as, _, _, _, _, _, .prim h, hv => .prim (HasTypeL.subst as h hv)
  | .lam _ e, Δ, Γ, _, _, _, .lam h, hv => .lam (HasType.subst e (Δ := _ :: Δ) h hv)
  | .fix τ₁ τ₂ e, Δ, Γ, _, _, _, .fix h, hv => by
      have := HasType.subst e (Δ := τ₁ :: .arr τ₁ τ₂ :: Δ) h hv
      exact .fix (by simpa [Nat.add_assoc] using this)
  | .pair a₁ a₂, _, _, _, _, _, .pair h₁ h₂, hv => .pair (HasTypeA.subst a₁ h₁ hv) (HasTypeA.subst a₂ h₂ hv)
  | .fst a, _, _, _, _, _, .fst h, hv => .fst (HasTypeA.subst a h hv)
  | .snd a, _, _, _, _, _, .snd h, hv => .snd (HasTypeA.subst a h hv)
  | .inl _ a, _, _, _, _, _, .inl h, hv => .inl (HasTypeA.subst a h hv)
  | .inr _ a, _, _, _, _, _, .inr h, hv => .inr (HasTypeA.subst a h hv)
theorem HasTypeL.subst : ∀ (as : List (Atom S)) {Δ Γ : Ctx S} {τ τs v}, HasTypeL E (Δ ++ τ :: Γ) as τs → HasTypeA E [] v τ →
    HasTypeL E (Δ ++ Γ) (Atom.substL Δ.length v as) τs
  | [], _, _, _, _, _, .nil, _ => .nil
  | a :: as, _, _, _, _, _, .cons h hs, hv => .cons (HasTypeA.subst a h hv) (HasTypeL.subst as hs hv)
theorem HasType.subst : ∀ (e : Tm S) {Δ Γ : Ctx S} {τ τ' v}, HasType E (Δ ++ τ :: Γ) e τ' → HasTypeA E [] v τ →
    HasType E (Δ ++ Γ) (e.subst Δ.length v) τ'
  | .ret a, _, _, _, _, _, .ret h, hv => .ret (HasTypeA.subst a h hv)
  | .letE τ₁ e₁ e₂, Δ, _, _, _, _, .letE h₁ h₂, hv => .letE (HasType.subst e₁ h₁ hv) (HasType.subst e₂ (Δ := τ₁ :: Δ) h₂ hv)
  | .letOp o as _ e, Δ, _, _, _, _, .letOp h₁ h₂, hv =>
      .letOp (HasTypeL.subst as h₁ hv) (HasType.subst e (Δ := E.oRes o :: Δ) h₂ hv)
  | .app a₁ a₂, _, _, _, _, _, .app h₁ h₂, hv => .app (HasTypeA.subst a₁ h₁ hv) (HasTypeA.subst a₂ h₂ hv)
  | .ite a e₁ e₂, _, _, _, _, _, .ite h h₁ h₂, hv => .ite (HasTypeA.subst a h hv) (HasType.subst e₁ h₁ hv) (HasType.subst e₂ h₂ hv)
  | .case a e₁ e₂, Δ, _, _, _, _, .case h h₁ h₂, hv =>
      .case (HasTypeA.subst a h hv) (HasType.subst e₁ (Δ := _ :: Δ) h₁ hv) (HasType.subst e₂ (Δ := _ :: Δ) h₂ hv)
end

/-- The substitution lemma at the top binder: the form the step relation uses. -/
theorem HasType.subst0 {e : Tm S} {Γ : Ctx S} {τ τ' v} (h : HasType E (τ :: Γ) e τ') (hv : HasTypeA E [] v τ) :
    HasType E Γ (e.subst 0 v) τ' := HasType.subst e (Δ := []) h hv

end VIRL1
