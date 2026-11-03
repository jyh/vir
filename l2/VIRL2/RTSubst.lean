/-
  O95 layer L2, Lean arm. Y5: substitution into RUNTIME-typed terms. `RT.substV`: a value that fits the position (a closed
  typed non-capability atom, or anything at an unused capability position) at a `false` mask position; Ω is unchanged
  (constants ⟨p⟩ are untouched by substitution). The capability form (⟨p⟩ at a TRUE position, Ω grows by p) is next.
-/
import VIRL2.Runtime

namespace VIRL2
open VIRL1

theorem RT.substV : ∀ {Γ₁ Γ : Ctx S₂} {Δ₁ Δ : List Bool} {Ω e τ τ' v}, Δ₁.length = Γ₁.length →
    RT (Γ₁ ++ τ :: Γ) (Δ₁ ++ false :: Δ) Ω e τ' → Fits v τ → RT (Γ₁ ++ Γ) (Δ₁ ++ Δ) Ω (e.subst Γ₁.length v) τ'
  | _, _, _, _, _, .ret a, _, _, _, _, .ret hΔ h, hv => .ret (mask_empty_drop hΔ) (substA₂ h hv)
  | Γ₁, _, Δ₁, _, _, .ret (.var n), _, _, _, hl, .retCap hΓ hΔ, hv => by
    have hn := mask_true_ne hΔ.1
    rw [hl] at hn
    show RT _ _ _ (.ret ((Atom.var n).subst Γ₁.length _)) _
    rw [subst_var_ne hn]
    refine .retCap (by rw [← get_drop hn]; exact hΓ) ?_
    have := mask_only_drop hΔ; rwa [hl] at this
  | _, _, _, _, _, .ret (.const (.cap p)), _, _, _, _, .retCapC hΔ, _ => .retCapC (mask_empty_drop hΔ)
  | Γ₁, Γ, Δ₁, Δ, _, .letE τ₁ e₁ e₂, _, _, _, hl, .letE hs hp hc h₁ h₂, hv => by
    obtain ⟨A₁, A₂, B₁, B₂, rfl, rfl, hA, hB, hs'⟩ := split_mid hs
    refine .letE hs' hp hc (RT.substV (hA.trans hl) h₁ hv) ?_
    exact RT.substV (Γ₁ := τ₁ :: Γ₁) (Δ₁ := _ :: B₁) (by simp [hB, hl]) h₂ hv
  | Γ₁, Γ, Δ₁, Δ, _, .letOp .alloc [a] _ e, _, _, _, hl, .alloc ha h, hv =>
    .alloc (substA₂ ha hv) (RT.substV (Γ₁ := tcap :: Γ₁) (Δ₁ := true :: Δ₁) (by simp [hl]) h hv)
  | Γ₁, Γ, Δ₁, Δ, _, .letOp .load [.var n, a] _ e, _, _, _, hl, .load hΓ hΔ ha h, hv => by
    have hn := mask_true_ne hΔ; rw [hl] at hn
    show RT _ _ _ (.letOp .load [(Atom.var n).subst Γ₁.length _, _] _ _) _
    rw [subst_var_ne hn]
    refine .load (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop (hl ▸ hn)]; exact hΔ) (substA₂ ha hv) ?_
    exact RT.substV (Γ₁ := tint :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h hv
  | Γ₁, Γ, Δ₁, Δ, _, .letOp .load [.const (.cap p), a] _ e, _, _, _, hl, .loadC hp ha h, hv =>
    .loadC hp (substA₂ ha hv) (RT.substV (Γ₁ := tint :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h hv)
  | Γ₁, Γ, Δ₁, Δ, _, .letOp .store [.var n, a₁, a₂] _ e, _, _, _, hl, .store hΓ hΔ h₁ h₂ h, hv => by
    have hn := mask_true_ne hΔ; rw [hl] at hn
    have hn' : n ≠ Δ₁.length := hl ▸ hn
    show RT _ _ _ (.letOp .store [(Atom.var n).subst Γ₁.length _, _, _] _ _) _
    rw [subst_var_ne hn]
    refine .store (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ)
      (substA₂ h₁ hv) (substA₂ h₂ hv) ?_
    rw [set_mid hn'] at h
    have := RT.substV (Γ₁ := tcap :: Γ₁) (Δ₁ := true :: _) (by simp [List.length_set]; split_ifs <;> simp [hl]) h hv
    simp only [List.cons_append] at this
    rw [set_drop hn', hl] at this; exact this
  | Γ₁, Γ, Δ₁, Δ, _, .letOp .store [.const (.cap p), a₁, a₂] _ e, _, _, _, hl, .storeC hp h₁ h₂ h, hv =>
    .storeC hp (substA₂ h₁ hv) (substA₂ h₂ hv) (RT.substV (Γ₁ := tcap :: Γ₁) (Δ₁ := true :: Δ₁) (by simp [hl]) h hv)
  | Γ₁, Γ, Δ₁, Δ, _, .letOp .free [.var n] _ e, _, _, _, hl, .free hΓ hΔ h, hv => by
    have hn := mask_true_ne hΔ; rw [hl] at hn
    have hn' : n ≠ Δ₁.length := hl ▸ hn
    show RT _ _ _ (.letOp .free [(Atom.var n).subst Γ₁.length _] _ _) _
    rw [subst_var_ne hn]
    refine .free (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ) ?_
    rw [set_mid hn'] at h
    have := RT.substV (Γ₁ := tunit :: Γ₁) (Δ₁ := false :: _) (by simp [List.length_set]; split_ifs <;> simp [hl]) h hv
    simp only [List.cons_append] at this
    rw [set_drop hn', hl] at this; exact this
  | Γ₁, Γ, Δ₁, Δ, _, .letOp .free [.const (.cap p)] _ e, _, _, _, hl, .freeC hp h, hv =>
    .freeC hp (RT.substV (Γ₁ := tunit :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h hv)
  | _, _, _, _, _, .app a b, _, _, _, _, .app hΔ h₁ h₂, hv => .app (mask_empty_drop hΔ) (substA₂ h₁ hv) (substA₂ h₂ hv)
  | _, _, _, _, _, .ite a e₁ e₂, _, _, _, hl, .ite h h₁ h₂, hv =>
    .ite (substA₂ h hv) (RT.substV hl h₁ hv) (RT.substV hl h₂ hv)
  | Γ₁, Γ, Δ₁, Δ, _, .case a e₁ e₂, _, _, _, hl, .case h h₁ h₂, hv =>
    .case (substA₂ h hv) (RT.substV (Γ₁ := _ :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h₁ hv)
      (RT.substV (Γ₁ := _ :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h₂ hv)

/-! ## Mask facts at a TRUE position -/
theorem mask_empty_true {Δ₁ Δ : List Bool} (h : Mask.empty (Δ₁ ++ true :: Δ)) : False :=
  h Δ₁.length (by simp)

theorem mask_only_true {Δ₁ Δ : List Bool} {n : Nat} (h : Mask.only (Δ₁ ++ true :: Δ) n) : n = Δ₁.length := by
  by_contra hn; exact h.2 Δ₁.length (Ne.symm hn) (by simp)

theorem mask_only_self {Δ₁ Δ : List Bool} (h : Mask.only (Δ₁ ++ true :: Δ) Δ₁.length) : Mask.empty (Δ₁ ++ Δ) := by
  intro m hm
  by_cases hk : m < Δ₁.length
  · exact h.2 m (by omega) (by rw [get_mid, if_pos hk]; exact hm)
  · exact h.2 (m + 1) (by omega) (by rw [get_mid, if_neg (by omega), if_neg (by omega)]; simpa using hm)

theorem split_mid_true {Δ₁ Δ A B : List Bool} (h : Split (Δ₁ ++ true :: Δ) A B) :
    ∃ A₁ A₂ B₁ B₂ a, A = A₁ ++ a :: A₂ ∧ B = B₁ ++ (!a) :: B₂ ∧ A₁.length = Δ₁.length ∧ B₁.length = Δ₁.length ∧
      Split (Δ₁ ++ Δ) (A₁ ++ A₂) (B₁ ++ B₂) := by
  induction Δ₁ generalizing A B with
  | nil =>
    cases h with
    | left h => exact ⟨[], _, [], _, true, rfl, rfl, rfl, rfl, h⟩
    | right h => exact ⟨[], _, [], _, false, rfl, rfl, rfl, rfl, h⟩
  | cons d Δ₁ ih =>
    cases h with
    | left h =>
      obtain ⟨A₁, A₂, B₁, B₂, a, rfl, rfl, h₁, h₂, hs⟩ := ih h
      exact ⟨true :: A₁, A₂, false :: B₁, B₂, a, rfl, rfl, by simp [h₁], by simp [h₂], .left hs⟩
    | right h =>
      obtain ⟨A₁, A₂, B₁, B₂, a, rfl, rfl, h₁, h₂, hs⟩ := ih h
      exact ⟨false :: A₁, A₂, true :: B₁, B₂, a, rfl, rfl, by simp [h₁], by simp [h₂], .right hs⟩
    | none h =>
      obtain ⟨A₁, A₂, B₁, B₂, a, rfl, rfl, h₁, h₂, hs⟩ := ih h
      exact ⟨false :: A₁, A₂, false :: B₁, B₂, a, rfl, rfl, by simp [h₁], by simp [h₂], .none hs⟩

/-! ## RT is invariant under permuting what it owns -/
theorem RT.perm : ∀ {Γ Δ Ω Ω' e τ}, Ω.Perm Ω' → RT Γ Δ Ω e τ → RT Γ Δ Ω' e τ
  | _, _, _, _, _, _, hp, .ret hΔ h => by rw [List.perm_nil.1 hp.symm]; exact .ret hΔ h
  | _, _, _, _, _, _, hp, .retCap hΓ hΔ => by rw [List.perm_nil.1 hp.symm]; exact .retCap hΓ hΔ
  | _, _, _, _, _, _, hp, .retCapC hΔ => by rw [List.perm_singleton.1 hp.symm]; exact .retCapC hΔ
  | _, _, _, _, _, _, hp, .letE hs hp' hc h₁ h₂ => .letE hs (hp.symm.trans hp') hc h₁ h₂
  | _, _, _, _, _, _, hp, .alloc ha h => .alloc ha (RT.perm hp h)
  | _, _, _, _, _, _, hp, .load hΓ hΔ ha h => .load hΓ hΔ ha (RT.perm hp h)
  | _, _, _, _, _, _, hp, .loadC hm ha h => .loadC (hp.subset hm) ha (RT.perm hp h)
  | _, _, _, _, _, _, hp, .store hΓ hΔ h₁ h₂ h => .store hΓ hΔ h₁ h₂ (RT.perm hp h)
  | _, _, _, _, _, _, hp, .storeC hm h₁ h₂ h => .storeC (hp.subset hm) h₁ h₂ (RT.perm (hp.erase _) h)
  | _, _, _, _, _, _, hp, .free hΓ hΔ h => .free hΓ hΔ (RT.perm hp h)
  | _, _, _, _, _, _, hp, .freeC hm h => .freeC (hp.subset hm) (RT.perm (hp.erase _) h)
  | _, _, _, _, _, _, hp, .app hΔ h₁ h₂ => by rw [List.perm_nil.1 hp.symm]; exact .app hΔ h₁ h₂
  | _, _, _, _, _, _, hp, .ite h h₁ h₂ => .ite h (RT.perm hp h₁) (RT.perm hp h₂)
  | _, _, _, _, _, _, hp, .case h h₁ h₂ => .case h (RT.perm hp h₁) (RT.perm hp h₂)

theorem erase_cons_perm {p q : Int} {Ω : List Int} (hq : q ∈ Ω) : ((p :: Ω).erase q).Perm (p :: Ω.erase q) := by
  by_cases h : p = q
  · subst h; rw [List.erase_cons_head]; exact (List.perm_cons_erase hq)
  · rw [List.erase_cons_tail (by simpa using h)]

theorem set_self {Δ₁ Δ : List Bool} {b : Bool} : (Δ₁ ++ b :: Δ).set Δ₁.length false = Δ₁ ++ false :: Δ := by
  rw [List.set_append_right _ _ (by omega)]; simp

theorem fits_cap (p : Int) : Fits (.const (.cap p)) tcap := .inr rfl

theorem subst_var_self {k : Nat} {v : Atom₂} : (Atom.var k : Atom₂).subst k v = v := by simp [Atom.subst]

/-- `RT.substC`: ⟨p⟩ at a TRUE mask position (a capability variable the term owns): the term now owns p. -/
theorem RT.substC : ∀ {Γ₁ Γ : Ctx S₂} {Δ₁ Δ : List Bool} {Ω e τ'} (p : Int), Δ₁.length = Γ₁.length →
    RT (Γ₁ ++ tcap :: Γ) (Δ₁ ++ true :: Δ) Ω e τ' → RT (Γ₁ ++ Γ) (Δ₁ ++ Δ) (p :: Ω) (e.subst Γ₁.length (.const (.cap p))) τ'
  | _, _, _, _, _, _, _, _, _, .ret hΔ _ => (mask_empty_true hΔ).elim
  | Γ₁, _, Δ₁, _, _, .ret (.var n), _, p, hl, .retCap _ hΔ => by
    have hn := mask_only_true hΔ; subst hn
    show RT _ _ _ (.ret ((Atom.var Δ₁.length).subst Γ₁.length _)) _
    rw [hl, subst_var_self]; exact .retCapC (mask_only_self (hl ▸ hΔ))
  | _, _, _, _, _, _, _, _, _, .retCapC hΔ => (mask_empty_true hΔ).elim
  | Γ₁, Γ, Δ₁, Δ, Ω, .letE τ₁ e₁ e₂, _, p, hl, .letE hs hp hc h₁ h₂ => by
    obtain ⟨A₁, A₂, B₁, B₂, a, rfl, rfl, hA, hB, hs'⟩ := split_mid_true hs
    cases a with
    | true =>
      refine .letE hs' (hp.cons p) hc (RT.substC p (hA.trans hl) h₁) ?_
      exact RT.substV (Γ₁ := τ₁ :: Γ₁) (Δ₁ := _ :: B₁) (by simp [hB, hl]) h₂ (fits_cap p)
    | false =>
      refine .letE hs' ((hp.cons p).trans List.perm_middle.symm) hc (RT.substV (hA.trans hl) h₁ (fits_cap p)) ?_
      exact RT.substC (Γ₁ := τ₁ :: Γ₁) (Δ₁ := _ :: B₁) p (by simp [hB, hl]) h₂
  | Γ₁, Γ, Δ₁, Δ, _, .letOp .alloc [a] _ e, _, p, hl, .alloc ha h =>
    .alloc (substA₂ ha (fits_cap p)) (RT.substC (Γ₁ := tcap :: Γ₁) (Δ₁ := true :: Δ₁) p (by simp [hl]) h)
  | Γ₁, Γ, Δ₁, Δ, _, .letOp .load [.var n, a] _ e, _, p, hl, .load hΓ hΔ ha h => by
    by_cases hn : n = Γ₁.length
    · subst hn
      show RT _ _ _ (.letOp .load [(Atom.var Γ₁.length).subst Γ₁.length _, _] _ _) _
      rw [subst_var_self]
      exact .loadC (List.mem_cons_self) (substA₂ ha (fits_cap p))
        (RT.substC (Γ₁ := tint :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h)
    · show RT _ _ _ (.letOp .load [(Atom.var n).subst Γ₁.length _, _] _ _) _
      rw [subst_var_ne hn]
      refine .load (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop (hl ▸ hn)]; exact hΔ)
        (substA₂ ha (fits_cap p)) ?_
      exact RT.substC (Γ₁ := tint :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h
  | Γ₁, Γ, Δ₁, Δ, _, .letOp .load [.const (.cap q), a] _ e, _, p, hl, .loadC hq ha h =>
    .loadC (List.mem_cons_of_mem _ hq) (substA₂ ha (fits_cap p))
      (RT.substC (Γ₁ := tint :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h)
  | Γ₁, Γ, Δ₁, Δ, Ω, .letOp .store [.var n, a₁, a₂] _ e, _, p, hl, .store hΓ hΔ h₁ h₂ h => by
    by_cases hn : n = Γ₁.length
    · subst hn
      show RT _ _ _ (.letOp .store [(Atom.var Γ₁.length).subst Γ₁.length _, _, _] _ _) _
      rw [subst_var_self]
      rw [← hl, set_self] at h
      refine .storeC (List.mem_cons_self) (substA₂ h₁ (fits_cap p)) (substA₂ h₂ (fits_cap p)) ?_
      rw [List.erase_cons_head]
      have := RT.substV (Γ₁ := tcap :: Γ₁) (Δ₁ := true :: Δ₁) (by simp [hl]) h (fits_cap p)
      simpa [hl] using this
    · have hn' : n ≠ Δ₁.length := hl ▸ hn
      show RT _ _ _ (.letOp .store [(Atom.var n).subst Γ₁.length _, _, _] _ _) _
      rw [subst_var_ne hn]
      refine .store (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ)
        (substA₂ h₁ (fits_cap p)) (substA₂ h₂ (fits_cap p)) ?_
      rw [set_mid hn'] at h
      have := RT.substC (Γ₁ := tcap :: Γ₁) (Δ₁ := true :: _) p (by simp [List.length_set]; split_ifs <;> simp [hl]) h
      simp only [List.cons_append] at this
      rw [set_drop hn', hl] at this; exact this
  | Γ₁, Γ, Δ₁, Δ, Ω, .letOp .store [.const (.cap q), a₁, a₂] _ e, _, p, hl, .storeC hq h₁ h₂ h =>
    .storeC (List.mem_cons_of_mem _ hq) (substA₂ h₁ (fits_cap p)) (substA₂ h₂ (fits_cap p))
      (RT.perm (erase_cons_perm hq).symm (RT.substC (Γ₁ := tcap :: Γ₁) (Δ₁ := true :: Δ₁) p (by simp [hl]) h))
  | Γ₁, Γ, Δ₁, Δ, Ω, .letOp .free [.var n] _ e, _, p, hl, .free hΓ hΔ h => by
    by_cases hn : n = Γ₁.length
    · subst hn
      show RT _ _ _ (.letOp .free [(Atom.var Γ₁.length).subst Γ₁.length _] _ _) _
      rw [subst_var_self]
      rw [← hl, set_self] at h
      refine .freeC (List.mem_cons_self) ?_
      rw [List.erase_cons_head]
      have := RT.substV (Γ₁ := tunit :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h (fits_cap p)
      simpa [hl] using this
    · have hn' : n ≠ Δ₁.length := hl ▸ hn
      show RT _ _ _ (.letOp .free [(Atom.var n).subst Γ₁.length _] _ _) _
      rw [subst_var_ne hn]
      refine .free (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ) ?_
      rw [set_mid hn'] at h
      have := RT.substC (Γ₁ := tunit :: Γ₁) (Δ₁ := false :: _) p (by simp [List.length_set]; split_ifs <;> simp [hl]) h
      simp only [List.cons_append] at this
      rw [set_drop hn', hl] at this; exact this
  | Γ₁, Γ, Δ₁, Δ, Ω, .letOp .free [.const (.cap q)] _ e, _, p, hl, .freeC hq h =>
    .freeC (List.mem_cons_of_mem _ hq)
      (RT.perm (erase_cons_perm hq).symm (RT.substC (Γ₁ := tunit :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h))
  | _, _, _, _, _, _, _, _, _, .app hΔ _ _ => (mask_empty_true hΔ).elim
  | _, _, _, _, _, .ite a e₁ e₂, _, p, hl, .ite h h₁ h₂ =>
    .ite (substA₂ h (fits_cap p)) (RT.substC p hl h₁) (RT.substC p hl h₂)
  | Γ₁, Γ, Δ₁, Δ, _, .case a e₁ e₂, _, p, hl, .case h h₁ h₂ =>
    .case (substA₂ h (fits_cap p)) (RT.substC (Γ₁ := _ :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h₁)
      (RT.substC (Γ₁ := _ :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h₂)

end VIRL2
