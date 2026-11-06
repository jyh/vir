/-
  O95 layer L4, Lean arm (amend-21 Q6; l4/DECLARATIONS-LEAN.md addendum 6). Q6's PRESERVATION, part (i): RT₄'s structural lemmas,
  L2's restated for the mutual RTA₄/RTL₄/RT₄ (a λ or fix body is RT₄-typed with Ω = [], so a lemma on atoms recurses into terms).
  First, weakening at the context's END (no index moves), which a closed value needs to be typed in any context.
-/
import VIRL4.RouterV

namespace VIRL4
open VIRL1 VIRL2

theorem get_app_left {α : Type} {Γ Γ' : List α} {n : Nat} {x : α} (h : Γ[n]? = some x) : (Γ ++ Γ')[n]? = some x := by
  have hl : _ < _ := (List.getElem?_eq_some_iff.1 h).1
  rw [List.getElem?_append_left hl]; exact h

mutual
theorem weakA₄ : ∀ {Γ a τ} (Γ' : Ctx₄), RTA₄ Γ a τ → RTA₄ (Γ ++ Γ') a τ
  | _, _, _, _, .var h hc => .var (get_app_left h) hc
  | _, _, _, _, .int => .int
  | _, _, _, _, .bool => .bool
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .lockC => .lockC
  | _, _, _, Γ', .prim h => .prim (weakL₄ Γ' h)
  | _, _, _, Γ', .lam h₁ h₂ hΔ hl h => .lam h₁ h₂ (mask_empty_pad Γ'.length hΔ) (by simp [hl]; omega) (weak₄ Γ' h)
  | _, _, _, Γ', .fix h₁ h₂ hΔ hl h => .fix h₁ h₂ (mask_empty_pad Γ'.length hΔ) (by simp [hl]; omega) (weak₄ Γ' h)
  | _, _, _, Γ', .pair h₁ h₂ => .pair (weakA₄ Γ' h₁) (weakA₄ Γ' h₂)
  | _, _, _, Γ', .fst h => .fst (weakA₄ Γ' h)
  | _, _, _, Γ', .snd h => .snd (weakA₄ Γ' h)
  | _, _, _, Γ', .inl hc h => .inl hc (weakA₄ Γ' h)
  | _, _, _, Γ', .inr hc h => .inr hc (weakA₄ Γ' h)
theorem weakL₄ : ∀ {Γ as τs} (Γ' : Ctx₄), RTL₄ Γ as τs → RTL₄ (Γ ++ Γ') as τs
  | _, _, _, _, .nil => .nil
  | _, _, _, Γ', .cons h hs => .cons (weakA₄ Γ' h) (weakL₄ Γ' hs)
theorem weak₄ : ∀ {Γ Δ Ω e τ} (Γ' : Ctx₄), RT₄ Γ Δ Ω e τ →
    RT₄ (Γ ++ Γ') (Δ ++ List.replicate Γ'.length false) Ω e τ
  | _, _, _, _, _, _, .ret hΔ h => .ret (mask_empty_pad _ hΔ) (weakA₄ _ h)
  | _, _, _, _, _, _, .retCap hΓ hΔ => .retCap (get_app_left hΓ) (mask_only_pad _ hΔ)
  | _, _, _, _, _, _, .retCapC hΔ => .retCapC (mask_empty_pad _ hΔ)
  | _, _, _, _, _, Γ', .letE hs hp hc h₁ h₂ => .letE (split_pad _ hs) hp hc (weak₄ Γ' h₁) (weak₄ Γ' h₂)
  | _, _, _, _, _, Γ', .alloc ha h => .alloc (weakA₄ Γ' ha) (weak₄ Γ' h)
  | _, _, _, _, _, Γ', .load hΓ hΔ ha h => .load (get_app_left hΓ) (get_pad hΔ) (weakA₄ Γ' ha) (weak₄ Γ' h)
  | _, _, _, _, _, Γ', .loadC hp ha h => .loadC hp (weakA₄ Γ' ha) (weak₄ Γ' h)
  | _, _, _, _, _, Γ', .store hΓ hΔ h₁ h₂ h => .store (get_app_left hΓ) (get_pad hΔ) (weakA₄ Γ' h₁) (weakA₄ Γ' h₂)
      (by rw [set_pad hΔ]; exact weak₄ Γ' h)
  | _, _, _, _, _, Γ', .storeC hp h₁ h₂ h => .storeC hp (weakA₄ Γ' h₁) (weakA₄ Γ' h₂) (weak₄ Γ' h)
  | _, _, _, _, _, Γ', .free hΓ hΔ h => .free (get_app_left hΓ) (get_pad hΔ) (by rw [set_pad hΔ]; exact weak₄ Γ' h)
  | _, _, _, _, _, Γ', .freeC hp h => .freeC hp (weak₄ Γ' h)
  | _, _, _, _, _, Γ', .app hΔ h₁ h₂ => .app (mask_empty_pad _ hΔ) (weakA₄ Γ' h₁) (weakA₄ Γ' h₂)
  | _, _, _, _, _, Γ', .ite h h₁ h₂ => .ite (weakA₄ Γ' h) (weak₄ Γ' h₁) (weak₄ Γ' h₂)
  | _, _, _, _, _, Γ', .case h h₁ h₂ => .case (weakA₄ Γ' h) (weak₄ Γ' h₁) (weak₄ Γ' h₂)
  | _, _, _, _, _, Γ', .newlock hΓ hΔ h => .newlock (get_app_left hΓ) (get_pad hΔ) (by rw [set_pad hΔ]; exact weak₄ Γ' h)
  | _, _, _, _, _, Γ', .newlockC hp h => .newlockC hp (weak₄ Γ' h)
  | _, _, _, _, _, Γ', .acquire ha h => .acquire (weakA₄ Γ' ha) (weak₄ Γ' h)
  | _, _, _, _, _, Γ', .release ha hΓ hΔ h => .release (weakA₄ Γ' ha) (get_app_left hΓ) (get_pad hΔ)
      (by rw [set_pad hΔ]; exact weak₄ Γ' h)
  | _, _, _, _, _, Γ', .releaseC ha hp h => .releaseC (weakA₄ Γ' ha) hp (weak₄ Γ' h)
  | _, _, _, _, _, Γ', .par hs₁ hs₂ hp hc₁ hc₂ h₁ h₂ h =>
      .par (split_pad _ hs₁) (split_pad _ hs₂) hp hc₁ hc₂ (weak₄ Γ' h₁) (weak₄ Γ' h₂) (weak₄ Γ' h)
end

/-- A closed RT₄-typed atom is typed in every context. -/
theorem closedA₄ {v : Atom₄} {τ : Ty₄} (Γ : Ctx₄) (h : RTA₄ [] v τ) : RTA₄ Γ v τ := by
  simpa using weakA₄ Γ h

/-- RT₄ is invariant under permuting Ω. -/
theorem RT₄.perm : ∀ {Γ Δ Ω Ω' e τ}, Ω.Perm Ω' → RT₄ Γ Δ Ω e τ → RT₄ Γ Δ Ω' e τ
  | _, _, _, _, _, _, hp, .ret hΔ h => by rw [List.perm_nil.1 hp.symm]; exact .ret hΔ h
  | _, _, _, _, _, _, hp, .retCap hΓ hΔ => by rw [List.perm_nil.1 hp.symm]; exact .retCap hΓ hΔ
  | _, _, _, _, _, _, hp, .retCapC hΔ => by rw [List.perm_singleton.1 hp.symm]; exact .retCapC hΔ
  | _, _, _, _, _, _, hp, .letE hs hq hc h₁ h₂ => .letE hs (hp.symm.trans hq) hc h₁ h₂
  | _, _, _, _, _, _, hp, .alloc ha h => .alloc ha (RT₄.perm hp h)
  | _, _, _, _, _, _, hp, .load hΓ hΔ ha h => .load hΓ hΔ ha (RT₄.perm hp h)
  | _, _, _, _, _, _, hp, .loadC hq ha h => .loadC (hp.mem_iff.1 hq) ha (RT₄.perm hp h)
  | _, _, _, _, _, _, hp, .store hΓ hΔ h₁ h₂ h => .store hΓ hΔ h₁ h₂ (RT₄.perm hp h)
  | _, _, _, _, _, _, hp, .storeC hq h₁ h₂ h => .storeC (hp.mem_iff.1 hq) h₁ h₂ (RT₄.perm (hp.erase _) h)
  | _, _, _, _, _, _, hp, .free hΓ hΔ h => .free hΓ hΔ (RT₄.perm hp h)
  | _, _, _, _, _, _, hp, .freeC hq h => .freeC (hp.mem_iff.1 hq) (RT₄.perm (hp.erase _) h)
  | _, _, _, _, _, _, hp, .app hΔ h₁ h₂ => by rw [List.perm_nil.1 hp.symm]; exact .app hΔ h₁ h₂
  | _, _, _, _, _, _, hp, .ite h h₁ h₂ => .ite h (RT₄.perm hp h₁) (RT₄.perm hp h₂)
  | _, _, _, _, _, _, hp, .case h h₁ h₂ => .case h (RT₄.perm hp h₁) (RT₄.perm hp h₂)
  | _, _, _, _, _, _, hp, .newlock hΓ hΔ h => .newlock hΓ hΔ (RT₄.perm hp h)
  | _, _, _, _, _, _, hp, .newlockC hq h => .newlockC (hp.mem_iff.1 hq) (RT₄.perm (hp.erase _) h)
  | _, _, _, _, _, _, hp, .acquire ha h => .acquire ha (RT₄.perm hp h)
  | _, _, _, _, _, _, hp, .release ha hΓ hΔ h => .release ha hΓ hΔ (RT₄.perm hp h)
  | _, _, _, _, _, _, hp, .releaseC ha hq h => .releaseC ha (hp.mem_iff.1 hq) (RT₄.perm (hp.erase _) h)
  | _, _, _, _, _, _, hp, .par hs₁ hs₂ hq hc₁ hc₂ h₁ h₂ h => .par hs₁ hs₂ (hp.symm.trans hq) hc₁ hc₂ h₁ h₂ h

/-! ## Substituting a value at a FALSE mask position (L2's `RT.substV`): Ω is unchanged. -/

theorem subst_var_ne₄ {n k : Nat} {v : Atom₄} (h : n ≠ k) : (Atom₄.var n).subst k v = .var (dropIdx k n) := by
  simp only [Atom₄.subst, dropIdx]; split_ifs <;> first | rfl | omega

/-- What may be substituted at a position of type τ: a closed typed atom, or anything at a capability position. -/
def Fits₄ (v : Atom₄) (τ : Ty₄) : Prop := RTA₄ [] v τ ∨ hasCap₄ τ = true

set_option maxHeartbeats 2000000 in
mutual
theorem substA₄ : ∀ {Γ₁ Γ : Ctx₄} {a τ τ' v}, RTA₄ (Γ₁ ++ τ :: Γ) a τ' → Fits₄ v τ →
    RTA₄ (Γ₁ ++ Γ) (a.subst Γ₁.length v) τ'
  | Γ₁, Γ, .var n, τ, τ', v, .var h hc, hv => by
    by_cases hk : n = Γ₁.length
    · subst hk
      rw [List.getElem?_append_right (by omega)] at h; simp at h; subst h
      simp only [Atom₄.subst, Nat.lt_irrefl, if_false, if_true]
      rcases hv with hv | hv
      · exact closedA₄ _ hv
      · rw [hc] at hv; cases hv
    · rw [subst_var_ne₄ hk]; exact .var (by rw [← get_drop hk]; exact h) hc
  | _, _, _, _, _, _, .int, _ => .int
  | _, _, _, _, _, _, .bool, _ => .bool
  | _, _, _, _, _, _, .unit, _ => .unit
  | _, _, _, _, _, _, .lockC, _ => .lockC
  | _, _, .prim p as, _, _, _, .prim h, hv => .prim (substL₄ h hv)
  | Γ₁, Γ, .lam τ₁ e, _, _, _, .lam h₁ h₂ hΔ hl h, hv => by
    have hs := empty_split hΔ (Γ₁.length + 1) Γ.length (by simp at hl; omega)
    rw [hs] at h
    have := substV₄ (Γ₁ := τ₁ :: Γ₁) (Δ₁ := List.replicate (Γ₁.length + 1) false) (by simp) h hv
    exact .lam h₁ h₂ (mask_empty_reps _ _) (by simp; omega) this
  | Γ₁, Γ, .fix τ₁ τ₂ e, _, _, _, .fix h₁ h₂ hΔ hl h, hv => by
    have hs := empty_split hΔ (Γ₁.length + 2) Γ.length (by simp at hl; omega)
    rw [hs] at h
    have := substV₄ (Γ₁ := τ₁ :: .arr τ₁ τ₂ :: Γ₁) (Δ₁ := List.replicate (Γ₁.length + 2) false) (by simp) h hv
    simp only [List.length_cons, Nat.add_assoc] at this
    exact .fix h₁ h₂ (mask_empty_reps _ _) (by simp; omega) this
  | _, _, .pair a b, _, _, _, .pair h₁ h₂, hv => .pair (substA₄ h₁ hv) (substA₄ h₂ hv)
  | _, _, .fst a, _, _, _, .fst h, hv => .fst (substA₄ h hv)
  | _, _, .snd a, _, _, _, .snd h, hv => .snd (substA₄ h hv)
  | _, _, .inl _ a, _, _, _, .inl hc h, hv => .inl hc (substA₄ h hv)
  | _, _, .inr _ a, _, _, _, .inr hc h, hv => .inr hc (substA₄ h hv)
theorem substL₄ : ∀ {Γ₁ Γ : Ctx₄} {as τ τs v}, RTL₄ (Γ₁ ++ τ :: Γ) as τs → Fits₄ v τ →
    RTL₄ (Γ₁ ++ Γ) (Atom₄.substL Γ₁.length v as) τs
  | _, _, [], _, _, _, .nil, _ => .nil
  | _, _, _ :: _, _, _, _, .cons h hs, hv => .cons (substA₄ h hv) (substL₄ hs hv)
theorem substV₄ : ∀ {Γ₁ Γ : Ctx₄} {Δ₁ Δ : List Bool} {Ω e τ τ' v}, Δ₁.length = Γ₁.length →
    RT₄ (Γ₁ ++ τ :: Γ) (Δ₁ ++ false :: Δ) Ω e τ' → Fits₄ v τ → RT₄ (Γ₁ ++ Γ) (Δ₁ ++ Δ) Ω (e.subst Γ₁.length v) τ'
  | _, _, _, _, _, .ret a, _, _, _, _, .ret hΔ h, hv => .ret (mask_empty_drop hΔ) (substA₄ h hv)
  | Γ₁, _, Δ₁, _, _, .ret (.var n), _, _, _, hl, .retCap hΓ hΔ, hv => by
    have hn := mask_true_ne hΔ.1
    rw [hl] at hn
    show RT₄ _ _ _ (.ret ((Atom₄.var n).subst Γ₁.length _)) _
    rw [subst_var_ne₄ hn]
    refine .retCap (by rw [← get_drop hn]; exact hΓ) ?_
    have := mask_only_drop hΔ; rwa [hl] at this
  | _, _, _, _, _, .ret (.const (.c2 (.cap p))), _, _, _, _, .retCapC hΔ, _ => .retCapC (mask_empty_drop hΔ)
  | Γ₁, Γ, Δ₁, Δ, _, .letE τ₁ e₁ e₂, _, _, _, hl, .letE hs hp hc h₁ h₂, hv => by
    obtain ⟨A₁, A₂, B₁, B₂, rfl, rfl, hA, hB, hs'⟩ := split_mid hs
    refine .letE hs' hp hc (substV₄ (hA.trans hl) h₁ hv) ?_
    exact substV₄ (Γ₁ := τ₁ :: Γ₁) (Δ₁ := _ :: B₁) (by simp [hB, hl]) h₂ hv
  | Γ₁, Γ, Δ₁, Δ, _, .letOp (.o2 .alloc) [a] _ e, _, _, _, hl, .alloc ha h, hv =>
    .alloc (substA₄ ha hv) (substV₄ (Γ₁ := t4cap :: Γ₁) (Δ₁ := true :: Δ₁) (by simp [hl]) h hv)
  | Γ₁, Γ, Δ₁, Δ, _, .letOp (.o2 .load) [.var n, a] _ e, _, _, _, hl, .load hΓ hΔ ha h, hv => by
    have hn := mask_true_ne hΔ; rw [hl] at hn
    show RT₄ _ _ _ (.letOp (.o2 .load) [(Atom₄.var n).subst Γ₁.length _, _] _ _) _
    rw [subst_var_ne₄ hn]
    refine .load (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop (hl ▸ hn)]; exact hΔ) (substA₄ ha hv) ?_
    exact substV₄ (Γ₁ := t4int :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h hv
  | Γ₁, Γ, Δ₁, Δ, _, .letOp (.o2 .load) [.const (.c2 (.cap p)), a] _ e, _, _, _, hl, .loadC hp ha h, hv =>
    .loadC hp (substA₄ ha hv) (substV₄ (Γ₁ := t4int :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h hv)
  | Γ₁, Γ, Δ₁, Δ, _, .letOp (.o2 .store) [.var n, a₁, a₂] _ e, _, _, _, hl, .store hΓ hΔ h₁ h₂ h, hv => by
    have hn := mask_true_ne hΔ; rw [hl] at hn
    have hn' : n ≠ Δ₁.length := hl ▸ hn
    show RT₄ _ _ _ (.letOp (.o2 .store) [(Atom₄.var n).subst Γ₁.length _, _, _] _ _) _
    rw [subst_var_ne₄ hn]
    refine .store (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ)
      (substA₄ h₁ hv) (substA₄ h₂ hv) ?_
    rw [set_mid hn'] at h
    have := substV₄ (Γ₁ := t4cap :: Γ₁) (Δ₁ := true :: _) (by simp [List.length_set]; split_ifs <;> simp [hl]) h hv
    simp only [List.cons_append] at this
    rw [set_drop hn', hl] at this; exact this
  | Γ₁, Γ, Δ₁, Δ, _, .letOp (.o2 .store) [.const (.c2 (.cap p)), a₁, a₂] _ e, _, _, _, hl, .storeC hp h₁ h₂ h, hv =>
    .storeC hp (substA₄ h₁ hv) (substA₄ h₂ hv) (substV₄ (Γ₁ := t4cap :: Γ₁) (Δ₁ := true :: Δ₁) (by simp [hl]) h hv)
  | Γ₁, Γ, Δ₁, Δ, _, .letOp (.o2 .free) [.var n] _ e, _, _, _, hl, .free hΓ hΔ h, hv => by
    have hn := mask_true_ne hΔ; rw [hl] at hn
    have hn' : n ≠ Δ₁.length := hl ▸ hn
    show RT₄ _ _ _ (.letOp (.o2 .free) [(Atom₄.var n).subst Γ₁.length _] _ _) _
    rw [subst_var_ne₄ hn]
    refine .free (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ) ?_
    rw [set_mid hn'] at h
    have := substV₄ (Γ₁ := t4unit :: Γ₁) (Δ₁ := false :: _) (by simp [List.length_set]; split_ifs <;> simp [hl]) h hv
    simp only [List.cons_append] at this
    rw [set_drop hn', hl] at this; exact this
  | Γ₁, Γ, Δ₁, Δ, _, .letOp (.o2 .free) [.const (.c2 (.cap p))] _ e, _, _, _, hl, .freeC hp h, hv =>
    .freeC hp (substV₄ (Γ₁ := t4unit :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h hv)
  | _, _, _, _, _, .app a b, _, _, _, _, .app hΔ h₁ h₂, hv => .app (mask_empty_drop hΔ) (substA₄ h₁ hv) (substA₄ h₂ hv)
  | _, _, _, _, _, .ite a e₁ e₂, _, _, _, hl, .ite h h₁ h₂, hv =>
    .ite (substA₄ h hv) (substV₄ hl h₁ hv) (substV₄ hl h₂ hv)
  | Γ₁, Γ, Δ₁, Δ, _, .case a e₁ e₂, _, _, _, hl, .case h h₁ h₂, hv =>
    .case (substA₄ h hv) (substV₄ (Γ₁ := _ :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h₁ hv)
      (substV₄ (Γ₁ := _ :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h₂ hv)
  | Γ₁, Γ, Δ₁, Δ, _, .letOp .newlock [.var n] _ e, _, _, _, hl, .newlock hΓ hΔ h, hv => by
    have hn := mask_true_ne hΔ; rw [hl] at hn
    have hn' : n ≠ Δ₁.length := hl ▸ hn
    show RT₄ _ _ _ (.letOp .newlock [(Atom₄.var n).subst Γ₁.length _] _ _) _
    rw [subst_var_ne₄ hn]
    refine .newlock (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ) ?_
    rw [set_mid hn'] at h
    have := substV₄ (Γ₁ := t4lock :: Γ₁) (Δ₁ := false :: _) (by simp [List.length_set]; split_ifs <;> simp [hl]) h hv
    simp only [List.cons_append] at this
    rw [set_drop hn', hl] at this; exact this
  | Γ₁, Γ, Δ₁, Δ, _, .letOp .newlock [.const (.c2 (.cap p))] _ e, _, _, _, hl, .newlockC hp h, hv =>
    .newlockC hp (substV₄ (Γ₁ := t4lock :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h hv)
  | Γ₁, Γ, Δ₁, Δ, _, .letOp .acquire [a] _ e, _, _, _, hl, .acquire ha h, hv =>
    .acquire (substA₄ ha hv) (substV₄ (Γ₁ := t4cap :: Γ₁) (Δ₁ := true :: Δ₁) (by simp [hl]) h hv)
  | Γ₁, Γ, Δ₁, Δ, _, .letOp .release [a, .var n] _ e, _, _, _, hl, .release ha hΓ hΔ h, hv => by
    have hn := mask_true_ne hΔ; rw [hl] at hn
    have hn' : n ≠ Δ₁.length := hl ▸ hn
    show RT₄ _ _ _ (.letOp .release [a.subst Γ₁.length _, (Atom₄.var n).subst Γ₁.length _] _ _) _
    rw [subst_var_ne₄ hn]
    refine .release (substA₄ ha hv) (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ) ?_
    rw [set_mid hn'] at h
    have := substV₄ (Γ₁ := t4unit :: Γ₁) (Δ₁ := false :: _) (by simp [List.length_set]; split_ifs <;> simp [hl]) h hv
    simp only [List.cons_append] at this
    rw [set_drop hn', hl] at this; exact this
  | Γ₁, Γ, Δ₁, Δ, _, .letOp .release [a, .const (.c2 (.cap p))] _ e, _, _, _, hl, .releaseC ha hp h, hv =>
    .releaseC (substA₄ ha hv) hp (substV₄ (Γ₁ := t4unit :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h hv)
  | Γ₁, Γ, Δ₁, Δ, _, .par τ₁ τ₂ e₁ e₂ e, _, _, _, hl, .par hs₁ hs₂ hp hc₁ hc₂ h₁ h₂ h, hv => by
    obtain ⟨A₁, A₂, B₁, B₂, rfl, rfl, hA, hB, hs₁'⟩ := split_mid hs₁
    obtain ⟨C₁, C₂, D₁, D₂, rfl, rfl, hC, hD, hs₂'⟩ := split_mid hs₂
    refine .par hs₁' hs₂' hp hc₁ hc₂ (substV₄ (hA.trans hl) h₁ hv) (substV₄ (hC.trans (hB.trans hl)) h₂ hv) ?_
    exact substV₄ (Γ₁ := τ₂ :: τ₁ :: Γ₁) (Δ₁ := _ :: _ :: D₁) (by simp [hD, hB, hl]) h hv
end

end VIRL4
