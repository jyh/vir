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

/-! ## ⟨p⟩ at a TRUE mask position (L2's `RT.substC`): the term now owns p. -/

theorem fits_cap₄ (p : Int) : Fits₄ (capv p) t4cap := .inr rfl

theorem subst_var_self₄ {k : Nat} {v : Atom₄} : (Atom₄.var k).subst k v = v := by simp [Atom₄.subst]

theorem perm_mid2 {p : Int} {Ω Ω₁ Ω₂ Ω₀ : List Int} (hp : Ω.Perm (Ω₁ ++ Ω₂ ++ Ω₀)) :
    (p :: Ω).Perm (Ω₁ ++ (p :: Ω₂) ++ Ω₀) :=
  (hp.cons p).trans (by simp only [List.append_assoc, List.cons_append]; exact List.perm_middle.symm)

theorem perm_mid3 {p : Int} {Ω Ω₁ Ω₂ Ω₀ : List Int} (hp : Ω.Perm (Ω₁ ++ Ω₂ ++ Ω₀)) :
    (p :: Ω).Perm (Ω₁ ++ Ω₂ ++ p :: Ω₀) :=
  (hp.cons p).trans List.perm_middle.symm

set_option maxHeartbeats 2000000 in
theorem substC₄ : ∀ {Γ₁ Γ : Ctx₄} {Δ₁ Δ : List Bool} {Ω e τ'} (p : Int), Δ₁.length = Γ₁.length →
    RT₄ (Γ₁ ++ t4cap :: Γ) (Δ₁ ++ true :: Δ) Ω e τ' → RT₄ (Γ₁ ++ Γ) (Δ₁ ++ Δ) (p :: Ω) (e.subst Γ₁.length (capv p)) τ'
  | _, _, _, _, _, _, _, _, _, .ret hΔ _ => (mask_empty_true hΔ).elim
  | Γ₁, _, Δ₁, _, _, .ret (.var n), _, p, hl, .retCap _ hΔ => by
    have hn := mask_only_true hΔ; subst hn
    show RT₄ _ _ _ (.ret ((Atom₄.var Δ₁.length).subst Γ₁.length _)) _
    rw [hl, subst_var_self₄]; exact .retCapC (mask_only_self (hl ▸ hΔ))
  | _, _, _, _, _, _, _, _, _, .retCapC hΔ => (mask_empty_true hΔ).elim
  | Γ₁, Γ, Δ₁, Δ, Ω, .letE τ₁ e₁ e₂, _, p, hl, .letE hs hp hc h₁ h₂ => by
    obtain ⟨A₁, A₂, B₁, B₂, a, rfl, rfl, hA, hB, hs'⟩ := split_mid_true hs
    cases a with
    | true =>
      refine .letE hs' (hp.cons p) hc (substC₄ p (hA.trans hl) h₁) ?_
      exact substV₄ (Γ₁ := τ₁ :: Γ₁) (Δ₁ := _ :: B₁) (by simp [hB, hl]) h₂ (fits_cap₄ p)
    | false =>
      refine .letE hs' ((hp.cons p).trans List.perm_middle.symm) hc (substV₄ (hA.trans hl) h₁ (fits_cap₄ p)) ?_
      exact substC₄ (Γ₁ := τ₁ :: Γ₁) (Δ₁ := _ :: B₁) p (by simp [hB, hl]) h₂
  | Γ₁, Γ, Δ₁, Δ, _, .letOp (.o2 .alloc) [a] _ e, _, p, hl, .alloc ha h =>
    .alloc (substA₄ ha (fits_cap₄ p)) (substC₄ (Γ₁ := t4cap :: Γ₁) (Δ₁ := true :: Δ₁) p (by simp [hl]) h)
  | Γ₁, Γ, Δ₁, Δ, _, .letOp (.o2 .load) [.var n, a] _ e, _, p, hl, .load hΓ hΔ ha h => by
    by_cases hn : n = Γ₁.length
    · subst hn
      show RT₄ _ _ _ (.letOp (.o2 .load) [(Atom₄.var Γ₁.length).subst Γ₁.length _, _] _ _) _
      rw [subst_var_self₄]
      exact .loadC (List.mem_cons_self) (substA₄ ha (fits_cap₄ p))
        (substC₄ (Γ₁ := t4int :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h)
    · show RT₄ _ _ _ (.letOp (.o2 .load) [(Atom₄.var n).subst Γ₁.length _, _] _ _) _
      rw [subst_var_ne₄ hn]
      refine .load (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop (hl ▸ hn)]; exact hΔ)
        (substA₄ ha (fits_cap₄ p)) ?_
      exact substC₄ (Γ₁ := t4int :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h
  | Γ₁, Γ, Δ₁, Δ, _, .letOp (.o2 .load) [.const (.c2 (.cap q)), a] _ e, _, p, hl, .loadC hq ha h =>
    .loadC (List.mem_cons_of_mem _ hq) (substA₄ ha (fits_cap₄ p))
      (substC₄ (Γ₁ := t4int :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h)
  | Γ₁, Γ, Δ₁, Δ, Ω, .letOp (.o2 .store) [.var n, a₁, a₂] _ e, _, p, hl, .store hΓ hΔ h₁ h₂ h => by
    by_cases hn : n = Γ₁.length
    · subst hn
      show RT₄ _ _ _ (.letOp (.o2 .store) [(Atom₄.var Γ₁.length).subst Γ₁.length _, _, _] _ _) _
      rw [subst_var_self₄]
      rw [← hl, set_self] at h
      refine .storeC (List.mem_cons_self) (substA₄ h₁ (fits_cap₄ p)) (substA₄ h₂ (fits_cap₄ p)) ?_
      rw [List.erase_cons_head]
      have := substV₄ (Γ₁ := t4cap :: Γ₁) (Δ₁ := true :: Δ₁) (by simp [hl]) h (fits_cap₄ p)
      simpa [hl] using this
    · have hn' : n ≠ Δ₁.length := hl ▸ hn
      show RT₄ _ _ _ (.letOp (.o2 .store) [(Atom₄.var n).subst Γ₁.length _, _, _] _ _) _
      rw [subst_var_ne₄ hn]
      refine .store (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ)
        (substA₄ h₁ (fits_cap₄ p)) (substA₄ h₂ (fits_cap₄ p)) ?_
      rw [set_mid hn'] at h
      have := substC₄ (Γ₁ := t4cap :: Γ₁) (Δ₁ := true :: _) p (by simp [List.length_set]; split_ifs <;> simp [hl]) h
      simp only [List.cons_append] at this
      rw [set_drop hn', hl] at this; exact this
  | Γ₁, Γ, Δ₁, Δ, Ω, .letOp (.o2 .store) [.const (.c2 (.cap q)), a₁, a₂] _ e, _, p, hl, .storeC hq h₁ h₂ h =>
    .storeC (List.mem_cons_of_mem _ hq) (substA₄ h₁ (fits_cap₄ p)) (substA₄ h₂ (fits_cap₄ p))
      (RT₄.perm (erase_cons_perm hq).symm (substC₄ (Γ₁ := t4cap :: Γ₁) (Δ₁ := true :: Δ₁) p (by simp [hl]) h))
  | Γ₁, Γ, Δ₁, Δ, Ω, .letOp (.o2 .free) [.var n] _ e, _, p, hl, .free hΓ hΔ h => by
    by_cases hn : n = Γ₁.length
    · subst hn
      show RT₄ _ _ _ (.letOp (.o2 .free) [(Atom₄.var Γ₁.length).subst Γ₁.length _] _ _) _
      rw [subst_var_self₄]
      rw [← hl, set_self] at h
      refine .freeC (List.mem_cons_self) ?_
      rw [List.erase_cons_head]
      have := substV₄ (Γ₁ := t4unit :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h (fits_cap₄ p)
      simpa [hl] using this
    · have hn' : n ≠ Δ₁.length := hl ▸ hn
      show RT₄ _ _ _ (.letOp (.o2 .free) [(Atom₄.var n).subst Γ₁.length _] _ _) _
      rw [subst_var_ne₄ hn]
      refine .free (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ) ?_
      rw [set_mid hn'] at h
      have := substC₄ (Γ₁ := t4unit :: Γ₁) (Δ₁ := false :: _) p (by simp [List.length_set]; split_ifs <;> simp [hl]) h
      simp only [List.cons_append] at this
      rw [set_drop hn', hl] at this; exact this
  | Γ₁, Γ, Δ₁, Δ, Ω, .letOp (.o2 .free) [.const (.c2 (.cap q))] _ e, _, p, hl, .freeC hq h =>
    .freeC (List.mem_cons_of_mem _ hq)
      (RT₄.perm (erase_cons_perm hq).symm (substC₄ (Γ₁ := t4unit :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h))
  | _, _, _, _, _, _, _, _, _, .app hΔ _ _ => (mask_empty_true hΔ).elim
  | _, _, _, _, _, .ite a e₁ e₂, _, p, hl, .ite h h₁ h₂ =>
    .ite (substA₄ h (fits_cap₄ p)) (substC₄ p hl h₁) (substC₄ p hl h₂)
  | Γ₁, Γ, Δ₁, Δ, _, .case a e₁ e₂, _, p, hl, .case h h₁ h₂ =>
    .case (substA₄ h (fits_cap₄ p)) (substC₄ (Γ₁ := _ :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h₁)
      (substC₄ (Γ₁ := _ :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h₂)
  | Γ₁, Γ, Δ₁, Δ, Ω, .letOp .newlock [.var n] _ e, _, p, hl, .newlock hΓ hΔ h => by
    by_cases hn : n = Γ₁.length
    · subst hn
      show RT₄ _ _ _ (.letOp .newlock [(Atom₄.var Γ₁.length).subst Γ₁.length _] _ _) _
      rw [subst_var_self₄]
      rw [← hl, set_self] at h
      refine .newlockC (List.mem_cons_self) ?_
      rw [List.erase_cons_head]
      have := substV₄ (Γ₁ := t4lock :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h (fits_cap₄ p)
      simpa [hl] using this
    · have hn' : n ≠ Δ₁.length := hl ▸ hn
      show RT₄ _ _ _ (.letOp .newlock [(Atom₄.var n).subst Γ₁.length _] _ _) _
      rw [subst_var_ne₄ hn]
      refine .newlock (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ) ?_
      rw [set_mid hn'] at h
      have := substC₄ (Γ₁ := t4lock :: Γ₁) (Δ₁ := false :: _) p (by simp [List.length_set]; split_ifs <;> simp [hl]) h
      simp only [List.cons_append] at this
      rw [set_drop hn', hl] at this; exact this
  | Γ₁, Γ, Δ₁, Δ, Ω, .letOp .newlock [.const (.c2 (.cap q))] _ e, _, p, hl, .newlockC hq h =>
    .newlockC (List.mem_cons_of_mem _ hq)
      (RT₄.perm (erase_cons_perm hq).symm (substC₄ (Γ₁ := t4lock :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h))
  | Γ₁, Γ, Δ₁, Δ, _, .letOp .acquire [a] _ e, _, p, hl, .acquire ha h =>
    .acquire (substA₄ ha (fits_cap₄ p)) (substC₄ (Γ₁ := t4cap :: Γ₁) (Δ₁ := true :: Δ₁) p (by simp [hl]) h)
  | Γ₁, Γ, Δ₁, Δ, Ω, .letOp .release [a, .var n] _ e, _, p, hl, .release ha hΓ hΔ h => by
    by_cases hn : n = Γ₁.length
    · subst hn
      show RT₄ _ _ _ (.letOp .release [a.subst Γ₁.length _, (Atom₄.var Γ₁.length).subst Γ₁.length _] _ _) _
      rw [subst_var_self₄]
      rw [← hl, set_self] at h
      refine .releaseC (substA₄ ha (fits_cap₄ p)) (List.mem_cons_self) ?_
      rw [List.erase_cons_head]
      have := substV₄ (Γ₁ := t4unit :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h (fits_cap₄ p)
      simpa [hl] using this
    · have hn' : n ≠ Δ₁.length := hl ▸ hn
      show RT₄ _ _ _ (.letOp .release [a.subst Γ₁.length _, (Atom₄.var n).subst Γ₁.length _] _ _) _
      rw [subst_var_ne₄ hn]
      refine .release (substA₄ ha (fits_cap₄ p)) (by rw [← get_drop hn]; exact hΓ)
        (by rw [← hl, ← get_drop hn']; exact hΔ) ?_
      rw [set_mid hn'] at h
      have := substC₄ (Γ₁ := t4unit :: Γ₁) (Δ₁ := false :: _) p (by simp [List.length_set]; split_ifs <;> simp [hl]) h
      simp only [List.cons_append] at this
      rw [set_drop hn', hl] at this; exact this
  | Γ₁, Γ, Δ₁, Δ, Ω, .letOp .release [a, .const (.c2 (.cap q))] _ e, _, p, hl, .releaseC ha hq h =>
    .releaseC (substA₄ ha (fits_cap₄ p)) (List.mem_cons_of_mem _ hq)
      (RT₄.perm (erase_cons_perm hq).symm (substC₄ (Γ₁ := t4unit :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h))
  | Γ₁, Γ, Δ₁, Δ, Ω, .par τ₁ τ₂ e₁ e₂ e, _, p, hl, .par hs₁ hs₂ hp hc₁ hc₂ h₁ h₂ h => by
    obtain ⟨A₁, A₂, B₁, B₂, a, rfl, rfl, hA, hB, hs₁'⟩ := split_mid_true hs₁
    cases a with
    | true =>
      obtain ⟨C₁, C₂, D₁, D₂, rfl, rfl, hC, hD, hs₂'⟩ := split_mid hs₂
      refine .par hs₁' hs₂' (hp.cons p) hc₁ hc₂ (substC₄ p (hA.trans hl) h₁)
        (substV₄ (hC.trans (hB.trans hl)) h₂ (fits_cap₄ p)) ?_
      exact substV₄ (Γ₁ := τ₂ :: τ₁ :: Γ₁) (Δ₁ := _ :: _ :: D₁) (by simp [hD, hB, hl]) h (fits_cap₄ p)
    | false =>
      obtain ⟨C₁, C₂, D₁, D₂, b, rfl, rfl, hC, hD, hs₂'⟩ := split_mid_true hs₂
      cases b with
      | true =>
        refine .par hs₁' hs₂' (perm_mid2 hp) hc₁ hc₂ (substV₄ (hA.trans hl) h₁ (fits_cap₄ p))
          (substC₄ p (hC.trans (hB.trans hl)) h₂) ?_
        exact substV₄ (Γ₁ := τ₂ :: τ₁ :: Γ₁) (Δ₁ := _ :: _ :: D₁) (by simp [hD, hB, hl]) h (fits_cap₄ p)
      | false =>
        refine .par hs₁' hs₂' (perm_mid3 hp) hc₁ hc₂ (substV₄ (hA.trans hl) h₁ (fits_cap₄ p))
          (substV₄ (hC.trans (hB.trans hl)) h₂ (fits_cap₄ p)) ?_
        exact substC₄ (Γ₁ := τ₂ :: τ₁ :: Γ₁) (Δ₁ := _ :: _ :: D₁) p (by simp [hD, hB, hl]) h

/-! ## Part (ii), the atoms: values, evaluation soundness, canonical forms. -/

def IsVal₄ : Atom₄ → Prop
  | .const _ | .lam _ _ | .fix _ _ _ => True
  | .pair a₁ a₂ => IsVal₄ a₁ ∧ IsVal₄ a₂
  | .inl _ a | .inr _ a => IsVal₄ a
  | _ => False

/-- An RTA₄-typed atom carries no capability (⟨p⟩ is typed only by RT₄'s operand forms). -/
theorem atom_noCap₄ : ∀ {Γ a τ}, RTA₄ Γ a τ → hasCap₄ τ = false
  | _, _, _, .var _ h => h
  | _, _, _, .int => rfl
  | _, _, _, .bool => rfl
  | _, _, _, .unit => rfl
  | _, _, _, .lockC => rfl
  | _, _, _, .prim (p := p) _ => by cases p <;> rfl
  | _, _, _, .lam h₁ h₂ _ _ _ => by simp [hasCap₄, h₁, h₂]
  | _, _, _, .fix h₁ h₂ _ _ _ => by simp [hasCap₄, h₁, h₂]
  | _, _, _, .pair h₁ h₂ => by simp [hasCap₄, atom_noCap₄ h₁, atom_noCap₄ h₂]
  | _, _, _, .fst h => by have := atom_noCap₄ h; simp [hasCap₄] at this; exact this.1
  | _, _, _, .snd h => by have := atom_noCap₄ h; simp [hasCap₄] at this; exact this.2
  | _, _, _, .inl h₂ h => by simp [hasCap₄, atom_noCap₄ h, h₂]
  | _, _, _, .inr h₁ h => by simp [hasCap₄, atom_noCap₄ h, h₁]

theorem prim_sound {p : L1.Prim} {cs : List L1.Const} {c : L1.Const} (h : L1.Prim.interp p cs = some c) :
    L1.Const.ty c = L1.Prim.res p := by
  cases p <;> (rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨_, _⟩⟩⟩) <;> (try cases c₁) <;> (try cases c₂) <;>
    simp_all [L1.Prim.interp, L1.Prim.res] <;> subst_vars <;> rfl

theorem const_ofL1_typed {Γ : Ctx₄} {c : L1.Const} {b : L1.BTy} (h : L1.Const.ty c = b) :
    RTA₄ Γ (.const (.c2 (Const.ofL1 c))) (.base (BTy₄.ofB2 (BTy.ofL1 b))) := by
  cases c <;> subst h <;> first | exact .int | exact .bool

mutual
theorem eval_sound₄ : ∀ (a : Atom₄) {τ v}, RTA₄ [] a τ → Atom₄.eval a = some v → IsVal₄ v ∧ RTA₄ [] v τ
  | .var _, _, _, .var h _, _ => by simp at h
  | .const _, _, _, .int, h => by simp [Atom₄.eval] at h; subst h; exact ⟨trivial, .int⟩
  | .const _, _, _, .bool, h => by simp [Atom₄.eval] at h; subst h; exact ⟨trivial, .bool⟩
  | .const _, _, _, .unit, h => by simp [Atom₄.eval] at h; subst h; exact ⟨trivial, .unit⟩
  | .const _, _, _, .lockC, h => by simp [Atom₄.eval] at h; subst h; exact ⟨trivial, .lockC⟩
  | .prim p as, _, _, .prim _, h => by
    simp only [Atom₄.eval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨vs, -, cs, -, c, hc, rfl⟩ := h
    exact ⟨trivial, const_ofL1_typed (prim_sound hc)⟩
  | .lam τ e, _, _, ht, h => by simp [Atom₄.eval] at h; subst h; exact ⟨trivial, ht⟩
  | .fix τ₁ τ₂ e, _, _, ht, h => by simp [Atom₄.eval] at h; subst h; exact ⟨trivial, ht⟩
  | .pair a₁ a₂, _, _, .pair h₁ h₂, h => by
    simp only [Atom₄.eval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := h
    obtain ⟨i₁, t₁⟩ := eval_sound₄ a₁ h₁ hv₁
    obtain ⟨i₂, t₂⟩ := eval_sound₄ a₂ h₂ hv₂
    exact ⟨⟨i₁, i₂⟩, .pair t₁ t₂⟩
  | .fst a, _, _, .fst ht, h => by
    simp only [Atom₄.eval, Option.bind_eq_some_iff] at h
    obtain ⟨w, hw, hv⟩ := h
    obtain ⟨iw, tw⟩ := eval_sound₄ a ht hw
    cases w <;> simp at hv
    subst hv
    cases tw with
    | pair t₁ _ => exact ⟨iw.1, t₁⟩
  | .snd a, _, _, .snd ht, h => by
    simp only [Atom₄.eval, Option.bind_eq_some_iff] at h
    obtain ⟨w, hw, hv⟩ := h
    obtain ⟨iw, tw⟩ := eval_sound₄ a ht hw
    cases w <;> simp at hv
    subst hv
    cases tw with
    | pair _ t₂ => exact ⟨iw.2, t₂⟩
  | .inl τ a, _, _, .inl hc ht, h => by
    simp only [Atom₄.eval, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    obtain ⟨iw, tw⟩ := eval_sound₄ a ht hw
    exact ⟨iw, .inl hc tw⟩
  | .inr τ a, _, _, .inr hc ht, h => by
    simp only [Atom₄.eval, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    obtain ⟨iw, tw⟩ := eval_sound₄ a ht hw
    exact ⟨iw, .inr hc tw⟩
end

theorem canon_int₄ {v : Atom₄} (hv : IsVal₄ v) (h : RTA₄ [] v t4int) : ∃ k, v = c4 k := by
  cases v <;> simp [IsVal₄] at hv <;> cases h
  all_goals first | exact ⟨_, rfl⟩ | (rename_i h; simp at h)

theorem canon_lock₄ {v : Atom₄} (hv : IsVal₄ v) (h : RTA₄ [] v t4lock) : ∃ l, v = lockv l := by
  cases v <;> simp [IsVal₄] at hv <;> cases h
  all_goals first | exact ⟨_, rfl⟩ | (rename_i h; simp at h)

/-! ## Part (ii), the configurations: preservation through ⟶₄ (addendum 6). -/

/-- The trivial invariant: the shared part only records which regions the free locks own. -/
def Itriv : Int → Assn := fun _ _ => True

/-- A thread's typed configuration: its regions σ, the free locks' regions σS, any frame σF. -/
def TC (L : List LockSt) (σ σS σF : Store) : Prop :=
  Store.Disj σ (σS ⊎ σF) ∧ Store.Disj σS σF ∧ Shared Itriv L σS ∧ Store.WF (σ ⊎ (σS ⊎ σF))

theorem decide_tcap_false₄ {t : Ty₄} (h : hasCap₄ t = false) : decide (t = t4cap) = false := by
  by_cases e : t = t4cap
  · subst e; simp [hasCap₄, t4cap] at h
  · simp [e]

theorem tc_split {L : List LockSt} {σ₁ σ₂ σS σF : Store} (h12 : Store.Disj σ₁ σ₂) (htc : TC L (σ₁ ⊎ σ₂) σS σF) :
    TC L σ₁ σS (σ₂ ⊎ σF) ∧ Store.Disj σ₂ σF ∧ (σ₁ ⊎ σ₂) ⊎ (σS ⊎ σF) = σ₁ ⊎ (σS ⊎ (σ₂ ⊎ σF)) := by
  obtain ⟨hd, hSF, hsh, hwf⟩ := htc
  obtain ⟨h1, h2⟩ := (Store.disj_union_left _ _ _).1 hd
  obtain ⟨h1S, h1F⟩ := (Store.disj_union_right _ _ _).1 h1
  obtain ⟨h2S, h2F⟩ := (Store.disj_union_right _ _ _).1 h2
  have heq : (σ₁ ⊎ σ₂) ⊎ (σS ⊎ σF) = σ₁ ⊎ (σS ⊎ (σ₂ ⊎ σF)) := by
    rw [Store.union_assoc, swap12 h2S]
  refine ⟨⟨(Store.disj_union_right _ _ _).2 ⟨h1S, (Store.disj_union_right _ _ _).2 ⟨h12, h1F⟩⟩,
    (Store.disj_union_right _ _ _).2 ⟨disj_symm h2S, hSF⟩, hsh, heq ▸ hwf⟩, h2F, heq⟩

theorem tc_join {L : List LockSt} {σ₁ σ₂ σS σF : Store} (htc : TC L σ₁ σS (σ₂ ⊎ σF)) (h2F : Store.Disj σ₂ σF) :
    Store.Disj σ₁ σ₂ ∧ TC L (σ₁ ⊎ σ₂) σS σF ∧ σ₁ ⊎ (σS ⊎ (σ₂ ⊎ σF)) = (σ₁ ⊎ σ₂) ⊎ (σS ⊎ σF) := by
  obtain ⟨hd, hSF, hsh, hwf⟩ := htc
  obtain ⟨h1S, h1r⟩ := (Store.disj_union_right _ _ _).1 hd
  obtain ⟨h12, h1F⟩ := (Store.disj_union_right _ _ _).1 h1r
  obtain ⟨hS2, hSF'⟩ := (Store.disj_union_right _ _ _).1 hSF
  have heq : σ₁ ⊎ (σS ⊎ (σ₂ ⊎ σF)) = (σ₁ ⊎ σ₂) ⊎ (σS ⊎ σF) := by
    rw [Store.union_assoc, swap12 (disj_symm hS2)]
  refine ⟨h12, ⟨(Store.disj_union_left _ _ _).2 ⟨(Store.disj_union_right _ _ _).2 ⟨h1S, h1F⟩,
    (Store.disj_union_right _ _ _).2 ⟨disj_symm hS2, h2F⟩⟩, hSF', hsh, heq ▸ hwf⟩, heq⟩

/-- Binding a `ret`'s value: a non-capability value by `substV₄`, a ⟨p⟩ by `substC₄` (the binder then owns p). -/
theorem bind_one {Γ : Ctx₄} {Δ : List Bool} {Ω Ωa : List Int} {τ' τ : Ty₄} {e : Tm₄} {a v : Atom₄}
    (h : RT₄ (τ' :: Γ) (decide (τ' = t4cap) :: Δ) Ω e τ) (ha : RT₄ [] [] Ωa (.ret a) τ') (hv : Atom₄.eval a = some v) :
    RT₄ Γ Δ (Ωa ++ Ω) (e.subst 0 v) τ := by
  cases ha with
  | ret _ hat =>
    obtain ⟨-, hwt⟩ := eval_sound₄ _ hat hv
    rw [decide_tcap_false₄ (atom_noCap₄ hat)] at h
    exact substV₄ (Γ₁ := []) (Δ₁ := []) rfl h (.inl hwt)
  | retCap hΓ _ => simp at hΓ
  | retCapC _ =>
    simp [Atom₄.eval, capv] at hv; subst hv
    rw [show decide (t4cap = t4cap) = true from decide_eq_true rfl] at h
    exact substC₄ (Γ₁ := []) (Δ₁ := []) _ rfl h

theorem op4_o2 {o : Op} {vs : List Atom₄} {s : Store₄} {v : Atom₄} {s' : Store₄} (h : opStep₄ (.o2 o) vs s = some (v, s')) :
    ∃ ws w σ', vs.mapM lowerV = some ws ∧ opStep o ws s.σ = some (w, σ') ∧ v = raiseV w ∧ s' = ⟨σ', s.locks⟩ := by
  simp only [opStep₄, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨ws, hws, ⟨w, σ'⟩, hop, he⟩ := h
  simp only [Prod.mk.injEq] at he
  exact ⟨ws, w, σ', hws, hop, he.1.symm, he.2.symm⟩

theorem evalL_one {a : Atom₄} {vs : List Atom₄} (h : Atom₄.evalL [a] = some vs) :
    ∃ w, Atom₄.eval a = some w ∧ vs = [w] := by
  simp only [Atom₄.evalL] at h
  cases ha : Atom₄.eval a <;> simp_all

theorem evalL_two {a b : Atom₄} {vs : List Atom₄} (h : Atom₄.evalL [a, b] = some vs) :
    ∃ w₁ w₂, Atom₄.eval a = some w₁ ∧ Atom₄.eval b = some w₂ ∧ vs = [w₁, w₂] := by
  simp only [Atom₄.evalL] at h
  cases ha : Atom₄.eval a <;> cases hb : Atom₄.eval b <;> simp_all

theorem evalL_three {a b d : Atom₄} {vs : List Atom₄} (h : Atom₄.evalL [a, b, d] = some vs) :
    ∃ w₁ w₂ w₃, Atom₄.eval a = some w₁ ∧ Atom₄.eval b = some w₂ ∧ Atom₄.eval d = some w₃ ∧ vs = [w₁, w₂, w₃] := by
  simp only [Atom₄.evalL] at h
  cases ha : Atom₄.eval a <;> cases hb : Atom₄.eval b <;> cases hd : Atom₄.eval d <;> simp_all

set_option maxHeartbeats 2000000 in
/-- **PRESERVATION through ⟶₄ (Q6-P, addendum 6), in frame form.** A step from a typed configuration (the thread owns exactly Ω's
  regions, the free locks own theirs, any frame) lands in a typed configuration: Ω moves as the step's operation says. -/
theorem pres₄ : ∀ {c c' : Config₄}, Step₄ c c' → ∀ {Ω τ σ σS σF}, RT₄ [] [] Ω c.1 τ → OwnAll Ω σ →
    TC c.2.locks σ σS σF → c.2.σ = σ ⊎ (σS ⊎ σF) →
    ∃ Ω' σ' σS', RT₄ [] [] Ω' c'.1 τ ∧ OwnAll Ω' σ' ∧ TC c'.2.locks σ' σS' σF ∧ c'.2.σ = σ' ⊎ (σS' ⊎ σF) := by
  intro c c' h
  induction h with
  | letRet hv =>
    intro Ω τ σ σS σF hrt hown htc hσ
    cases hrt with
    | letE hs hp hc h₁ h₂ =>
      cases hs
      exact ⟨_, σ, σS, bind_one h₂ h₁ hv, OwnAll.perm hp _ hown, htc, hσ⟩
  | letStep _ ih =>
    intro Ω τ σ σS σF hrt hown htc hσ
    cases hrt with
    | letE hs hp hc h₁ h₂ =>
      cases hs
      obtain ⟨σ₁, σ₂, h12, rfl, ho₁, ho₂⟩ := (OwnAll.append _ _ _).1 (OwnAll.perm hp _ hown)
      obtain ⟨htc₁, h2F, heq⟩ := tc_split h12 htc
      obtain ⟨Ω₁', σ₁', σS', ht₁', ho₁', htc', hσ'⟩ := ih h₁ ho₁ htc₁ (hσ.trans heq)
      obtain ⟨h12', htcj, heq'⟩ := tc_join htc' h2F
      exact ⟨Ω₁' ++ _, σ₁' ⊎ σ₂, σS', RT₄.letE .nil (List.Perm.refl _) hc ht₁' h₂,
        (OwnAll.append _ _ _).2 ⟨σ₁', σ₂, h12', rfl, ho₁', ho₂⟩, htcj, hσ'.trans heq'⟩
  | appLam hv₁ hv₂ =>
    intro Ω τ σ σS σF hrt hown htc hσ
    cases hrt with
    | app _ h₁ h₂ =>
      obtain ⟨-, hwt₁⟩ := eval_sound₄ _ h₁ hv₁
      obtain ⟨-, hwt₂⟩ := eval_sound₄ _ h₂ hv₂
      cases hwt₁ with
      | lam _ _ hm hl hb =>
        obtain rfl := mask_one hm hl
        exact ⟨[], σ, σS, substV₄ (Γ₁ := []) (Δ₁ := []) rfl hb (.inl hwt₂), hown, htc, hσ⟩
  | appFix hv₁ hv₂ =>
    intro Ω τ σ σS σF hrt hown htc hσ
    cases hrt with
    | app _ h₁ h₂ =>
      obtain ⟨-, hwt₁⟩ := eval_sound₄ _ h₁ hv₁
      obtain ⟨-, hwt₂⟩ := eval_sound₄ _ h₂ hv₂
      have hfix := hwt₁
      cases hwt₁ with
      | fix _ _ hm hl hb =>
        obtain rfl := mask_two hm hl
        exact ⟨[], σ, σS, substV₄ (Γ₁ := []) (Δ₁ := []) rfl
          (substV₄ (Γ₁ := []) (Δ₁ := []) rfl hb (.inl hwt₂)) (.inl hfix), hown, htc, hσ⟩
  | iteT _ _ =>
    intro Ω τ σ σS σF hrt hown htc hσ
    cases hrt with
    | ite _ h₁ _ => exact ⟨Ω, σ, σS, h₁, hown, htc, hσ⟩
  | iteF _ _ =>
    intro Ω τ σ σS σF hrt hown htc hσ
    cases hrt with
    | ite _ _ h₂ => exact ⟨Ω, σ, σS, h₂, hown, htc, hσ⟩
  | caseL hv =>
    intro Ω τ σ σS σF hrt hown htc hσ
    cases hrt with
    | case ha h₁ _ =>
      obtain ⟨-, hwt⟩ := eval_sound₄ _ ha hv
      cases hwt with
      | inl _ hx => exact ⟨Ω, σ, σS, substV₄ (Γ₁ := []) (Δ₁ := []) rfl h₁ (.inl hx), hown, htc, hσ⟩
  | caseR hv =>
    intro Ω τ σ σS σF hrt hown htc hσ
    cases hrt with
    | case ha _ h₂ =>
      obtain ⟨-, hwt⟩ := eval_sound₄ _ ha hv
      cases hwt with
      | inr _ hx => exact ⟨Ω, σ, σS, substV₄ (Γ₁ := []) (Δ₁ := []) rfl h₂ (.inl hx), hown, htc, hσ⟩
  | @op o as τ' e vs v s s' hvs hop =>
    intro Ω τ σ σS σF hrt hown htc hσ
    obtain ⟨σg, L⟩ := s
    simp only at hσ htc ⊢
    subst hσ
    obtain ⟨hd, hSF, hsh, hwf⟩ := htc
    cases hrt with
    | alloc ha ht =>
      obtain ⟨w, hw, rfl⟩ := evalL_one hvs
      obtain ⟨iw, tw⟩ := eval_sound₄ _ ha hw
      obtain ⟨k, rfl⟩ := canon_int₄ iw tw
      obtain ⟨ws, w', σ'', hws, hop', rfl, rfl⟩ := op4_o2 hop
      simp [lowerV, c4] at hws; subst hws
      have hk : 0 < k := by
        simp only [opStep, Store.alloc] at hop'
        by_contra hc; rw [if_neg hc] at hop'; simp at hop'
      obtain ⟨v₁, σn, hop'', hdn, hwfn, p, rfl, hreg⟩ :=
        alloc_axiom k hk Store.empty (σ ⊎ (σS ⊎ σF)) rfl (disj_empty_left _) (by rw [Store.empty_union]; exact hwf)
      rw [Store.empty_union] at hop''
      simp only at hop'
      rw [hop'] at hop''; cases hop''
      obtain ⟨hdnq, hdnr⟩ := (Store.disj_union_right _ _ _).1 hdn
      refine ⟨p :: Ω, σn ⊎ σ, σS, substC₄ (Γ₁ := []) (Δ₁ := []) p rfl ht, ⟨σn, σ, hdnq, rfl, ⟨_, hreg.isRegion⟩, hown⟩,
        ⟨(Store.disj_union_left _ _ _).2 ⟨hdnr, hd⟩, hSF, hsh, by rw [Store.union_assoc]; exact hwfn⟩, by
          simp [raiseV, Store.union_assoc]⟩
    | load hΓ _ _ _ => simp at hΓ
    | loadC hp ha ht =>
      obtain ⟨w₀, w, hw₀, hw, rfl⟩ := evalL_two hvs
      simp [Atom₄.eval, capv] at hw₀; subst hw₀
      obtain ⟨iw, tw⟩ := eval_sound₄ _ ha hw
      obtain ⟨i, rfl⟩ := canon_int₄ iw tw
      obtain ⟨ws, w', σ'', hws, hop', rfl, rfl⟩ := op4_o2 hop
      simp [lowerV, c4] at hws; subst hws
      simp only [opStep, Option.map_eq_some_iff] at hop'
      obtain ⟨u, -, hu⟩ := hop'
      simp only [Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      exact ⟨Ω, σ, σS, substV₄ (Γ₁ := []) (Δ₁ := []) rfl ht (.inl .int), hown, ⟨hd, hSF, hsh, hwf⟩, rfl⟩
    | store hΓ _ _ _ _ => simp at hΓ
    | storeC hp h₁ h₂ ht =>
      obtain ⟨w₀, w₁, w₂, hw₀, hw₁, hw₂, rfl⟩ := evalL_three hvs
      simp [Atom₄.eval, capv] at hw₀; subst hw₀
      obtain ⟨i, rfl⟩ := canon_int₄ (eval_sound₄ _ h₁ hw₁).1 (eval_sound₄ _ h₁ hw₁).2
      obtain ⟨x, rfl⟩ := canon_int₄ (eval_sound₄ _ h₂ hw₂).1 (eval_sound₄ _ h₂ hw₂).2
      obtain ⟨σr, σs, hrs, rfl, ⟨n, hreg⟩, hos⟩ := OwnAll.extract hp hown
      obtain ⟨hdr, hds⟩ := (Store.disj_union_left _ _ _).1 hd
      have hd' : Store.Disj σr (σs ⊎ (σS ⊎ σF)) := (Store.disj_union_right _ _ _).2 ⟨hrs, hdr⟩
      rw [Store.union_assoc] at hop hwf
      obtain ⟨ws, w', σ'', hws, hop', rfl, rfl⟩ := op4_o2 hop
      simp [lowerV, c4, capv] at hws; subst hws
      have hlk := hreg.lookup_union (σs ⊎ (σS ⊎ σF))
      have hi : 0 ≤ i ∧ i < n := by
        simp only [opStep, Store.store, hlk] at hop'
        by_contra hc; rw [if_neg hc] at hop'; simp at hop'
      obtain ⟨c, σn, hop'', hdn, hwfn, rfl, hreg'⟩ := store_region _ n i x hi σr (σs ⊎ (σS ⊎ σF)) hreg hd' hwf
      simp only at hop'
      rw [hop'] at hop''; cases hop''
      obtain ⟨hdns, hdnr⟩ := (Store.disj_union_right _ _ _).1 hdn
      refine ⟨_ :: _, σn ⊎ σs, σS, substC₄ (Γ₁ := []) (Δ₁ := []) _ rfl ht, ⟨σn, σs, hdns, rfl, ⟨n, hreg'⟩, hos⟩,
        ⟨(Store.disj_union_left _ _ _).2 ⟨hdnr, hds⟩, hSF, hsh, by rw [Store.union_assoc]; exact hwfn⟩, by
          simp [raiseV, Store.union_assoc]⟩
    | free hΓ _ _ => simp at hΓ
    | freeC hp ht =>
      obtain ⟨w₀, hw₀, rfl⟩ := evalL_one hvs
      simp [Atom₄.eval, capv] at hw₀; subst hw₀
      obtain ⟨σr, σs, hrs, rfl, ⟨n, hreg⟩, hos⟩ := OwnAll.extract hp hown
      obtain ⟨hdr, hds⟩ := (Store.disj_union_left _ _ _).1 hd
      have hd' : Store.Disj σr (σs ⊎ (σS ⊎ σF)) := (Store.disj_union_right _ _ _).2 ⟨hrs, hdr⟩
      rw [Store.union_assoc] at hop hwf
      obtain ⟨ws, w', σ'', hws, hop', rfl, rfl⟩ := op4_o2 hop
      simp [lowerV, capv] at hws; subst hws
      obtain ⟨c, σn, hop'', hdn, hwfn, rfl, rfl⟩ := free_axiom _ n σr (σs ⊎ (σS ⊎ σF)) hreg hd' hwf
      simp only at hop'
      rw [hop'] at hop''; cases hop''
      rw [Store.empty_union] at hwfn
      exact ⟨_, σs, σS, substV₄ (Γ₁ := []) (Δ₁ := []) rfl ht (.inl .unit), hos, ⟨hds, hSF, hsh, hwfn⟩, by
        simp [raiseV, Store.empty_union]⟩
    | newlock hΓ _ _ => simp at hΓ
    | newlockC hp ht =>
      obtain ⟨w₀, hw₀, rfl⟩ := evalL_one hvs
      simp [Atom₄.eval, capv] at hw₀; subst hw₀
      simp only [opStep₄, Option.some.injEq, Prod.mk.injEq] at hop
      obtain ⟨rfl, rfl⟩ := hop
      obtain ⟨σr, σs, hrs, rfl, hreg, hos⟩ := OwnAll.extract hp hown
      obtain ⟨hdr, hds⟩ := (Store.disj_union_left _ _ _).1 hd
      obtain ⟨hrS, hrF⟩ := (Store.disj_union_right _ _ _).1 hdr
      obtain ⟨hsS, hsF⟩ := (Store.disj_union_right _ _ _).1 hds
      refine ⟨_, σs, σr ⊎ σS, substV₄ (Γ₁ := []) (Δ₁ := []) rfl ht (.inl .lockC), hos,
        ⟨(Store.disj_union_right _ _ _).2 ⟨(Store.disj_union_right _ _ _).2 ⟨disj_symm hrs, hsS⟩, hsF⟩,
          (Store.disj_union_left _ _ _).2 ⟨hrF, hSF⟩, shared_append _ _ _ _ hsh hrS hreg trivial, ?_⟩, ?_⟩
      · simp only [Store.union_assoc] at hwf ⊢; rw [← swap12 hrs]; exact hwf
      · simp only [Store.union_assoc]; first | exact swap12 hrs | exact (swap12 hrs).symm
    | acquire ha ht =>
      obtain ⟨w, hw, rfl⟩ := evalL_one hvs
      obtain ⟨l, rfl⟩ := canon_lock₄ (eval_sound₄ _ ha hw).1 (eval_sound₄ _ ha hw).2
      simp only [opStep₄, lockv] at hop
      split at hop
      · rename_i p hl
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        obtain ⟨σI, σS', hIS, rfl, hreg, -, hsh'⟩ := shared_take L l p σS hl hsh
        obtain ⟨hIS', hSF'⟩ := (Store.disj_union_left _ _ _).1 hSF
        obtain ⟨hσI, hσS'⟩ := (Store.disj_union_right _ _ _).1 ((Store.disj_union_right _ _ _).1 hd).1
        have hσF := ((Store.disj_union_right _ _ _).1 hd).2
        refine ⟨p :: Ω, σI ⊎ σ, σS', substC₄ (Γ₁ := []) (Δ₁ := []) p rfl ht, ⟨σI, σ, disj_symm hσI, rfl, hreg, hown⟩,
          ⟨(Store.disj_union_left _ _ _).2 ⟨(Store.disj_union_right _ _ _).2 ⟨hIS, hIS'⟩,
            (Store.disj_union_right _ _ _).2 ⟨hσS', hσF⟩⟩, hSF', hsh', ?_⟩, ?_⟩
        · simp only [Store.union_assoc] at hwf ⊢; rw [← swap12 hσI]; exact hwf
        · simp only [Store.union_assoc]; first | exact swap12 hσI | exact (swap12 hσI).symm
      · simp at hop
    | release _ hΓ _ _ => simp at hΓ
    | releaseC ha hp ht =>
      obtain ⟨w, w₀, hw, hw₀, rfl⟩ := evalL_two hvs
      simp [Atom₄.eval, capv] at hw₀; subst hw₀
      obtain ⟨l, rfl⟩ := canon_lock₄ (eval_sound₄ _ ha hw).1 (eval_sound₄ _ ha hw).2
      simp only [opStep₄, lockv] at hop
      split at hop
      · rename_i q hl
        split at hop
        · rename_i hpq
          subst hpq
          simp only [Option.some.injEq, Prod.mk.injEq] at hop
          obtain ⟨rfl, rfl⟩ := hop
          obtain ⟨σr, σs, hrs, rfl, hreg, hos⟩ := OwnAll.extract hp hown
          obtain ⟨hdr, hds⟩ := (Store.disj_union_left _ _ _).1 hd
          obtain ⟨hrS, hrF⟩ := (Store.disj_union_right _ _ _).1 hdr
          obtain ⟨hsS, hsF⟩ := (Store.disj_union_right _ _ _).1 hds
          refine ⟨_, σs, σr ⊎ σS, substV₄ (Γ₁ := []) (Δ₁ := []) rfl ht (.inl .unit), hos,
            ⟨(Store.disj_union_right _ _ _).2 ⟨(Store.disj_union_right _ _ _).2 ⟨disj_symm hrs, hsS⟩, hsF⟩,
              (Store.disj_union_left _ _ _).2 ⟨hrF, hSF⟩, shared_put _ _ _ _ _ hl hsh hrS hreg trivial, ?_⟩, ?_⟩
          · simp only [Store.union_assoc] at hwf ⊢; rw [← swap12 hrs]; exact hwf
          · simp only [Store.union_assoc]; first | exact swap12 hrs | exact (swap12 hrs).symm
        · simp at hop
      · simp at hop
  | parL _ ih =>
    intro Ω τ σ σS σF hrt hown htc hσ
    cases hrt with
    | par hs₁ hs₂ hp hc₁ hc₂ h₁ h₂ h =>
      cases hs₁; cases hs₂
      have hp' := hp.trans (List.Perm.of_eq (List.append_assoc _ _ _))
      obtain ⟨σ₁, σ₂, h12, rfl, ho₁, ho₂⟩ := (OwnAll.append _ _ _).1 (OwnAll.perm hp' _ hown)
      obtain ⟨htc₁, h2F, heq⟩ := tc_split h12 htc
      obtain ⟨Ω₁', σ₁', σS', ht₁', ho₁', htc', hσ'⟩ := ih h₁ ho₁ htc₁ (hσ.trans heq)
      obtain ⟨h12', htcj, heq'⟩ := tc_join htc' h2F
      exact ⟨Ω₁' ++ (_ ++ _), σ₁' ⊎ σ₂, σS', RT₄.par .nil .nil (List.Perm.of_eq (List.append_assoc _ _ _).symm) hc₁ hc₂ ht₁' h₂ h,
        (OwnAll.append _ _ _).2 ⟨σ₁', σ₂, h12', rfl, ho₁', ho₂⟩, htcj, hσ'.trans heq'⟩
  | parR _ ih =>
    intro Ω τ σ σS σF hrt hown htc hσ
    cases hrt with
    | par hs₁ hs₂ hp hc₁ hc₂ h₁ h₂ h =>
      cases hs₁; cases hs₂
      have hp' : Ω.Perm (_ ++ (_ ++ _)) :=
        hp.trans ((List.perm_append_comm.append_right _).trans (List.Perm.of_eq (List.append_assoc _ _ _)))
      obtain ⟨σ₂, σ₁, h21, rfl, ho₂, ho₁⟩ := (OwnAll.append _ _ _).1 (OwnAll.perm hp' _ hown)
      obtain ⟨htc₂, h1F, heq⟩ := tc_split h21 htc
      obtain ⟨Ω₂', σ₂', σS', ht₂', ho₂', htc', hσ'⟩ := ih h₂ ho₂ htc₂ (hσ.trans heq)
      obtain ⟨h21', htcj, heq'⟩ := tc_join htc' h1F
      refine ⟨Ω₂' ++ (_ ++ _), σ₂' ⊎ σ₁, σS', RT₄.par .nil .nil ?_ hc₁ hc₂ h₁ ht₂' h,
        (OwnAll.append _ _ _).2 ⟨σ₂', σ₁, h21', rfl, ho₂', ho₁⟩, htcj, hσ'.trans heq'⟩
      exact (List.Perm.of_eq (List.append_assoc _ _ _).symm).trans (List.perm_append_comm.append_right _)
  | parDone hv₁ hv₂ =>
    intro Ω τ σ σS σF hrt hown htc hσ
    cases hrt with
    | par hs₁ hs₂ hp hc₁ hc₂ h₁ h₂ h =>
      cases hs₁; cases hs₂
      have hb := bind_one (bind_one h h₂ hv₂) h₁ hv₁
      exact ⟨_, σ, σS, hb, OwnAll.perm (hp.trans (List.Perm.of_eq (List.append_assoc _ _ _))) _ hown, htc, hσ⟩

theorem pres₄_steps {c c' : Config₄} (h : Steps₄ c c') :
    ∀ {Ω τ σ σS σF}, RT₄ [] [] Ω c.1 τ → OwnAll Ω σ → TC c.2.locks σ σS σF → c.2.σ = σ ⊎ (σS ⊎ σF) →
    ∃ Ω' σ' σS', RT₄ [] [] Ω' c'.1 τ ∧ OwnAll Ω' σ' ∧ TC c'.2.locks σ' σS' σF ∧ c'.2.σ = σ' ⊎ (σS' ⊎ σF) := by
  induction h with
  | refl c => intro Ω τ σ σS σF ht ho htc hσ; exact ⟨Ω, σ, σS, ht, ho, htc, hσ⟩
  | step hs _ ih =>
    intro Ω τ σ σS σF ht ho htc hσ
    obtain ⟨Ω', σ', σS', ht', ho', htc', hσ'⟩ := pres₄ hs ht ho htc hσ
    exact ih ht' ho' htc' hσ'

/-- **Q6, PRESERVED (addendum 6):** from a typed configuration, EVERY ⟶₄*-reachable configuration is typed (some Ω' with the
  thread part owning exactly its regions), hence has no race on any region. -/
theorem Q6_reach {Ω : List Int} {e : Tm₄} {τ : Ty₄} {σ σS σF : Store} {L : List LockSt}
    (ht : RT₄ [] [] Ω e τ) (ho : OwnAll Ω σ) (htc : TC L σ σS σF) :
    ∀ c, Steps₄ (e, ⟨σ ⊎ (σS ⊎ σF), L⟩) c → ∀ p, ¬ Race c.1 p := by
  intro c hc p
  obtain ⟨Ω', σ', -, ht', ho', -, -⟩ := pres₄_steps hc ht ho htc rfl
  exact Q6_no_race ht' ho' p

/-- From the empty store and lock table: a closed RT₄-typed program owning nothing never races, on any interleaving. -/
theorem Q6_reach_empty {e : Tm₄} {τ : Ty₄} (ht : RT₄ [] [] [] e τ) :
    ∀ c, Steps₄ (e, ⟨Store.empty, []⟩) c → ∀ p, ¬ Race c.1 p := by
  have h := Q6_reach (σ := Store.empty) (σS := Store.empty) (σF := Store.empty) (L := []) ht rfl
    ⟨by rw [Store.empty_union]; exact disj_empty_empty, disj_empty_empty, rfl,
      by rw [Store.empty_union, Store.empty_union]; exact wf_empty⟩
  simpa [Store.empty_union] using h

/-! ## A statically typed program is runtime-typed owning nothing (⊢₄ ⇒ RT₄ with Ω = []). -/

mutual
theorem rtA_of : ∀ {Γ a τ}, HasTypeA₄ Γ a τ → RTA₄ Γ a τ
  | _, _, _, .var h hc => .var h hc
  | _, _, _, .int => .int
  | _, _, _, .bool => .bool
  | _, _, _, .unit => .unit
  | _, _, _, .prim h => .prim (rtL_of h)
  | _, _, _, .lam h₁ h₂ hΔ hl h => .lam h₁ h₂ hΔ hl (rt_of h)
  | _, _, _, .fix h₁ h₂ hΔ hl h => .fix h₁ h₂ hΔ hl (rt_of h)
  | _, _, _, .pair h₁ h₂ => .pair (rtA_of h₁) (rtA_of h₂)
  | _, _, _, .fst h => .fst (rtA_of h)
  | _, _, _, .snd h => .snd (rtA_of h)
  | _, _, _, .inl hc h => .inl hc (rtA_of h)
  | _, _, _, .inr hc h => .inr hc (rtA_of h)
theorem rtL_of : ∀ {Γ as τs}, HasTypeL₄ Γ as τs → RTL₄ Γ as τs
  | _, _, _, .nil => .nil
  | _, _, _, .cons h hs => .cons (rtA_of h) (rtL_of hs)
theorem rt_of : ∀ {Γ Δ e τ}, HasType₄ Γ Δ e τ → RT₄ Γ Δ [] e τ
  | _, _, _, _, .ret hΔ h => .ret hΔ (rtA_of h)
  | _, _, _, _, .retCap hΓ hΔ => .retCap hΓ hΔ
  | _, _, _, _, .letE hs hc h₁ h₂ => .letE hs (List.Perm.refl _) hc (rt_of h₁) (rt_of h₂)
  | _, _, _, _, .alloc ha h => .alloc (rtA_of ha) (rt_of h)
  | _, _, _, _, .load hΓ hΔ ha h => .load hΓ hΔ (rtA_of ha) (rt_of h)
  | _, _, _, _, .store hΓ hΔ h₁ h₂ h => .store hΓ hΔ (rtA_of h₁) (rtA_of h₂) (rt_of h)
  | _, _, _, _, .free hΓ hΔ h => .free hΓ hΔ (rt_of h)
  | _, _, _, _, .app hΔ h₁ h₂ => .app hΔ (rtA_of h₁) (rtA_of h₂)
  | _, _, _, _, .ite h h₁ h₂ => .ite (rtA_of h) (rt_of h₁) (rt_of h₂)
  | _, _, _, _, .case h h₁ h₂ => .case (rtA_of h) (rt_of h₁) (rt_of h₂)
  | _, _, _, _, .newlock hΓ hΔ h => .newlock hΓ hΔ (rt_of h)
  | _, _, _, _, .acquire ha h => .acquire (rtA_of ha) (rt_of h)
  | _, _, _, _, .release ha hΓ hΔ h => .release (rtA_of ha) hΓ hΔ (rt_of h)
  | _, _, _, _, .par hs₁ hs₂ hc₁ hc₂ h₁ h₂ h => .par hs₁ hs₂ (List.Perm.refl _) hc₁ hc₂ (rt_of h₁) (rt_of h₂) (rt_of h)
end

/-- **Q6 FOR EVERY REACHABLE CONFIGURATION OF A TYPED PROGRAM (addendum 6, the stronger reading of addendum 3):** a closed
  ⊢₄-typed program, run from the empty store and lock table, has no race on any region at any ⟶₄*-reachable configuration. -/
theorem Q6_typed_program {e : Tm₄} {τ : Ty₄} (ht : HasType₄ [] [] e τ) :
    ∀ c, Steps₄ (e, ⟨Store.empty, []⟩) c → ∀ p, ¬ Race c.1 p :=
  Q6_reach_empty (rt_of ht)

/-- Control (the hypothesis is met by a real program): N1, the two-thread locked counter, never races. -/
theorem N1_no_race : ∀ c, Steps₄ (N1, ⟨Store.empty, []⟩) c → ∀ p, ¬ Race c.1 p := Q6_typed_program N1_typed

end VIRL4
