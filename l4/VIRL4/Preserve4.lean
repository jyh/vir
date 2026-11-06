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

end VIRL4
