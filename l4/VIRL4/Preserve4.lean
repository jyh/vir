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

end VIRL4
