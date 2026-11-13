/-
  O95 layer L5, Lean arm (amend-24 LV4 groundwork). WEAKENING at the end of the context (L2's `weak₂`, restated for ⊢₅; part of
  `L5.syntaxCopy`), so a closed well-typed atom is typed in any context (`closedA₅`). The new cases are the three L1′ rules: their
  capability lists (`CapsExact`) only mention indices below Γ.length, and the appended positions are `false`.
-/
import VIRL5.Typing5
import VIRL2.MaskLemmas

namespace VIRL5
open VIRL1 VIRL2

theorem getElem?_pad {Δ : List Bool} {k n : Nat} : (Δ ++ List.replicate k false)[n]? = some true ↔ Δ[n]? = some true := by
  constructor
  · intro h
    by_cases hl : n < Δ.length
    · rwa [List.getElem?_append_left hl] at h
    · rw [List.getElem?_append_right (by omega), List.getElem?_replicate] at h; split_ifs at h <;> simp at h
  · intro h
    have hl : n < Δ.length := (List.getElem?_eq_some_iff.1 h).1
    rwa [List.getElem?_append_left hl]

theorem getElem?_app_left {α : Type} {Γ Γ' : List α} {n : Nat} {x : α} (h : Γ[n]? = some x) : (Γ ++ Γ')[n]? = some x := by
  have hl : _ < _ := (List.getElem?_eq_some_iff.1 h).1
  rw [List.getElem?_append_left hl]; exact h

theorem CapsExact.pad {Γ : Ctx₅} {Δ : List Bool} {ns : List Nat} (Γ' : Ctx₅) (h : CapsExact Γ Δ ns) :
    CapsExact (Γ ++ Γ') (Δ ++ List.replicate Γ'.length false) ns :=
  ⟨h.1, fun n hn => getElem?_app_left (h.2.1 n hn), fun n => by rw [getElem?_pad]; exact h.2.2 n⟩

mutual
theorem weakA₅ : ∀ {Γ a τ} (Γ' : Ctx₅), HasTypeA₅ Γ a τ → HasTypeA₅ (Γ ++ Γ') a τ
  | _, _, _, _, .var h hc => .var (getElem?_app_left h) hc
  | _, _, _, _, .int => .int
  | _, _, _, _, .bool => .bool
  | _, _, _, _, .unit => .unit
  | _, _, _, Γ', .prim h => .prim (weakL₅ Γ' h)
  | _, _, _, Γ', .lam (k := k) h₁ h₂ hΔ hl h => by
      have := weak₅ Γ' h
      simp only [List.append_assoc, List.cons_append] at this
      exact .lam h₁ h₂ (mask_empty_pad Γ'.length hΔ) (by simp [hl]; omega) this
  | _, _, _, Γ', .fix (k := k) h₁ h₂ hΔ hl h => by
      have := weak₅ Γ' h
      simp only [List.append_assoc, List.cons_append] at this
      exact .fix h₁ h₂ (mask_empty_pad Γ'.length hΔ) (by simp [hl]; omega) this
  | _, _, _, Γ', .pair h₁ h₂ => .pair (weakA₅ Γ' h₁) (weakA₅ Γ' h₂)
  | _, _, _, Γ', .fst h => .fst (weakA₅ Γ' h)
  | _, _, _, Γ', .snd h => .snd (weakA₅ Γ' h)
  | _, _, _, Γ', .inl hc h => .inl hc (weakA₅ Γ' h)
  | _, _, _, Γ', .inr hc h => .inr hc (weakA₅ Γ' h)
theorem weakL₅ : ∀ {Γ as τs} (Γ' : Ctx₅), HasTypeL₅ Γ as τs → HasTypeL₅ (Γ ++ Γ') as τs
  | _, _, _, _, .nil => .nil
  | _, _, _, Γ', .cons h hs => .cons (weakA₅ Γ' h) (weakL₅ Γ' hs)
theorem weak₅ : ∀ {Γ Δ e τ k} (Γ' : Ctx₅), HasType₅ Γ Δ e τ k →
    HasType₅ (Γ ++ Γ') (Δ ++ List.replicate Γ'.length false) e τ k
  | _, _, _, _, _, Γ', .ret hΔ h => .ret (mask_empty_pad _ hΔ) (weakA₅ Γ' h)
  | _, _, _, _, _, Γ', .retCap hΓ hΔ => .retCap (getElem?_app_left hΓ) (mask_only_pad _ hΔ)
  | _, _, _, _, _, Γ', .letE hs hc h₁ h₂ => .letE (split_pad _ hs) hc (weak₅ Γ' h₁) (weak₅ Γ' h₂)
  | _, _, _, _, _, Γ', .alloc ha h => .alloc (weakA₅ Γ' ha) (weak₅ Γ' h)
  | _, _, _, _, _, Γ', .load hΓ hΔ ha h => .load (getElem?_app_left hΓ) (get_pad hΔ) (weakA₅ Γ' ha) (weak₅ Γ' h)
  | _, _, _, _, _, Γ', .store hΓ hΔ h₁ h₂ h => .store (getElem?_app_left hΓ) (get_pad hΔ) (weakA₅ Γ' h₁)
      (weakA₅ Γ' h₂) (by rw [set_pad hΔ]; exact weak₅ Γ' h)
  | _, _, _, _, _, Γ', .free hΓ hΔ h => .free (getElem?_app_left hΓ) (get_pad hΔ)
      (by rw [set_pad hΔ]; exact weak₅ Γ' h)
  | _, _, _, _, _, Γ', .app hΔ h₁ h₂ => .app (mask_empty_pad _ hΔ) (weakA₅ Γ' h₁) (weakA₅ Γ' h₂)
  | _, _, _, _, _, Γ', .ite h h₁ h₂ => .ite (weakA₅ Γ' h) (weak₅ Γ' h₁) (weak₅ Γ' h₂)
  | _, _, _, _, _, Γ', .case h h₁ h₂ => .case (weakA₅ Γ' h) (weak₅ Γ' h₁) (weak₅ Γ' h₂)
  | _, _, _, _, _, Γ', .retK hc h hx => .retK hc (weakA₅ Γ' h) (hx.pad Γ')
  | _, _, _, _, _, Γ', .appK h₁ h₂ hx => .appK (weakA₅ Γ' h₁) (weakA₅ Γ' h₂) (hx.pad Γ')
  | _, _, _, _, _, Γ', .letK hs hc h₁ h₂ => by
      have := weak₅ Γ' h₂
      simp only [List.append_assoc, List.cons_append] at this
      exact .letK (split_pad _ hs) hc (weak₅ Γ' h₁) this
end

theorem closedA₅ {v : Atom₅} {τ} (Γ : Ctx₅) (h : HasTypeA₅ [] v τ) : HasTypeA₅ Γ v τ := by
  simpa using weakA₅ Γ h

end VIRL5
