/-
  O95 layer L2, Lean arm. Y5 groundwork: the linear-context mask with ONE position removed (the position a substitution
  eliminates), stated at depth k = Δ₁.length. These are amend-16 Y7's "lemmas about Δ alone" (EXPLORATORY): the split, the
  empty mask, `only`, `set`, and lookup, each commuting with the removal of a `false` position.
-/
import VIRL2.Typing2

namespace VIRL2
open VIRL1

theorem get_mid {α : Type} {Δ₁ Δ : List α} {b : α} (n : Nat) :
    (Δ₁ ++ b :: Δ)[n]? = if n < Δ₁.length then (Δ₁ ++ Δ)[n]? else if n = Δ₁.length then some b else (Δ₁ ++ Δ)[n - 1]? := by
  split_ifs with h₁ h₂
  · rw [List.getElem?_append_left h₁, List.getElem?_append_left h₁]
  · subst h₂; simp
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    obtain ⟨m, rfl⟩ : ∃ m, n = Δ₁.length + 1 + m := ⟨n - Δ₁.length - 1, by omega⟩
    simp [show Δ₁.length + 1 + m - Δ₁.length = m + 1 by omega, show Δ₁.length + 1 + m - 1 - Δ₁.length = m by omega]

/-- The index a variable keeps after the position k is removed (n ≠ k). -/
def dropIdx (k n : Nat) : Nat := if n < k then n else n - 1

theorem get_drop {α : Type} {Δ₁ Δ : List α} {b : α} {n : Nat} (hn : n ≠ Δ₁.length) :
    (Δ₁ ++ b :: Δ)[n]? = (Δ₁ ++ Δ)[dropIdx Δ₁.length n]? := by
  rw [get_mid]; unfold dropIdx; split_ifs <;> first | rfl | omega

theorem mask_empty_drop {Δ₁ Δ : List Bool} {b : Bool} (h : Mask.empty (Δ₁ ++ b :: Δ)) : Mask.empty (Δ₁ ++ Δ) := by
  intro m hm
  by_cases hk : m < Δ₁.length
  · exact h m (by rw [get_mid, if_pos hk]; exact hm)
  · exact h (m + 1) (by rw [get_mid, if_neg (by omega), if_neg (by omega)]; simpa using hm)

theorem mask_true_ne {Δ₁ Δ : List Bool} {n : Nat} (h : (Δ₁ ++ false :: Δ)[n]? = some true) : n ≠ Δ₁.length := by
  intro e; subst e; simp at h

theorem mask_only_drop {Δ₁ Δ : List Bool} {n : Nat} (h : Mask.only (Δ₁ ++ false :: Δ) n) :
    Mask.only (Δ₁ ++ Δ) (dropIdx Δ₁.length n) := by
  have hn := mask_true_ne h.1
  refine ⟨by rw [← get_drop hn]; exact h.1, fun m hm => ?_⟩
  by_cases hk : m < Δ₁.length
  · intro hm'
    exact h.2 m (by unfold dropIdx at hm; split_ifs at hm <;> omega) (by rw [get_mid, if_pos hk]; exact hm')
  · intro hm'
    refine h.2 (m + 1) (by unfold dropIdx at hm; split_ifs at hm <;> omega) ?_
    rw [get_mid, if_neg (by omega), if_neg (by omega)]; simpa using hm'

theorem set_mid {Δ₁ Δ : List Bool} {b : Bool} {n : Nat} (hn : n ≠ Δ₁.length) :
    (Δ₁ ++ b :: Δ).set n false =
      (if n < Δ₁.length then Δ₁.set n false else Δ₁) ++ b :: (if n < Δ₁.length then Δ else Δ.set (n - Δ₁.length - 1) false) := by
  split_ifs with h
  · rw [List.set_append_left _ _ h]
  · rw [List.set_append_right _ _ (by omega)]
    obtain ⟨m, rfl⟩ : ∃ m, n = Δ₁.length + 1 + m := ⟨n - Δ₁.length - 1, by omega⟩
    simp [show Δ₁.length + 1 + m - Δ₁.length = m + 1 by omega]

theorem set_drop {Δ₁ Δ : List Bool} {n : Nat} (hn : n ≠ Δ₁.length) :
    (if n < Δ₁.length then Δ₁.set n false else Δ₁) ++ (if n < Δ₁.length then Δ else Δ.set (n - Δ₁.length - 1) false) =
      (Δ₁ ++ Δ).set (dropIdx Δ₁.length n) false := by
  unfold dropIdx
  split_ifs with h
  · rw [List.set_append_left _ _ h]
  · rw [List.set_append_right _ _ (by omega)]; congr 2; omega

theorem split_length {Δ Δ₁ Δ₂ : List Bool} (h : Split Δ Δ₁ Δ₂) : Δ₁.length = Δ.length ∧ Δ₂.length = Δ.length := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | left _ ih | right _ ih | none _ ih => exact ⟨by simp [ih.1], by simp [ih.2]⟩

/-- A split of a mask with a `false` at depth k splits as two masks with `false` at depth k. -/
theorem split_mid {Δ₁ Δ A B : List Bool} (h : Split (Δ₁ ++ false :: Δ) A B) :
    ∃ A₁ A₂ B₁ B₂, A = A₁ ++ false :: A₂ ∧ B = B₁ ++ false :: B₂ ∧ A₁.length = Δ₁.length ∧ B₁.length = Δ₁.length ∧
      Split (Δ₁ ++ Δ) (A₁ ++ A₂) (B₁ ++ B₂) := by
  induction Δ₁ generalizing A B with
  | nil =>
    cases h with
    | none h => exact ⟨[], _, [], _, rfl, rfl, rfl, rfl, h⟩
  | cons d Δ₁ ih =>
    cases h with
    | left h =>
      obtain ⟨A₁, A₂, B₁, B₂, rfl, rfl, h₁, h₂, hs⟩ := ih h
      exact ⟨true :: A₁, A₂, false :: B₁, B₂, rfl, rfl, by simp [h₁], by simp [h₂], .left hs⟩
    | right h =>
      obtain ⟨A₁, A₂, B₁, B₂, rfl, rfl, h₁, h₂, hs⟩ := ih h
      exact ⟨false :: A₁, A₂, true :: B₁, B₂, rfl, rfl, by simp [h₁], by simp [h₂], .right hs⟩
    | none h =>
      obtain ⟨A₁, A₂, B₁, B₂, rfl, rfl, h₁, h₂, hs⟩ := ih h
      exact ⟨false :: A₁, A₂, false :: B₁, B₂, rfl, rfl, by simp [h₁], by simp [h₂], .none hs⟩

/-! ## Weakening at the END of the context (masks padded with `false`): a closed value types in every context. -/
theorem mask_empty_pad {Δ : List Bool} (k : Nat) (h : Mask.empty Δ) : Mask.empty (Δ ++ List.replicate k false) := by
  intro m hm
  by_cases hl : m < Δ.length
  · exact h m (by rw [List.getElem?_append_left hl] at hm; exact hm)
  · rw [List.getElem?_append_right (by omega), List.getElem?_replicate] at hm; split_ifs at hm <;> simp at hm

theorem get_pad {Δ : List Bool} {k n : Nat} (h : Δ[n]? = some true) : (Δ ++ List.replicate k false)[n]? = some true := by
  have hl : n < Δ.length := by
    rcases Nat.lt_or_ge n Δ.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  rw [List.getElem?_append_left hl]; exact h

theorem mask_only_pad {Δ : List Bool} {n : Nat} (k : Nat) (h : Mask.only Δ n) : Mask.only (Δ ++ List.replicate k false) n := by
  refine ⟨get_pad h.1, fun m hm hm' => ?_⟩
  by_cases hl : m < Δ.length
  · exact h.2 m hm (by rw [List.getElem?_append_left hl] at hm'; exact hm')
  · rw [List.getElem?_append_right (by omega), List.getElem?_replicate] at hm'; split_ifs at hm' <;> simp at hm'

theorem set_pad {Δ : List Bool} {k n : Nat} (h : Δ[n]? = some true) :
    (Δ ++ List.replicate k false).set n false = Δ.set n false ++ List.replicate k false := by
  have hl : n < Δ.length := by
    rcases Nat.lt_or_ge n Δ.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  rw [List.set_append_left _ _ hl]

theorem split_pad {Δ Δ₁ Δ₂ : List Bool} (k : Nat) (h : Split Δ Δ₁ Δ₂) :
    Split (Δ ++ List.replicate k false) (Δ₁ ++ List.replicate k false) (Δ₂ ++ List.replicate k false) := by
  induction h with
  | nil => induction k with
    | zero => exact .nil
    | succ k ih => exact .none ih
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | none _ ih => exact .none ih

mutual
theorem weakA₂ : ∀ {Γ a τ} (Γ' : Ctx S₂), HasTypeA₂ Γ a τ → HasTypeA₂ (Γ ++ Γ') a τ
  | _, _, _, _, .var h hc => .var (by
      have hl : _ < _ := (List.getElem?_eq_some_iff.1 h).1
      rw [List.getElem?_append_left hl]; exact h) hc
  | _, _, _, _, .int => .int
  | _, _, _, _, .bool => .bool
  | _, _, _, _, .unit => .unit
  | _, _, _, Γ', .prim h => .prim (weakL₂ Γ' h)
  | _, _, _, Γ', .lam h₁ h₂ hΔ hl h => .lam h₁ h₂ (mask_empty_pad Γ'.length hΔ) (by simp [hl]; omega) (weak₂ Γ' h)
  | _, _, _, Γ', .fix h₁ h₂ hΔ hl h => .fix h₁ h₂ (mask_empty_pad Γ'.length hΔ) (by simp [hl]; omega) (weak₂ Γ' h)
  | _, _, _, Γ', .pair h₁ h₂ => .pair (weakA₂ Γ' h₁) (weakA₂ Γ' h₂)
  | _, _, _, Γ', .fst h => .fst (weakA₂ Γ' h)
  | _, _, _, Γ', .snd h => .snd (weakA₂ Γ' h)
  | _, _, _, Γ', .inl hc h => .inl hc (weakA₂ Γ' h)
  | _, _, _, Γ', .inr hc h => .inr hc (weakA₂ Γ' h)
theorem weakL₂ : ∀ {Γ as τs} (Γ' : Ctx S₂), HasTypeL₂ Γ as τs → HasTypeL₂ (Γ ++ Γ') as τs
  | _, _, _, _, .nil => .nil
  | _, _, _, Γ', .cons h hs => .cons (weakA₂ Γ' h) (weakL₂ Γ' hs)
theorem weak₂ : ∀ {Γ Δ e τ} (Γ' : Ctx S₂), HasType₂ Γ Δ e τ →
    HasType₂ (Γ ++ Γ') (Δ ++ List.replicate Γ'.length false) e τ
  | _, _, _, _, Γ', .ret hΔ h => .ret (mask_empty_pad _ hΔ) (weakA₂ Γ' h)
  | _, _, _, _, Γ', .retCap hΓ hΔ => .retCap (by
      have hl : _ < _ := (List.getElem?_eq_some_iff.1 hΓ).1
      rw [List.getElem?_append_left hl]; exact hΓ) (mask_only_pad _ hΔ)
  | _, _, _, _, Γ', .letE hs hc h₁ h₂ => .letE (split_pad _ hs) hc (weak₂ Γ' h₁) (weak₂ Γ' h₂)
  | _, _, _, _, Γ', .alloc ha h => .alloc (weakA₂ Γ' ha) (weak₂ Γ' h)
  | _, _, _, _, Γ', .load hΓ hΔ ha h => .load (by
      have hl : _ < _ := (List.getElem?_eq_some_iff.1 hΓ).1
      rw [List.getElem?_append_left hl]; exact hΓ) (get_pad hΔ) (weakA₂ Γ' ha) (weak₂ Γ' h)
  | _, _, _, _, Γ', .store hΓ hΔ h₁ h₂ h => .store (by
      have hl : _ < _ := (List.getElem?_eq_some_iff.1 hΓ).1
      rw [List.getElem?_append_left hl]; exact hΓ) (get_pad hΔ) (weakA₂ Γ' h₁) (weakA₂ Γ' h₂)
      (by rw [set_pad hΔ]; exact weak₂ Γ' h)
  | _, _, _, _, Γ', .free hΓ hΔ h => .free (by
      have hl : _ < _ := (List.getElem?_eq_some_iff.1 hΓ).1
      rw [List.getElem?_append_left hl]; exact hΓ) (get_pad hΔ)
      (by rw [set_pad hΔ]; exact weak₂ Γ' h)
  | _, _, _, _, Γ', .app hΔ h₁ h₂ => .app (mask_empty_pad _ hΔ) (weakA₂ Γ' h₁) (weakA₂ Γ' h₂)
  | _, _, _, _, Γ', .ite h h₁ h₂ => .ite (weakA₂ Γ' h) (weak₂ Γ' h₁) (weak₂ Γ' h₂)
  | _, _, _, _, Γ', .case h h₁ h₂ => .case (weakA₂ Γ' h) (weak₂ Γ' h₁) (weak₂ Γ' h₂)
end

theorem closedA₂ {v : Atom₂} {τ} (Γ : Ctx S₂) (h : HasTypeA₂ [] v τ) : HasTypeA₂ Γ v τ := by
  simpa using weakA₂ Γ h

end VIRL2
