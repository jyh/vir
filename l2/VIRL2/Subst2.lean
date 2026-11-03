/-
  O95 layer L2, Lean arm. Y5 groundwork: the SUBSTITUTION LEMMA for ⊢₂ at depth k = Γ₁.length, at a position whose mask
  entry is `false`, for a value that is either a closed well-typed atom (the ordinary case) or anything at all when the
  position's type carries a capability (such a position is never mentioned by an atom, and a `false` mask forbids every O₂
  use of it, so any value may go there: this is the case of a λ body under a capability binder).
-/
import VIRL2.MaskLemmas
import VIRL2.SemBase

namespace VIRL2
open VIRL1

theorem subst_var_ne {n k : Nat} {v : Atom₂} (h : n ≠ k) : (Atom.var n : Atom₂).subst k v = .var (dropIdx k n) := by
  simp only [Atom.subst, dropIdx]; split_ifs <;> first | rfl | omega

theorem empty_rep {Δ : List Bool} (h : Mask.empty Δ) : Δ = List.replicate Δ.length false := by
  induction Δ with
  | nil => rfl
  | cons b Δ ih =>
    cases b with
    | true => exact absurd rfl (h 0)
    | false => simp only [List.length_cons, List.replicate_succ]; congr 1; exact ih (fun n hn => h (n + 1) (by simpa using hn))

theorem empty_split {Δ : List Bool} (h : Mask.empty Δ) (m r : Nat) (hl : Δ.length = m + 1 + r) :
    Δ = List.replicate m false ++ false :: List.replicate r false := by
  rw [empty_rep h, hl, show m + 1 + r = m + (r + 1) by omega, List.replicate_add]; rfl

theorem mask_empty_reps (a b : Nat) : Mask.empty (List.replicate a false ++ List.replicate b false) := by
  rw [← List.replicate_add]; intro m h; rw [List.getElem?_replicate] at h; split_ifs at h <;> simp at h

/-- What may be substituted at a position of type τ. -/
def Fits (v : Atom₂) (τ : Ty₂) : Prop := HasTypeA₂ [] v τ ∨ hasCap τ = true

mutual
theorem substA₂ : ∀ {Γ₁ Γ : Ctx S₂} {a τ τ' v}, HasTypeA₂ (Γ₁ ++ τ :: Γ) a τ' → Fits v τ →
    HasTypeA₂ (Γ₁ ++ Γ) (a.subst Γ₁.length v) τ'
  | Γ₁, Γ, .var n, τ, τ', v, .var h hc, hv => by
    by_cases hk : n = Γ₁.length
    · subst hk
      rw [List.getElem?_append_right (by omega)] at h; simp at h; subst h
      simp only [Atom.subst, Nat.lt_irrefl, if_false, if_true]
      rcases hv with hv | hv
      · exact closedA₂ _ hv
      · rw [hc] at hv; cases hv
    · rw [subst_var_ne hk]; exact .var (by rw [← get_drop hk]; exact h) hc
  | _, _, _, _, _, _, .int, _ => .int
  | _, _, _, _, _, _, .bool, _ => .bool
  | _, _, _, _, _, _, .unit, _ => .unit
  | _, _, .prim p as, _, _, _, .prim h, hv => .prim (substL₂ h hv)
  | Γ₁, Γ, .lam τ₁ e, _, _, _, .lam h₁ h₂ hΔ hl h, hv => by
    have hs := empty_split hΔ (Γ₁.length + 1) Γ.length (by simp at hl; omega)
    rw [hs] at h
    have := subst₂ (Γ₁ := τ₁ :: Γ₁) (Δ₁ := List.replicate (Γ₁.length + 1) false) (by simp) h hv
    exact .lam h₁ h₂ (mask_empty_reps _ _) (by simp; omega) this
  | Γ₁, Γ, .fix τ₁ τ₂ e, _, _, _, .fix h₁ h₂ hΔ hl h, hv => by
    have hs := empty_split hΔ (Γ₁.length + 2) Γ.length (by simp at hl; omega)
    rw [hs] at h
    have := subst₂ (Γ₁ := τ₁ :: .arr τ₁ τ₂ :: Γ₁) (Δ₁ := List.replicate (Γ₁.length + 2) false) (by simp) h hv
    simp only [List.length_cons, Nat.add_assoc] at this
    exact .fix h₁ h₂ (mask_empty_reps _ _) (by simp; omega) this
  | _, _, .pair a b, _, _, _, .pair h₁ h₂, hv => .pair (substA₂ h₁ hv) (substA₂ h₂ hv)
  | _, _, .fst a, _, _, _, .fst h, hv => .fst (substA₂ h hv)
  | _, _, .snd a, _, _, _, .snd h, hv => .snd (substA₂ h hv)
  | _, _, .inl _ a, _, _, _, .inl hc h, hv => .inl hc (substA₂ h hv)
  | _, _, .inr _ a, _, _, _, .inr hc h, hv => .inr hc (substA₂ h hv)
theorem substL₂ : ∀ {Γ₁ Γ : Ctx S₂} {as τ τs v}, HasTypeL₂ (Γ₁ ++ τ :: Γ) as τs → Fits v τ →
    HasTypeL₂ (Γ₁ ++ Γ) (Atom.substL Γ₁.length v as) τs
  | _, _, [], _, _, _, .nil, _ => .nil
  | _, _, _ :: _, _, _, _, .cons h hs, hv => .cons (substA₂ h hv) (substL₂ hs hv)
theorem subst₂ : ∀ {Γ₁ Γ : Ctx S₂} {Δ₁ Δ : List Bool} {e τ τ' v}, Δ₁.length = Γ₁.length →
    HasType₂ (Γ₁ ++ τ :: Γ) (Δ₁ ++ false :: Δ) e τ' → Fits v τ → HasType₂ (Γ₁ ++ Γ) (Δ₁ ++ Δ) (e.subst Γ₁.length v) τ'
  | _, _, _, _, .ret a, _, _, _, _, .ret hΔ h, hv => .ret (mask_empty_drop hΔ) (substA₂ h hv)
  | Γ₁, _, Δ₁, _, .ret (.var n), _, _, _, hl, .retCap hΓ hΔ, hv => by
    have hn := mask_true_ne hΔ.1
    rw [hl] at hn
    show HasType₂ _ _ (.ret ((Atom.var n).subst Γ₁.length _)) _
    rw [subst_var_ne hn]
    refine .retCap (by rw [← get_drop hn]; exact hΓ) ?_
    have := mask_only_drop hΔ; rwa [hl] at this
  | Γ₁, Γ, Δ₁, Δ, .letE τ₁ e₁ e₂, _, _, _, hl, .letE hs hc h₁ h₂, hv => by
    obtain ⟨A₁, A₂, B₁, B₂, rfl, rfl, hA, hB, hs'⟩ := split_mid hs
    refine .letE hs' hc (subst₂ (hA.trans hl) h₁ hv) ?_
    exact subst₂ (Γ₁ := τ₁ :: Γ₁) (Δ₁ := _ :: B₁) (by simp [hB, hl]) h₂ hv
  | Γ₁, Γ, Δ₁, Δ, .letOp .alloc [a] _ e, _, _, _, hl, .alloc ha h, hv =>
    .alloc (substA₂ ha hv) (subst₂ (Γ₁ := tcap :: Γ₁) (Δ₁ := true :: Δ₁) (by simp [hl]) h hv)
  | Γ₁, Γ, Δ₁, Δ, .letOp .load [.var n, a] _ e, _, _, _, hl, .load hΓ hΔ ha h, hv => by
    have hn := mask_true_ne hΔ; rw [hl] at hn
    show HasType₂ _ _ (.letOp .load [(Atom.var n).subst Γ₁.length _, _] _ _) _
    rw [subst_var_ne hn]
    refine .load (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop (hl ▸ hn)]; exact hΔ) (substA₂ ha hv) ?_
    exact subst₂ (Γ₁ := tint :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h hv
  | Γ₁, Γ, Δ₁, Δ, .letOp .store [.var n, a₁, a₂] _ e, _, _, _, hl, .store hΓ hΔ h₁ h₂ h, hv => by
    have hn := mask_true_ne hΔ; rw [hl] at hn
    have hn' : n ≠ Δ₁.length := hl ▸ hn
    show HasType₂ _ _ (.letOp .store [(Atom.var n).subst Γ₁.length _, _, _] _ _) _
    rw [subst_var_ne hn]
    refine .store (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ)
      (substA₂ h₁ hv) (substA₂ h₂ hv) ?_
    rw [set_mid hn'] at h
    have := subst₂ (Γ₁ := tcap :: Γ₁) (Δ₁ := true :: _) (by simp [List.length_set]; split_ifs <;> simp [hl]) h hv
    simp only [List.cons_append] at this
    rw [set_drop hn', hl] at this; exact this
  | Γ₁, Γ, Δ₁, Δ, .letOp .free [.var n] _ e, _, _, _, hl, .free hΓ hΔ h, hv => by
    have hn := mask_true_ne hΔ; rw [hl] at hn
    have hn' : n ≠ Δ₁.length := hl ▸ hn
    show HasType₂ _ _ (.letOp .free [(Atom.var n).subst Γ₁.length _] _ _) _
    rw [subst_var_ne hn]
    refine .free (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ) ?_
    rw [set_mid hn'] at h
    have := subst₂ (Γ₁ := tunit :: Γ₁) (Δ₁ := false :: _) (by simp [List.length_set]; split_ifs <;> simp [hl]) h hv
    simp only [List.cons_append] at this
    rw [set_drop hn', hl] at this; exact this
  | _, _, _, _, .app a b, _, _, _, _, .app hΔ h₁ h₂, hv => .app (mask_empty_drop hΔ) (substA₂ h₁ hv) (substA₂ h₂ hv)
  | _, _, _, _, .ite a e₁ e₂, _, _, _, hl, .ite h h₁ h₂, hv => .ite (substA₂ h hv) (subst₂ hl h₁ hv) (subst₂ hl h₂ hv)
  | Γ₁, Γ, Δ₁, Δ, .case a e₁ e₂, _, _, _, hl, .case h h₁ h₂, hv =>
    .case (substA₂ h hv) (subst₂ (Γ₁ := _ :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h₁ hv)
      (subst₂ (Γ₁ := _ :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h₂ hv)
end

end VIRL2
