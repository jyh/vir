/-
  O95 layer L5, Lean arm (amend-24 LV4 groundwork). The SUBSTITUTION LEMMA for ⊢₅ at depth Γ₁.length, at a `false` mask position,
  for a value that fits the position (L2's `subst₂`, restated; part of `L5.syntaxCopy`). The new cases: a λ/fix body under its k
  lent capabilities (the depth grows by k + 1, resp. k + 2), `letK`'s body under its j handed-back capabilities, and the capability
  lists of `retK`/`appK`, which never mention a `false` position and are re-indexed by `dropIdx` (`CapsExact.drop`).
-/
import VIRL5.Weak5
import VIRL2.Subst2

namespace VIRL5
open VIRL1 VIRL2

theorem subst_var_ne₅ {n k : Nat} {v : Atom₅} (h : n ≠ k) : (Atom₅.var n).subst k v = .var (dropIdx k n) := by
  simp only [Atom₅.subst, dropIdx]; split_ifs <;> first | rfl | omega

/-- What may be substituted at a position of type τ. -/
def Fits₅ (v : Atom₅) (τ : Ty₅) : Prop := HasTypeA₅ [] v τ ∨ τ.hasCap = true

/-- The inverse of `dropIdx k` away from k. -/
def liftIdx (k m : Nat) : Nat := if m < k then m else m + 1

theorem dropIdx_lift (k m : Nat) : dropIdx k (liftIdx k m) = m := by
  unfold dropIdx liftIdx; split_ifs <;> omega

theorem lift_ne (k m : Nat) : liftIdx k m ≠ k := by
  unfold liftIdx; split_ifs <;> omega

theorem dropIdx_inj {k a b : Nat} (ha : a ≠ k) (hb : b ≠ k) (h : dropIdx k a = dropIdx k b) : a = b := by
  unfold dropIdx at h; split_ifs at h <;> omega

theorem substL_vars {k : Nat} {v : Atom₅} : ∀ {ns : List Nat}, (∀ n ∈ ns, n ≠ k) →
    Atom₅.substL k v (ns.map Atom₅.var) = (ns.map (dropIdx k)).map Atom₅.var
  | [], _ => rfl
  | n :: ns, h => by
      simp only [List.map_cons, Atom₅.substL]
      rw [subst_var_ne₅ (h n (by simp)), substL_vars (fun m hm => h m (by simp [hm]))]

/-- A capability list at a `false` position: none of its variables is that position, and it re-indexes. -/
theorem CapsExact.drop {Γ₁ Γ : Ctx₅} {Δ₁ Δ : List Bool} {τ : Ty₅} {ns : List Nat} (hl : Δ₁.length = Γ₁.length)
    (h : CapsExact (Γ₁ ++ τ :: Γ) (Δ₁ ++ false :: Δ) ns) :
    (∀ n ∈ ns, n ≠ Γ₁.length) ∧ CapsExact (Γ₁ ++ Γ) (Δ₁ ++ Δ) (ns.map (dropIdx Γ₁.length)) := by
  obtain ⟨hnd, hΓ, hΔ⟩ := h
  have hne : ∀ n ∈ ns, n ≠ Γ₁.length := fun n hn => hl ▸ mask_true_ne ((hΔ n).2 hn)
  refine ⟨hne, ?_, ?_, ?_⟩
  · exact hnd.map_on (fun a ha b hb hab => dropIdx_inj (hne a ha) (hne b hb) hab)
  · intro m hm
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hm
    rw [← get_drop (hne n hn)]; exact hΓ n hn
  · intro m
    constructor
    · intro hm
      have h₁ : (Δ₁ ++ false :: Δ)[liftIdx Γ₁.length m]? = some true := by
        rw [get_drop (hl ▸ lift_ne _ m), hl, dropIdx_lift]; exact hm
      exact List.mem_map.2 ⟨_, (hΔ _).1 h₁, dropIdx_lift _ _⟩
    · intro hm
      obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hm
      have := (hΔ n).2 hn
      rw [get_drop (hl ▸ hne n hn), hl] at this; exact this

mutual
theorem substA₅ : ∀ {Γ₁ Γ : Ctx₅} {a τ τ' v}, HasTypeA₅ (Γ₁ ++ τ :: Γ) a τ' → Fits₅ v τ →
    HasTypeA₅ (Γ₁ ++ Γ) (a.subst Γ₁.length v) τ'
  | Γ₁, Γ, .var n, τ, τ', v, .var h hc, hv => by
    by_cases hk : n = Γ₁.length
    · subst hk
      rw [List.getElem?_append_right (by omega)] at h; simp at h; subst h
      simp only [Atom₅.subst, Nat.lt_irrefl, if_false, if_true]
      rcases hv with hv | hv
      · exact closedA₅ _ hv
      · rw [hc] at hv; cases hv
    · rw [subst_var_ne₅ hk]; exact .var (by rw [← get_drop hk]; exact h) hc
  | _, _, _, _, _, _, .int, _ => .int
  | _, _, _, _, _, _, .bool, _ => .bool
  | _, _, _, _, _, _, .unit, _ => .unit
  | _, _, .prim p as, _, _, _, .prim h, hv => .prim (substL₅ h hv)
  | Γ₁, Γ, .lam τ₁ j e, x, _, _, .lam (τ₂ := τ₂) h₁ h₂ hΔ hl h, hv => by
    simp only [List.length_append, List.length_cons] at hl
    have hs := empty_split hΔ (Γ₁.length + 1) Γ.length (by omega)
    rw [hs] at h
    have h' : HasType₅ ((List.replicate j t5cap ++ τ₁ :: Γ₁) ++ x :: Γ)
        ((List.replicate j true ++ List.replicate (Γ₁.length + 1) false) ++ false :: List.replicate Γ.length false) e τ₂ j := by
      simpa [List.append_assoc] using h
    have := subst₅ (by simp) h' hv
    have hlen : (List.replicate j t5cap ++ τ₁ :: Γ₁).length = Γ₁.length + j + 1 := by simp; omega
    rw [hlen] at this
    show HasTypeA₅ _ (.lam τ₁ j (e.subst (Γ₁.length + j + 1) _)) _
    refine .lam (Δ₀ := List.replicate (Γ₁.length + 1) false ++ List.replicate Γ.length false) h₁ h₂
      (mask_empty_reps _ _) (by simp; omega) ?_
    simpa [List.append_assoc] using this
  | Γ₁, Γ, .fix τ₁ j τ₂ e, x, _, _, .fix h₁ h₂ hΔ hl h, hv => by
    simp only [List.length_append, List.length_cons] at hl
    have hs := empty_split hΔ (Γ₁.length + 2) Γ.length (by omega)
    rw [hs] at h
    have h' : HasType₅ ((List.replicate j t5cap ++ τ₁ :: Ty₅.arr τ₁ j τ₂ :: Γ₁) ++ x :: Γ)
        ((List.replicate j true ++ List.replicate (Γ₁.length + 2) false) ++ false :: List.replicate Γ.length false) e τ₂ j := by
      simpa [List.append_assoc] using h
    have := subst₅ (by simp) h' hv
    have hlen : (List.replicate j t5cap ++ τ₁ :: Ty₅.arr τ₁ j τ₂ :: Γ₁).length = Γ₁.length + j + 2 := by simp; omega
    rw [hlen] at this
    show HasTypeA₅ _ (.fix τ₁ j τ₂ (e.subst (Γ₁.length + j + 2) _)) _
    refine .fix (Δ₀ := List.replicate (Γ₁.length + 2) false ++ List.replicate Γ.length false) h₁ h₂
      (mask_empty_reps _ _) (by simp; omega) ?_
    simpa [List.append_assoc] using this
  | _, _, .pair a b, _, _, _, .pair h₁ h₂, hv => .pair (substA₅ h₁ hv) (substA₅ h₂ hv)
  | _, _, .fst a, _, _, _, .fst h, hv => .fst (substA₅ h hv)
  | _, _, .snd a, _, _, _, .snd h, hv => .snd (substA₅ h hv)
  | _, _, .inl _ a, _, _, _, .inl hc h, hv => .inl hc (substA₅ h hv)
  | _, _, .inr _ a, _, _, _, .inr hc h, hv => .inr hc (substA₅ h hv)
theorem substL₅ : ∀ {Γ₁ Γ : Ctx₅} {as τ τs v}, HasTypeL₅ (Γ₁ ++ τ :: Γ) as τs → Fits₅ v τ →
    HasTypeL₅ (Γ₁ ++ Γ) (Atom₅.substL Γ₁.length v as) τs
  | _, _, [], _, _, _, .nil, _ => .nil
  | _, _, _ :: _, _, _, _, .cons h hs, hv => .cons (substA₅ h hv) (substL₅ hs hv)
theorem subst₅ : ∀ {Γ₁ Γ : Ctx₅} {Δ₁ Δ : List Bool} {e τ τ' k v}, Δ₁.length = Γ₁.length →
    HasType₅ (Γ₁ ++ τ :: Γ) (Δ₁ ++ false :: Δ) e τ' k → Fits₅ v τ →
    HasType₅ (Γ₁ ++ Γ) (Δ₁ ++ Δ) (e.subst Γ₁.length v) τ' k
  | _, _, _, _, .ret a, _, _, _, _, _, .ret hΔ h, hv => .ret (mask_empty_drop hΔ) (substA₅ h hv)
  | Γ₁, _, Δ₁, _, .ret (.var n), _, _, _, _, hl, .retCap hΓ hΔ, hv => by
    have hn := mask_true_ne hΔ.1
    rw [hl] at hn
    show HasType₅ _ _ (.ret ((Atom₅.var n).subst Γ₁.length _)) _ _
    rw [subst_var_ne₅ hn]
    refine .retCap (by rw [← get_drop hn]; exact hΓ) ?_
    have := mask_only_drop hΔ; rwa [hl] at this
  | Γ₁, Γ, Δ₁, Δ, .letE τ₁ e₁ e₂, _, _, _, _, hl, .letE hs hc h₁ h₂, hv => by
    obtain ⟨A₁, A₂, B₁, B₂, rfl, rfl, hA, hB, hs'⟩ := split_mid hs
    refine .letE hs' hc (subst₅ (hA.trans hl) h₁ hv) ?_
    exact subst₅ (Γ₁ := τ₁ :: Γ₁) (Δ₁ := _ :: B₁) (by simp [hB, hl]) h₂ hv
  | Γ₁, Γ, Δ₁, Δ, .letOp .alloc [a] _ e, _, _, _, _, hl, .alloc ha h, hv =>
    .alloc (substA₅ ha hv) (subst₅ (Γ₁ := t5cap :: Γ₁) (Δ₁ := true :: Δ₁) (by simp [hl]) h hv)
  | Γ₁, Γ, Δ₁, Δ, .letOp .load [.var n, a] _ e, _, _, _, _, hl, .load hΓ hΔ ha h, hv => by
    have hn := mask_true_ne hΔ; rw [hl] at hn
    show HasType₅ _ _ (.letOp .load [(Atom₅.var n).subst Γ₁.length _, _] _ _) _ _
    rw [subst_var_ne₅ hn]
    refine .load (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop (hl ▸ hn)]; exact hΔ) (substA₅ ha hv) ?_
    exact subst₅ (Γ₁ := t5int :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h hv
  | Γ₁, Γ, Δ₁, Δ, .letOp .store [.var n, a₁, a₂] _ e, _, _, _, _, hl, .store hΓ hΔ h₁ h₂ h, hv => by
    have hn := mask_true_ne hΔ; rw [hl] at hn
    have hn' : n ≠ Δ₁.length := hl ▸ hn
    show HasType₅ _ _ (.letOp .store [(Atom₅.var n).subst Γ₁.length _, _, _] _ _) _ _
    rw [subst_var_ne₅ hn]
    refine .store (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ)
      (substA₅ h₁ hv) (substA₅ h₂ hv) ?_
    rw [set_mid hn'] at h
    have := subst₅ (Γ₁ := t5cap :: Γ₁) (Δ₁ := true :: _) (by simp [List.length_set]; split_ifs <;> simp [hl]) h hv
    simp only [List.cons_append] at this
    rw [set_drop hn', hl] at this; exact this
  | Γ₁, Γ, Δ₁, Δ, .letOp .free [.var n] _ e, _, _, _, _, hl, .free hΓ hΔ h, hv => by
    have hn := mask_true_ne hΔ; rw [hl] at hn
    have hn' : n ≠ Δ₁.length := hl ▸ hn
    show HasType₅ _ _ (.letOp .free [(Atom₅.var n).subst Γ₁.length _] _ _) _ _
    rw [subst_var_ne₅ hn]
    refine .free (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ) ?_
    rw [set_mid hn'] at h
    have := subst₅ (Γ₁ := t5unit :: Γ₁) (Δ₁ := false :: _) (by simp [List.length_set]; split_ifs <;> simp [hl]) h hv
    simp only [List.cons_append] at this
    rw [set_drop hn', hl] at this; exact this
  | _, _, _, _, .app a b, _, _, _, _, _, .app hΔ h₁ h₂, hv => .app (mask_empty_drop hΔ) (substA₅ h₁ hv) (substA₅ h₂ hv)
  | _, _, _, _, .ite a e₁ e₂, _, _, _, _, hl, .ite h h₁ h₂, hv => .ite (substA₅ h hv) (subst₅ hl h₁ hv) (subst₅ hl h₂ hv)
  | Γ₁, Γ, Δ₁, Δ, .case a e₁ e₂, _, _, _, _, hl, .case h h₁ h₂, hv =>
    .case (substA₅ h hv) (subst₅ (Γ₁ := _ :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h₁ hv)
      (subst₅ (Γ₁ := _ :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h₂ hv)
  | Γ₁, Γ, Δ₁, Δ, .retK a _, _, _, _, _, hl, .retK (ns := ns) hc h hx, hv => by
    obtain ⟨hne, hx'⟩ := CapsExact.drop hl hx
    show HasType₅ _ _ (.retK (a.subst Γ₁.length _) (Atom₅.substL Γ₁.length _ (ns.map Atom₅.var))) _ _
    rw [substL_vars hne]
    have := HasType₅.retK hc (substA₅ h hv) hx'
    rwa [List.length_map] at this
  | Γ₁, Γ, Δ₁, Δ, .appK a₁ a₂ _, _, _, _, _, hl, .appK (ns := ns) h₁ h₂ hx, hv => by
    obtain ⟨hne, hx'⟩ := CapsExact.drop hl hx
    show HasType₅ _ _ (.appK (a₁.subst Γ₁.length _) (a₂.subst Γ₁.length _) (Atom₅.substL Γ₁.length _ (ns.map Atom₅.var))) _ _
    rw [substL_vars hne]
    have h₁' := substA₅ h₁ hv
    rw [← List.length_map (f := dropIdx Γ₁.length)] at h₁'
    have := HasType₅.appK h₁' (substA₅ h₂ hv) hx'
    rwa [List.length_map] at this
  | Γ₁, Γ, Δ₁, Δ, .letK τ₁ j e₁ e₂, x, _, _, _, hl, .letK (τ₂ := σ₂) (k := kk) hs hc h₁ h₂, hv => by
    obtain ⟨A₁, A₂, B₁, B₂, rfl, rfl, hA, hB, hs'⟩ := split_mid hs
    refine .letK hs' hc (subst₅ (hA.trans hl) h₁ hv) ?_
    have h' : HasType₅ ((List.replicate j t5cap ++ τ₁ :: Γ₁) ++ x :: Γ)
        ((List.replicate j true ++ false :: B₁) ++ false :: B₂) e₂ σ₂ kk := by
      simpa [List.append_assoc] using h₂
    have := subst₅ (by simp [hB, hl]) h' hv
    have hlen : (List.replicate j t5cap ++ τ₁ :: Γ₁).length = Γ₁.length + j + 1 := by simp; omega
    rw [hlen] at this
    simpa [List.append_assoc] using this
end

end VIRL5
