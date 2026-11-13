/-
  O95 layer L5, Lean arm (amend-24 LV4). Substitution into RUNTIME-typed terms (L2's RTSubst.lean, restated for RT₅; the L2 cases
  are ported text, part of `L5.syntaxCopy`). `RT₅.substV`: a value at a `false` position, Ω unchanged. `RT₅.substC`: ⟨p⟩ at a TRUE
  position, Ω grows by p. The new cases are the L1′ rules: a capability list re-indexes (`substL_capsV`), and at a TRUE position its
  one variable at that position becomes ⟨p⟩, moving from Δ's account to Ω's (`substL_capsC`, `CapsExact.dropAt`).
-/
import VIRL5.Runtime5
import VIRL2.RTSubst

namespace VIRL5
open VIRL1 VIRL2

theorem substL_length {k : Nat} {v : Atom₅} : ∀ ds : List Atom₅, (Atom₅.substL k v ds).length = ds.length
  | [] => rfl
  | _ :: ds => by simp [Atom₅.substL, substL_length ds]

theorem subst_var_self₅ {k : Nat} {v : Atom₅} : (Atom₅.var k).subst k v = v := by simp [Atom₅.subst]

theorem fits_cap₅ (p : Int) : Fits₅ (.const (.cap p)) t5cap := .inr rfl

theorem capVars_sub (d : Atom₅) (ds : List Atom₅) {n : Nat} (h : n ∈ capVars ds) : n ∈ capVars (d :: ds) := by
  cases d <;> simp [capVars, h]

/-- A capability list at a position none of its variables is: it re-indexes, its constants stay. -/
theorem substL_capsV {k : Nat} {v : Atom₅} : ∀ {ds : List Atom₅}, (∀ d ∈ ds, CapForm d) → (∀ n ∈ capVars ds, n ≠ k) →
    capVars (Atom₅.substL k v ds) = (capVars ds).map (dropIdx k) ∧ capPtrs (Atom₅.substL k v ds) = capPtrs ds ∧
      ∀ d ∈ Atom₅.substL k v ds, CapForm d
  | [], _, _ => ⟨rfl, rfl, by simp [Atom₅.substL]⟩
  | d :: ds, hf, hne => by
      have ih := substL_capsV (k := k) (v := v) (ds := ds) (fun d hd => hf d (by simp [hd]))
        (fun n hn => hne n (capVars_sub d ds hn))
      rcases hf d (by simp) with ⟨n, rfl⟩ | ⟨p, rfl⟩
      · have hn : n ≠ k := hne n (by simp [capVars])
        simp only [Atom₅.substL, subst_var_ne₅ hn, capVars, capPtrs, List.map_cons, ih.1, ih.2.1, true_and]
        intro d hd; simp at hd; rcases hd with rfl | hd
        · exact .inl ⟨_, rfl⟩
        · exact ih.2.2 d hd
      · simp only [Atom₅.substL, Atom₅.subst, capVars, capPtrs, ih.1, ih.2.1, true_and]
        intro d hd; simp at hd; rcases hd with rfl | hd
        · exact .inr ⟨_, rfl⟩
        · exact ih.2.2 d hd

/-- A capability list at the position of ONE of its variables (its variables distinct): that variable becomes ⟨p⟩. -/
theorem substL_capsC {k : Nat} {p : Int} : ∀ {ds : List Atom₅}, (∀ d ∈ ds, CapForm d) → k ∈ capVars ds →
    (capVars ds).Nodup →
    capVars (Atom₅.substL k (.const (.cap p)) ds) = ((capVars ds).erase k).map (dropIdx k) ∧
      (capPtrs (Atom₅.substL k (.const (.cap p)) ds)).Perm (p :: capPtrs ds) ∧
      ∀ d ∈ Atom₅.substL k (.const (.cap p)) ds, CapForm d
  | [], _, hk, _ => by simp [capVars] at hk
  | d :: ds, hf, hk, hnd => by
      have hf' : ∀ d ∈ ds, CapForm d := fun d hd => hf d (by simp [hd])
      rcases hf d (by simp) with ⟨n, rfl⟩ | ⟨q, rfl⟩
      · simp only [capVars, List.nodup_cons] at hnd hk
        by_cases hn : n = k
        · subst hn
          have hV := substL_capsV (k := n) (v := .const (.cap p)) hf' (fun m hm h => hnd.1 (h ▸ hm))
          simp only [Atom₅.substL, subst_var_self₅, capVars, capPtrs, List.erase_cons_head, hV.1, hV.2.1]
          refine ⟨by first | rfl | trivial, .refl _, ?_⟩
          intro d hd; simp at hd; rcases hd with rfl | hd
          · exact .inr ⟨_, rfl⟩
          · exact hV.2.2 d hd
        · have hk' : k ∈ capVars ds := by
            rcases List.mem_cons.1 hk with h | h
            · exact absurd h.symm hn
            · exact h
          have ih := substL_capsC (p := p) hf' hk' hnd.2
          have he : (n :: capVars ds).erase k = n :: (capVars ds).erase k := List.erase_cons_tail (by simp [hn])
          simp only [Atom₅.substL, subst_var_ne₅ hn, capVars, capPtrs, he, List.map_cons, ih.1]
          refine ⟨by first | rfl | trivial, ih.2.1, ?_⟩
          intro d hd; simp at hd; rcases hd with rfl | hd
          · exact .inl ⟨_, rfl⟩
          · exact ih.2.2 d hd
      · simp only [capVars] at hk hnd
        have ih := substL_capsC (p := p) hf' hk hnd
        simp only [Atom₅.substL, Atom₅.subst, capVars, capPtrs, ih.1]
        refine ⟨by first | rfl | trivial, (ih.2.1.cons q).trans (.swap _ _ _), ?_⟩
        intro d hd; simp at hd; rcases hd with rfl | hd
        · exact .inr ⟨_, rfl⟩
        · exact ih.2.2 d hd

/-- `CapsExact` across the removal of one position (any mask entry b there): the list loses that position and re-indexes. -/
theorem CapsExact.dropAt {Γ₁ Γ : Ctx₅} {Δ₁ Δ : List Bool} {τ : Ty₅} {b : Bool} {ns : List Nat} (hl : Δ₁.length = Γ₁.length)
    (h : CapsExact (Γ₁ ++ τ :: Γ) (Δ₁ ++ b :: Δ) ns) :
    CapsExact (Γ₁ ++ Γ) (Δ₁ ++ Δ) ((ns.erase Γ₁.length).map (dropIdx Γ₁.length)) := by
  obtain ⟨hnd, hΓ, hΔ⟩ := h
  have hmem : ∀ n, n ∈ ns.erase Γ₁.length ↔ n ≠ Γ₁.length ∧ n ∈ ns := fun n => hnd.mem_erase_iff
  refine ⟨?_, ?_, ?_⟩
  · exact (hnd.erase _).map_on (fun a ha b hb hab => dropIdx_inj ((hmem a).1 ha).1 ((hmem b).1 hb).1 hab)
  · intro m hm
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hm
    obtain ⟨hne, hn⟩ := (hmem n).1 hn
    rw [← get_drop hne]; exact hΓ n hn
  · intro m
    have hlift : (Δ₁ ++ b :: Δ)[liftIdx Γ₁.length m]? = (Δ₁ ++ Δ)[m]? := by
      rw [get_drop (hl ▸ lift_ne _ m), hl, dropIdx_lift]
    constructor
    · intro hm
      rw [← hlift] at hm
      exact List.mem_map.2 ⟨_, (hmem _).2 ⟨lift_ne _ m, (hΔ _).1 hm⟩, dropIdx_lift _ _⟩
    · intro hm
      obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hm
      obtain ⟨hne, hn⟩ := (hmem n).1 hn
      have := (hΔ n).2 hn
      rw [get_drop (hl ▸ hne), hl] at this; exact this

theorem CapsRT.substV {Γ₁ Γ : Ctx₅} {Δ₁ Δ : List Bool} {τ : Ty₅} {Ω : List Int} {ds : List Atom₅} {v : Atom₅}
    (hl : Δ₁.length = Γ₁.length) (h : CapsRT (Γ₁ ++ τ :: Γ) (Δ₁ ++ false :: Δ) Ω ds) :
    CapsRT (Γ₁ ++ Γ) (Δ₁ ++ Δ) Ω (Atom₅.substL Γ₁.length v ds) := by
  obtain ⟨hf, hx, hp⟩ := h
  obtain ⟨hne, hx'⟩ := CapsExact.drop hl hx
  have hs := substL_capsV (v := v) hf hne
  exact ⟨hs.2.2, by rw [hs.1]; exact hx', by rw [hs.2.1]; exact hp⟩

theorem CapsRT.substC {Γ₁ Γ : Ctx₅} {Δ₁ Δ : List Bool} {Ω : List Int} {ds : List Atom₅} (p : Int)
    (hl : Δ₁.length = Γ₁.length) (h : CapsRT (Γ₁ ++ t5cap :: Γ) (Δ₁ ++ true :: Δ) Ω ds) :
    CapsRT (Γ₁ ++ Γ) (Δ₁ ++ Δ) (p :: Ω) (Atom₅.substL Γ₁.length (.const (.cap p)) ds) := by
  obtain ⟨hf, hx, hp⟩ := h
  have hk : Γ₁.length ∈ capVars ds := (hx.2.2 Γ₁.length).1 (by rw [← hl]; simp)
  have hs := substL_capsC (p := p) hf hk hx.1
  exact ⟨hs.2.2, by rw [hs.1]; exact CapsExact.dropAt hl hx, (hp.cons p).trans hs.2.1.symm⟩

theorem RT₅.substV : ∀ {k : Nat} {Γ₁ Γ : Ctx₅} {Δ₁ Δ : List Bool} {Ω e τ τ' v}, Δ₁.length = Γ₁.length →
    RT₅ (Γ₁ ++ τ :: Γ) (Δ₁ ++ false :: Δ) Ω e τ' k → Fits₅ v τ → RT₅ (Γ₁ ++ Γ) (Δ₁ ++ Δ) Ω (e.subst Γ₁.length v) τ' k
  | _, _, _, _, _, _, .ret a, _, _, _, _, .ret hΔ h, hv => .ret (mask_empty_drop hΔ) (substA₅ h hv)
  | _, Γ₁, _, Δ₁, _, _, .ret (.var n), _, _, _, hl, .retCap hΓ hΔ, hv => by
    have hn := mask_true_ne hΔ.1
    rw [hl] at hn
    show RT₅ _ _ _ (.ret ((Atom₅.var n).subst Γ₁.length _)) _ _
    rw [subst_var_ne₅ hn]
    refine .retCap (by rw [← get_drop hn]; exact hΓ) ?_
    have := mask_only_drop hΔ; rwa [hl] at this
  | _, _, _, _, _, _, .ret (.const (.cap p)), _, _, _, _, .retCapC hΔ, _ => .retCapC (mask_empty_drop hΔ)
  | _, Γ₁, Γ, Δ₁, Δ, _, .letE τ₁ e₁ e₂, _, _, _, hl, .letE hs hp hc h₁ h₂, hv => by
    obtain ⟨A₁, A₂, B₁, B₂, rfl, rfl, hA, hB, hs'⟩ := split_mid hs
    refine .letE hs' hp hc (RT₅.substV (hA.trans hl) h₁ hv) ?_
    exact RT₅.substV (Γ₁ := τ₁ :: Γ₁) (Δ₁ := _ :: B₁) (by simp [hB, hl]) h₂ hv
  | _, Γ₁, Γ, Δ₁, Δ, _, .letOp .alloc [a] _ e, _, _, _, hl, .alloc ha h, hv =>
    .alloc (substA₅ ha hv) (RT₅.substV (Γ₁ := t5cap :: Γ₁) (Δ₁ := true :: Δ₁) (by simp [hl]) h hv)
  | _, Γ₁, Γ, Δ₁, Δ, _, .letOp .load [.var n, a] _ e, _, _, _, hl, .load hΓ hΔ ha h, hv => by
    have hn := mask_true_ne hΔ; rw [hl] at hn
    show RT₅ _ _ _ (.letOp .load [(Atom₅.var n).subst Γ₁.length _, _] _ _) _ _
    rw [subst_var_ne₅ hn]
    refine .load (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop (hl ▸ hn)]; exact hΔ) (substA₅ ha hv) ?_
    exact RT₅.substV (Γ₁ := t5int :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h hv
  | _, Γ₁, Γ, Δ₁, Δ, _, .letOp .load [.const (.cap p), a] _ e, _, _, _, hl, .loadC hp ha h, hv =>
    .loadC hp (substA₅ ha hv) (RT₅.substV (Γ₁ := t5int :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h hv)
  | _, Γ₁, Γ, Δ₁, Δ, _, .letOp .store [.var n, a₁, a₂] _ e, _, _, _, hl, .store hΓ hΔ h₁ h₂ h, hv => by
    have hn := mask_true_ne hΔ; rw [hl] at hn
    have hn' : n ≠ Δ₁.length := hl ▸ hn
    show RT₅ _ _ _ (.letOp .store [(Atom₅.var n).subst Γ₁.length _, _, _] _ _) _ _
    rw [subst_var_ne₅ hn]
    refine .store (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ)
      (substA₅ h₁ hv) (substA₅ h₂ hv) ?_
    rw [set_mid hn'] at h
    have := RT₅.substV (Γ₁ := t5cap :: Γ₁) (Δ₁ := true :: _) (by simp [List.length_set]; split_ifs <;> simp [hl]) h hv
    simp only [List.cons_append] at this
    rw [set_drop hn', hl] at this; exact this
  | _, Γ₁, Γ, Δ₁, Δ, _, .letOp .store [.const (.cap p), a₁, a₂] _ e, _, _, _, hl, .storeC hp h₁ h₂ h, hv =>
    .storeC hp (substA₅ h₁ hv) (substA₅ h₂ hv) (RT₅.substV (Γ₁ := t5cap :: Γ₁) (Δ₁ := true :: Δ₁) (by simp [hl]) h hv)
  | _, Γ₁, Γ, Δ₁, Δ, _, .letOp .free [.var n] _ e, _, _, _, hl, .free hΓ hΔ h, hv => by
    have hn := mask_true_ne hΔ; rw [hl] at hn
    have hn' : n ≠ Δ₁.length := hl ▸ hn
    show RT₅ _ _ _ (.letOp .free [(Atom₅.var n).subst Γ₁.length _] _ _) _ _
    rw [subst_var_ne₅ hn]
    refine .free (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ) ?_
    rw [set_mid hn'] at h
    have := RT₅.substV (Γ₁ := t5unit :: Γ₁) (Δ₁ := false :: _) (by simp [List.length_set]; split_ifs <;> simp [hl]) h hv
    simp only [List.cons_append] at this
    rw [set_drop hn', hl] at this; exact this
  | _, Γ₁, Γ, Δ₁, Δ, _, .letOp .free [.const (.cap p)] _ e, _, _, _, hl, .freeC hp h, hv =>
    .freeC hp (RT₅.substV (Γ₁ := t5unit :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h hv)
  | _, _, _, _, _, _, .app a b, _, _, _, _, .app hΔ h₁ h₂, hv => .app (mask_empty_drop hΔ) (substA₅ h₁ hv) (substA₅ h₂ hv)
  | _, _, _, _, _, _, .ite a e₁ e₂, _, _, _, hl, .ite h h₁ h₂, hv =>
    .ite (substA₅ h hv) (RT₅.substV hl h₁ hv) (RT₅.substV hl h₂ hv)
  | _, Γ₁, Γ, Δ₁, Δ, _, .case a e₁ e₂, _, _, _, hl, .case h h₁ h₂, hv =>
    .case (substA₅ h hv) (RT₅.substV (Γ₁ := _ :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h₁ hv)
      (RT₅.substV (Γ₁ := _ :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h₂ hv)

  | _, Γ₁, Γ, Δ₁, Δ, _, .retK a ds, _, _, v, hl, .retK hc h hx, hv => by
    show RT₅ _ _ _ (.retK (a.subst Γ₁.length v) (Atom₅.substL Γ₁.length v ds)) _ _
    have := RT₅.retK hc (substA₅ h hv) (CapsRT.substV (v := v) hl hx)
    rwa [substL_length] at this
  | _, Γ₁, Γ, Δ₁, Δ, _, .appK a₁ a₂ ds, _, _, v, hl, .appK h₁ h₂ hx, hv => by
    show RT₅ _ _ _ (.appK (a₁.subst Γ₁.length v) (a₂.subst Γ₁.length v) (Atom₅.substL Γ₁.length v ds)) _ _
    have h₁' := substA₅ h₁ hv
    rw [← substL_length (k := Γ₁.length) (v := v) ds] at h₁'
    have := RT₅.appK h₁' (substA₅ h₂ hv) (CapsRT.substV (v := v) hl hx)
    rwa [substL_length] at this
  | _, Γ₁, Γ, Δ₁, Δ, _, .letK τ₁ j e₁ e₂, x, _, _, hl, .letK (Ω₂ := Ω₂) (τ₂ := σ₂) (k := kk) hs hp hc h₁ h₂, hv => by
    obtain ⟨A₁, A₂, B₁, B₂, rfl, rfl, hA, hB, hs'⟩ := split_mid hs
    refine .letK hs' hp hc (RT₅.substV (hA.trans hl) h₁ hv) ?_
    have h' : RT₅ ((List.replicate j t5cap ++ τ₁ :: Γ₁) ++ x :: Γ)
        ((List.replicate j true ++ false :: B₁) ++ false :: B₂) Ω₂ e₂ σ₂ kk := by
      simpa [List.append_assoc] using h₂
    have := RT₅.substV (by simp [hB, hl]) h' hv
    have hlen : (List.replicate j t5cap ++ τ₁ :: Γ₁).length = Γ₁.length + j + 1 := by simp; omega
    rw [hlen] at this
    simpa [List.append_assoc] using this


/-- `RT₅.substC`: ⟨p⟩ at a TRUE mask position (a capability variable the term owns): the term now owns p. -/
theorem RT₅.substC : ∀ {k : Nat} {Γ₁ Γ : Ctx₅} {Δ₁ Δ : List Bool} {Ω e τ'} (p : Int), Δ₁.length = Γ₁.length →
    RT₅ (Γ₁ ++ t5cap :: Γ) (Δ₁ ++ true :: Δ) Ω e τ' k → RT₅ (Γ₁ ++ Γ) (Δ₁ ++ Δ) (p :: Ω) (e.subst Γ₁.length (.const (.cap p))) τ' k
  | _, _, _, _, _, _, _, _, _, _, .ret hΔ _ => (mask_empty_true hΔ).elim
  | _, Γ₁, _, Δ₁, _, _, .ret (.var n), _, p, hl, .retCap _ hΔ => by
    have hn := mask_only_true hΔ; subst hn
    show RT₅ _ _ _ (.ret ((Atom₅.var Δ₁.length).subst Γ₁.length _)) _ _
    rw [hl, subst_var_self₅]; exact .retCapC (mask_only_self (hl ▸ hΔ))
  | _, _, _, _, _, _, _, _, _, _, .retCapC hΔ => (mask_empty_true hΔ).elim
  | _, Γ₁, Γ, Δ₁, Δ, Ω, .letE τ₁ e₁ e₂, _, p, hl, .letE hs hp hc h₁ h₂ => by
    obtain ⟨A₁, A₂, B₁, B₂, a, rfl, rfl, hA, hB, hs'⟩ := split_mid_true hs
    cases a with
    | true =>
      refine .letE hs' (hp.cons p) hc (RT₅.substC p (hA.trans hl) h₁) ?_
      exact RT₅.substV (Γ₁ := τ₁ :: Γ₁) (Δ₁ := _ :: B₁) (by simp [hB, hl]) h₂ (fits_cap₅ p)
    | false =>
      refine .letE hs' ((hp.cons p).trans List.perm_middle.symm) hc (RT₅.substV (hA.trans hl) h₁ (fits_cap₅ p)) ?_
      exact RT₅.substC (Γ₁ := τ₁ :: Γ₁) (Δ₁ := _ :: B₁) p (by simp [hB, hl]) h₂
  | _, Γ₁, Γ, Δ₁, Δ, _, .letOp .alloc [a] _ e, _, p, hl, .alloc ha h =>
    .alloc (substA₅ ha (fits_cap₅ p)) (RT₅.substC (Γ₁ := t5cap :: Γ₁) (Δ₁ := true :: Δ₁) p (by simp [hl]) h)
  | _, Γ₁, Γ, Δ₁, Δ, _, .letOp .load [.var n, a] _ e, _, p, hl, .load hΓ hΔ ha h => by
    by_cases hn : n = Γ₁.length
    · subst hn
      show RT₅ _ _ _ (.letOp .load [(Atom₅.var Γ₁.length).subst Γ₁.length _, _] _ _) _ _
      rw [subst_var_self₅]
      exact .loadC (List.mem_cons_self) (substA₅ ha (fits_cap₅ p))
        (RT₅.substC (Γ₁ := t5int :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h)
    · show RT₅ _ _ _ (.letOp .load [(Atom₅.var n).subst Γ₁.length _, _] _ _) _ _
      rw [subst_var_ne₅ hn]
      refine .load (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop (hl ▸ hn)]; exact hΔ)
        (substA₅ ha (fits_cap₅ p)) ?_
      exact RT₅.substC (Γ₁ := t5int :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h
  | _, Γ₁, Γ, Δ₁, Δ, _, .letOp .load [.const (.cap q), a] _ e, _, p, hl, .loadC hq ha h =>
    .loadC (List.mem_cons_of_mem _ hq) (substA₅ ha (fits_cap₅ p))
      (RT₅.substC (Γ₁ := t5int :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h)
  | _, Γ₁, Γ, Δ₁, Δ, Ω, .letOp .store [.var n, a₁, a₂] _ e, _, p, hl, .store hΓ hΔ h₁ h₂ h => by
    by_cases hn : n = Γ₁.length
    · subst hn
      show RT₅ _ _ _ (.letOp .store [(Atom₅.var Γ₁.length).subst Γ₁.length _, _, _] _ _) _ _
      rw [subst_var_self₅]
      rw [← hl, set_self] at h
      refine .storeC (List.mem_cons_self) (substA₅ h₁ (fits_cap₅ p)) (substA₅ h₂ (fits_cap₅ p)) ?_
      rw [List.erase_cons_head]
      have := RT₅.substV (Γ₁ := t5cap :: Γ₁) (Δ₁ := true :: Δ₁) (by simp [hl]) h (fits_cap₅ p)
      simpa [hl] using this
    · have hn' : n ≠ Δ₁.length := hl ▸ hn
      show RT₅ _ _ _ (.letOp .store [(Atom₅.var n).subst Γ₁.length _, _, _] _ _) _ _
      rw [subst_var_ne₅ hn]
      refine .store (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ)
        (substA₅ h₁ (fits_cap₅ p)) (substA₅ h₂ (fits_cap₅ p)) ?_
      rw [set_mid hn'] at h
      have := RT₅.substC (Γ₁ := t5cap :: Γ₁) (Δ₁ := true :: _) p (by simp [List.length_set]; split_ifs <;> simp [hl]) h
      simp only [List.cons_append] at this
      rw [set_drop hn', hl] at this; exact this
  | _, Γ₁, Γ, Δ₁, Δ, Ω, .letOp .store [.const (.cap q), a₁, a₂] _ e, _, p, hl, .storeC hq h₁ h₂ h =>
    .storeC (List.mem_cons_of_mem _ hq) (substA₅ h₁ (fits_cap₅ p)) (substA₅ h₂ (fits_cap₅ p))
      (RT₅.perm (erase_cons_perm hq).symm (RT₅.substC (Γ₁ := t5cap :: Γ₁) (Δ₁ := true :: Δ₁) p (by simp [hl]) h))
  | _, Γ₁, Γ, Δ₁, Δ, Ω, .letOp .free [.var n] _ e, _, p, hl, .free hΓ hΔ h => by
    by_cases hn : n = Γ₁.length
    · subst hn
      show RT₅ _ _ _ (.letOp .free [(Atom₅.var Γ₁.length).subst Γ₁.length _] _ _) _ _
      rw [subst_var_self₅]
      rw [← hl, set_self] at h
      refine .freeC (List.mem_cons_self) ?_
      rw [List.erase_cons_head]
      have := RT₅.substV (Γ₁ := t5unit :: Γ₁) (Δ₁ := false :: Δ₁) (by simp [hl]) h (fits_cap₅ p)
      simpa [hl] using this
    · have hn' : n ≠ Δ₁.length := hl ▸ hn
      show RT₅ _ _ _ (.letOp .free [(Atom₅.var n).subst Γ₁.length _] _ _) _ _
      rw [subst_var_ne₅ hn]
      refine .free (by rw [← get_drop hn]; exact hΓ) (by rw [← hl, ← get_drop hn']; exact hΔ) ?_
      rw [set_mid hn'] at h
      have := RT₅.substC (Γ₁ := t5unit :: Γ₁) (Δ₁ := false :: _) p (by simp [List.length_set]; split_ifs <;> simp [hl]) h
      simp only [List.cons_append] at this
      rw [set_drop hn', hl] at this; exact this
  | _, Γ₁, Γ, Δ₁, Δ, Ω, .letOp .free [.const (.cap q)] _ e, _, p, hl, .freeC hq h =>
    .freeC (List.mem_cons_of_mem _ hq)
      (RT₅.perm (erase_cons_perm hq).symm (RT₅.substC (Γ₁ := t5unit :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h))
  | _, _, _, _, _, _, _, _, _, _, .app hΔ _ _ => (mask_empty_true hΔ).elim
  | _, _, _, _, _, _, .ite a e₁ e₂, _, p, hl, .ite h h₁ h₂ =>
    .ite (substA₅ h (fits_cap₅ p)) (RT₅.substC p hl h₁) (RT₅.substC p hl h₂)
  | _, Γ₁, Γ, Δ₁, Δ, _, .case a e₁ e₂, _, p, hl, .case h h₁ h₂ =>
    .case (substA₅ h (fits_cap₅ p)) (RT₅.substC (Γ₁ := _ :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h₁)
      (RT₅.substC (Γ₁ := _ :: Γ₁) (Δ₁ := false :: Δ₁) p (by simp [hl]) h₂)
  | _, Γ₁, Γ, Δ₁, Δ, _, .retK a ds, _, p, hl, .retK hc h hx => by
    show RT₅ _ _ _ (.retK (a.subst Γ₁.length _) (Atom₅.substL Γ₁.length (.const (.cap p)) ds)) _ _
    have := RT₅.retK hc (substA₅ h (fits_cap₅ p)) (CapsRT.substC p hl hx)
    rwa [substL_length] at this
  | _, Γ₁, Γ, Δ₁, Δ, _, .appK a₁ a₂ ds, _, p, hl, .appK h₁ h₂ hx => by
    show RT₅ _ _ _ (.appK (a₁.subst Γ₁.length _) (a₂.subst Γ₁.length _) (Atom₅.substL Γ₁.length (.const (.cap p)) ds)) _ _
    have h₁' := substA₅ h₁ (fits_cap₅ p)
    rw [← substL_length (k := Γ₁.length) (v := .const (.cap p)) ds] at h₁'
    have := RT₅.appK h₁' (substA₅ h₂ (fits_cap₅ p)) (CapsRT.substC p hl hx)
    rwa [substL_length] at this
  | _, Γ₁, Γ, Δ₁, Δ, Ω, .letK τ₁ j e₁ e₂, _, p, hl, .letK (Ω₂ := Ω₂) (τ₂ := σ₂) (k := kk) hs hp hc h₁ h₂ => by
    obtain ⟨A₁, A₂, B₁, B₂, a, rfl, rfl, hA, hB, hs'⟩ := split_mid_true hs
    have hlen : (List.replicate j t5cap ++ τ₁ :: Γ₁).length = Γ₁.length + j + 1 := by simp; omega
    cases a with
    | true =>
      refine .letK hs' (hp.cons p) hc (RT₅.substC p (hA.trans hl) h₁) ?_
      have h' : RT₅ ((List.replicate j t5cap ++ τ₁ :: Γ₁) ++ t5cap :: Γ)
          ((List.replicate j true ++ false :: B₁) ++ false :: B₂) Ω₂ e₂ σ₂ kk := by
        simpa [List.append_assoc] using h₂
      have := RT₅.substV (by simp [hB, hl]) h' (fits_cap₅ p)
      rw [hlen] at this
      simpa [List.append_assoc] using this
    | false =>
      refine .letK hs' ((hp.cons p).trans List.perm_middle.symm) hc (RT₅.substV (hA.trans hl) h₁ (fits_cap₅ p)) ?_
      have h' : RT₅ ((List.replicate j t5cap ++ τ₁ :: Γ₁) ++ t5cap :: Γ)
          ((List.replicate j true ++ false :: B₁) ++ true :: B₂) Ω₂ e₂ σ₂ kk := by
        simpa [List.append_assoc] using h₂
      have := RT₅.substC p (by simp [hB, hl]) h'
      rw [hlen] at this
      simpa [List.append_assoc] using this

end VIRL5
