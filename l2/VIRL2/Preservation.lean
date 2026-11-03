/-
  O95 layer L2, Lean arm. Y5 step 8 (STAGE-L2-LEAN): PRESERVATION of runtime typing, in FRAME form. A closed runtime-typed
  term owning exactly the regions Ω, run on its own fragment σq beside ANY disjoint frame σf, steps to a runtime-typed term
  owning some Ω′, on a fragment σq′ beside the SAME frame, untouched; the whole store stays well-formed.
  L1's steps (`pure_pres`) keep the store and permute Ω (a `let` of a capability constant moves p into the body).
  `letStep` splits Ω₁ ++ Ω₂: the e₂ part joins the frame. The O₂ operations go through the framed small axioms
  (`alloc_axiom`, `store_region`, `free_axiom` on one extracted region, the rest of OwnAll in the frame); `load` keeps σ.
-/
import VIRL2.OwnAll
import VIRL2.Progress
import VIRL2.RTSubst

namespace VIRL2
open VIRL1

theorem IsRegion.lookup_union {p : Int} {n : Nat} {σ : Store} (h : IsRegion p n σ) (X : Store) :
    ((σ ⊎ X).R).lookup p = some n :=
  regionAt_lookup_p (σf := X) h.regionAt

theorem decide_tcap_false {t : Ty₂} (h : hasCap t = false) : decide (t = tcap) = false := by
  rw [decide_eq_false_iff_not]; rintro rfl; simp [hasCap, tcap] at h

theorem mask_one {Δ : List Bool} (hm : Mask.empty Δ) (hl : Δ.length = 1) : Δ = [false] := by
  rw [empty_rep hm, hl]; rfl

theorem mask_two {Δ : List Bool} (hm : Mask.empty Δ) (hl : Δ.length = 2) : Δ = [false, false] := by
  rw [empty_rep hm, hl]; rfl

/-- L1's (pure) steps preserve closed runtime typing; the owned list is permuted, the store is not touched. -/
theorem pure_pres : ∀ {e e' : Tm₂}, Step e e' → ∀ {Ω τ}, RT [] [] Ω e τ → ∃ Ω', Ω'.Perm Ω ∧ RT [] [] Ω' e' τ := by
  intro e e' h
  induction h with
  | letRet hv =>
    intro Ω τ hrt
    cases hrt with
    | letE hs hp hc h₁ h₂ =>
      cases hs
      cases h₁ with
      | ret _ ha =>
        obtain ⟨w, hw, -, hwt⟩ := eval_total₂ _ ha
        rw [hw] at hv; cases hv
        rw [decide_tcap_false (atom_noCap ha)] at h₂
        refine ⟨_, ?_, RT.substV (Γ₁ := []) (Δ₁ := []) rfl h₂ (.inl hwt)⟩
        simpa using hp.symm
      | retCap hΓ _ => simp at hΓ
      | retCapC _ =>
        simp [Atom.eval] at hv; subst hv
        rw [show decide (tcap = tcap) = true from decide_eq_true rfl] at h₂
        refine ⟨_, ?_, RT.substC (Γ₁ := []) (Δ₁ := []) _ rfl h₂⟩
        simpa using hp.symm
  | letStep _ ih =>
    intro Ω τ hrt
    cases hrt with
    | letE hs hp hc h₁ h₂ =>
      cases hs
      obtain ⟨Ω₁', hp₁, h₁'⟩ := ih h₁
      exact ⟨Ω, List.Perm.refl _, .letE .nil (hp.trans (hp₁.symm.append_right _)) hc h₁' h₂⟩
  | appLam hv₁ hv₂ =>
    intro Ω τ hrt
    cases hrt with
    | app _ h₁ h₂ =>
      obtain ⟨w₁, hw₁, -, hwt₁⟩ := eval_total₂ _ h₁
      obtain ⟨w₂, hw₂, -, hwt₂⟩ := eval_total₂ _ h₂
      rw [hw₁] at hv₁; cases hv₁
      rw [hw₂] at hv₂; cases hv₂
      cases hwt₁ with
      | lam _ _ hm hl hb =>
        obtain rfl := mask_one hm hl
        exact ⟨[], List.Perm.refl _, RT.ofTyped (subst₂ (Γ₁ := []) (Δ₁ := []) rfl hb (.inl hwt₂))⟩
  | appFix hv₁ hv₂ =>
    intro Ω τ hrt
    cases hrt with
    | app _ h₁ h₂ =>
      obtain ⟨w₁, hw₁, -, hwt₁⟩ := eval_total₂ _ h₁
      obtain ⟨w₂, hw₂, -, hwt₂⟩ := eval_total₂ _ h₂
      rw [hw₁] at hv₁; cases hv₁
      rw [hw₂] at hv₂; cases hv₂
      have hfix := hwt₁
      cases hwt₁ with
      | fix _ _ hm hl hb =>
        obtain rfl := mask_two hm hl
        exact ⟨[], List.Perm.refl _, RT.ofTyped (subst₂ (Γ₁ := []) (Δ₁ := []) rfl
          (subst₂ (Γ₁ := []) (Δ₁ := []) rfl hb (.inl hwt₂)) (.inl hfix))⟩
  | iteT _ _ =>
    intro Ω τ hrt
    cases hrt with
    | ite _ h₁ _ => exact ⟨Ω, List.Perm.refl _, h₁⟩
  | iteF _ _ =>
    intro Ω τ hrt
    cases hrt with
    | ite _ _ h₂ => exact ⟨Ω, List.Perm.refl _, h₂⟩
  | caseL hv =>
    intro Ω τ hrt
    cases hrt with
    | case ha h₁ _ =>
      obtain ⟨w, hw, -, hwt⟩ := eval_total₂ _ ha
      rw [hw] at hv; cases hv
      cases hwt with
      | inl _ hx => exact ⟨Ω, List.Perm.refl _, RT.substV (Γ₁ := []) (Δ₁ := []) rfl h₁ (.inl hx)⟩
  | caseR hv =>
    intro Ω τ hrt
    cases hrt with
    | case ha _ h₂ =>
      obtain ⟨w, hw, -, hwt⟩ := eval_total₂ _ ha
      rw [hw] at hv; cases hv
      cases hwt with
      | inr _ hx => exact ⟨Ω, List.Perm.refl _, RT.substV (Γ₁ := []) (Δ₁ := []) rfl h₂ (.inl hx)⟩

/-- Preservation on configurations (the form the induction runs on). -/
theorem pres_rt : ∀ {c c' : Config}, Step₂ c c' → ∀ {Ω τ σq σf}, RT [] [] Ω c.1 τ → OwnAll Ω σq →
    Store.Disj σq σf → Store.WF (σq ⊎ σf) → c.2 = σq ⊎ σf →
    ∃ Ω' σq', RT [] [] Ω' c'.1 τ ∧ OwnAll Ω' σq' ∧ Store.Disj σq' σf ∧ c'.2 = σq' ⊎ σf ∧ Store.WF c'.2 := by
  intro c c' h
  induction h with
  | pure hs =>
    intro Ω τ σq σf hrt hown hd hwf hσ
    obtain ⟨Ω', hp, ht⟩ := pure_pres hs hrt
    refine ⟨Ω', σq, ht, OwnAll.perm hp.symm _ hown, hd, hσ, ?_⟩
    dsimp only at hσ ⊢; rw [hσ]; exact hwf
  | letStep _ ih =>
    intro Ω τ σq σf hrt hown hd hwf hσ
    dsimp only at hrt hσ ⊢
    cases hrt with
    | letE hs hp hc ht₁ ht₂ =>
      cases hs
      obtain ⟨σ₁, σ₂, h12, rfl, ho₁, ho₂⟩ := (OwnAll.append _ _ _).1 (OwnAll.perm hp _ hown)
      obtain ⟨hd₁, hd₂⟩ := (Store.disj_union_left _ _ _).1 hd
      have hd₁' : Store.Disj σ₁ (σ₂ ⊎ σf) := (Store.disj_union_right _ _ _).2 ⟨h12, hd₁⟩
      rw [Store.union_assoc] at hwf hσ
      obtain ⟨Ω₁', σ₁', ht₁', ho₁', hd', hσ', hwf'⟩ := ih ht₁ ho₁ hd₁' hwf hσ
      obtain ⟨hd₁₂', hd₁f'⟩ := (Store.disj_union_right _ _ _).1 hd'
      refine ⟨Ω₁' ++ _, σ₁' ⊎ σ₂, .letE .nil (List.Perm.refl _) hc ht₁' ht₂,
        (OwnAll.append _ _ _).2 ⟨σ₁', σ₂, hd₁₂', rfl, ho₁', ho₂⟩, (Store.disj_union_left _ _ _).2 ⟨hd₁f', hd₂⟩, ?_, hwf'⟩
      rw [Store.union_assoc]; exact hσ'
  | op hvs hop =>
    intro Ω τ σq σf hrt hown hd hwf hσ
    dsimp only at hrt hσ ⊢
    subst hσ
    cases hrt with
    | alloc ha ht =>
      obtain ⟨w, hw, hval, hwt⟩ := eval_total₂ _ ha
      obtain ⟨k, rfl⟩ := canon_int hval hwt
      simp [Atom.evalL, hw] at hvs; subst hvs
      have hk : 0 < k := by
        simp only [opStep, Store.alloc] at hop
        by_contra hc; rw [if_neg hc] at hop; simp at hop
      obtain ⟨v₁, σn, hop', hdn, hwfn, p, rfl, hreg⟩ :=
        alloc_axiom k hk Store.empty (σq ⊎ σf) rfl (disj_empty_left _) (by rw [Store.empty_union]; exact hwf)
      rw [Store.empty_union, hop] at hop'
      cases hop'
      obtain ⟨hdnq, hdnf⟩ := (Store.disj_union_right _ _ _).1 hdn
      exact ⟨p :: Ω, σn ⊎ σq, RT.substC (Γ₁ := []) (Δ₁ := []) p rfl ht, ⟨σn, σq, hdnq, rfl, ⟨_, hreg.isRegion⟩, hown⟩,
        (Store.disj_union_left _ _ _).2 ⟨hdnf, hd⟩, (Store.union_assoc _ _ _).symm, hwfn⟩
    | load hΓ _ _ _ => simp at hΓ
    | loadC _ ha ht =>
      obtain ⟨w, hw, hval, hwt⟩ := eval_total₂ _ ha
      obtain ⟨i, rfl⟩ := canon_int hval hwt
      simp [Atom.evalL, Atom.eval, hw] at hvs; subst hvs
      simp only [opStep, Option.map_eq_some_iff] at hop
      obtain ⟨u, -, hu⟩ := hop
      cases hu
      exact ⟨Ω, σq, RT.substV (Γ₁ := []) (Δ₁ := []) rfl ht (.inl .int), hown, hd, rfl, hwf⟩
    | store hΓ _ _ _ _ => simp at hΓ
    | storeC hp h₁ h₂ ht =>
      obtain ⟨w₁, hw₁, hv₁, ht₁⟩ := eval_total₂ _ h₁
      obtain ⟨i, rfl⟩ := canon_int hv₁ ht₁
      obtain ⟨w₂, hw₂, hv₂, ht₂⟩ := eval_total₂ _ h₂
      obtain ⟨x, rfl⟩ := canon_int hv₂ ht₂
      simp [Atom.evalL, Atom.eval, hw₁, hw₂] at hvs; subst hvs
      obtain ⟨σr, σs, hrs, rfl, ⟨n, hreg⟩, hos⟩ := OwnAll.extract hp hown
      obtain ⟨hdr, hds⟩ := (Store.disj_union_left _ _ _).1 hd
      rw [Store.union_assoc] at hop hwf
      have hlk := hreg.lookup_union (σs ⊎ σf)
      have hi : 0 ≤ i ∧ i < n := by
        simp only [opStep, Store.store, hlk] at hop
        by_contra hc; rw [if_neg hc] at hop; simp at hop
      obtain ⟨c, σn, hop', hdn, hwfn, rfl, hreg'⟩ :=
        store_region _ n i x hi σr (σs ⊎ σf) hreg ((Store.disj_union_right _ _ _).2 ⟨hrs, hdr⟩) hwf
      rw [hop] at hop'; cases hop'
      obtain ⟨hdns, hdnf⟩ := (Store.disj_union_right _ _ _).1 hdn
      exact ⟨_ :: _, σn ⊎ σs, RT.substC (Γ₁ := []) (Δ₁ := []) _ rfl ht, ⟨σn, σs, hdns, rfl, ⟨n, hreg'⟩, hos⟩,
        (Store.disj_union_left _ _ _).2 ⟨hdnf, hds⟩, (Store.union_assoc _ _ _).symm, hwfn⟩
    | free hΓ _ _ => simp at hΓ
    | freeC hp ht =>
      simp [Atom.evalL, Atom.eval] at hvs; subst hvs
      obtain ⟨σr, σs, hrs, rfl, ⟨n, hreg⟩, hos⟩ := OwnAll.extract hp hown
      obtain ⟨hdr, hds⟩ := (Store.disj_union_left _ _ _).1 hd
      rw [Store.union_assoc] at hop hwf
      obtain ⟨c, σn, hop', hdn, hwfn, rfl, rfl⟩ :=
        free_axiom _ n σr (σs ⊎ σf) hreg ((Store.disj_union_right _ _ _).2 ⟨hrs, hdr⟩) hwf
      rw [hop] at hop'; cases hop'
      refine ⟨_, σs, RT.substV (Γ₁ := []) (Δ₁ := []) rfl ht (.inl .unit), hos, hds, Store.empty_union _, ?_⟩
      exact hwfn

/-- PRESERVATION in frame form (STAGE-L2-LEAN step 8). -/
theorem preservation {Ω : List Int} {e e' : Tm₂} {τ : Ty₂} {σq σf σ' : Store} (ht : RT [] [] Ω e τ)
    (ho : OwnAll Ω σq) (hd : Store.Disj σq σf) (hwf : Store.WF (σq ⊎ σf)) (hs : Step₂ (e, σq ⊎ σf) (e', σ')) :
    ∃ Ω' σq', RT [] [] Ω' e' τ ∧ OwnAll Ω' σq' ∧ Store.Disj σq' σf ∧ σ' = σq' ⊎ σf ∧ Store.WF σ' :=
  pres_rt hs ht ho hd hwf rfl

end VIRL2
