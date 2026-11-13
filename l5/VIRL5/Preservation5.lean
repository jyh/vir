/-
  O95 layer L5, Lean arm (amend-24 LV4). PRESERVATION of runtime typing in FRAME form (L2's `pres_rt`, restated as ONE induction
  over ⟶₅, which folds L1's steps in): a closed RT₅-typed term owning exactly Ω, on its fragment σq beside any disjoint frame σf,
  steps to an RT₅-typed term owning some Ω′ on a fragment σq′ beside the SAME frame. The store cases go through L2's own `opStep`
  (opStep₅ is defined by it) and L2's framed axioms, unchanged. THE L1′ CASES: a lending call substitutes the k lent constants and
  the argument into the callee's body (`RT₅.substCaps`), owning what the caller lent; a `letK` of a `retK` substitutes the handed-back
  constants and the result into the continuation, owning both parts again. Neither touches the store.
-/
import VIRL5.SemBase5
import VIRL2.Preservation
import VIRL5.CE

namespace VIRL5
open VIRL1 VIRL2

theorem decide_t5cap_false {t : Ty₅} (h : t.hasCap = false) : decide (t = t5cap) = false := by
  rw [decide_eq_false_iff_not]; rintro rfl; simp [Ty₅.hasCap, t5cap] at h

/-- Substituting k capability constants for the k innermost (true) positions: the term owns them too. -/
theorem RT₅.substCaps : ∀ (ps : List Int) {Γ : Ctx₅} {Δ : List Bool} {Ω e τ k},
    RT₅ (List.replicate ps.length t5cap ++ Γ) (List.replicate ps.length true ++ Δ) Ω e τ k →
    ∃ Ω', Ω'.Perm (ps ++ Ω) ∧ RT₅ Γ Δ Ω' (Tm₅.substAll (capConsts ps) e) τ k
  | [], _, _, Ω, _, _, _, h => ⟨Ω, .refl _, h⟩
  | p :: ps, Γ, Δ, Ω, e, τ, k, h => by
      have h' : RT₅ (List.replicate ps.length t5cap ++ t5cap :: Γ) (List.replicate ps.length true ++ true :: Δ) Ω e τ k := by
        simpa [List.replicate_succ', List.append_assoc] using h
      obtain ⟨Ω', hp, ht⟩ := RT₅.substCaps ps h'
      exact ⟨p :: Ω', hp.cons p, RT₅.substC (Γ₁ := []) (Δ₁ := []) p rfl ht⟩

theorem ιL_map_const : ∀ cs : List Const, ιL (cs.map Atom.const) = cs.map Atom₅.const
  | [] => rfl
  | c :: cs => by simp [ιL, ιA, ιL_map_const cs]

theorem opStep₅_consts (o : Op) (cs : List Const) (σ : Store) :
    opStep₅ o (cs.map Atom₅.const) σ = (opStep o (cs.map Atom.const) σ).map fun p => (ιA p.1, p.2) := by
  have := opStep₅_ι o (cs.map Atom.const) σ
  rw [ιL_map_const] at this; exact this

theorem evalL_capConsts_eq {ps : List Int} {qs : List Atom₅} (h : Atom₅.evalL (capConsts ps) = some qs) : qs = capConsts ps := by
  rw [evalL_capConsts] at h; exact (Option.some.inj h).symm

theorem pres₅ : ∀ {c c' : Config₅}, Step₅ c c' → ∀ {Ω τ k σq σf}, RT₅ [] [] Ω c.1 τ k → OwnAll Ω σq →
    Store.Disj σq σf → Store.WF (σq ⊎ σf) → c.2 = σq ⊎ σf →
    ∃ Ω' σq', RT₅ [] [] Ω' c'.1 τ k ∧ OwnAll Ω' σq' ∧ Store.Disj σq' σf ∧ c'.2 = σq' ⊎ σf ∧ Store.WF c'.2 := by
  intro c c' h
  induction h with
  | letRet hv =>
    intro Ω τ k σq σf hrt hown hd hwf hσ
    dsimp only at hrt hσ ⊢
    cases hrt with
    | letE hs hp hc h₁ h₂ =>
      cases hs
      cases h₁ with
      | ret _ ha =>
        obtain ⟨w, hw, -, hwt⟩ := eval_total₅ _ ha
        rw [hw] at hv; cases hv
        rw [decide_t5cap_false (atom_noCap₅ ha)] at h₂
        exact ⟨_, σq, RT₅.substV (Γ₁ := []) (Δ₁ := []) rfl h₂ (.inl hwt), OwnAll.perm (by simpa using hp) _ hown,
          hd, hσ, hσ ▸ hwf⟩
      | retCap hΓ _ => simp at hΓ
      | retCapC _ =>
        simp [Atom₅.eval] at hv; subst hv
        rw [show decide (t5cap = t5cap) = true from decide_eq_true rfl] at h₂
        exact ⟨_, σq, RT₅.substC (Γ₁ := []) (Δ₁ := []) _ rfl h₂, OwnAll.perm (by simpa using hp) _ hown,
          hd, hσ, hσ ▸ hwf⟩
  | letStep _ ih =>
    intro Ω τ k σq σf hrt hown hd hwf hσ
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
  | letKStep _ ih =>
    intro Ω τ k σq σf hrt hown hd hwf hσ
    dsimp only at hrt hσ ⊢
    cases hrt with
    | letK hs hp hc ht₁ ht₂ =>
      cases hs
      obtain ⟨σ₁, σ₂, h12, rfl, ho₁, ho₂⟩ := (OwnAll.append _ _ _).1 (OwnAll.perm hp _ hown)
      obtain ⟨hd₁, hd₂⟩ := (Store.disj_union_left _ _ _).1 hd
      have hd₁' : Store.Disj σ₁ (σ₂ ⊎ σf) := (Store.disj_union_right _ _ _).2 ⟨h12, hd₁⟩
      rw [Store.union_assoc] at hwf hσ
      obtain ⟨Ω₁', σ₁', ht₁', ho₁', hd', hσ', hwf'⟩ := ih ht₁ ho₁ hd₁' hwf hσ
      obtain ⟨hd₁₂', hd₁f'⟩ := (Store.disj_union_right _ _ _).1 hd'
      refine ⟨Ω₁' ++ _, σ₁' ⊎ σ₂, .letK .nil (List.Perm.refl _) hc ht₁' ht₂,
        (OwnAll.append _ _ _).2 ⟨σ₁', σ₂, hd₁₂', rfl, ho₁', ho₂⟩, (Store.disj_union_left _ _ _).2 ⟨hd₁f', hd₂⟩, ?_, hwf'⟩
      rw [Store.union_assoc]; exact hσ'
  | letKRet hv hqs hlen =>
    intro Ω τ k σq σf hrt hown hd hwf hσ
    dsimp only at hrt hσ ⊢
    cases hrt with
    | letK hs hp hc ht₁ ht₂ =>
      cases hs
      cases ht₁ with
      | retK hc' ha hx =>
        obtain ⟨ps, rfl, hps⟩ := CapsRT.closed hx
        obtain rfl := evalL_capConsts_eq hqs
        obtain ⟨w, hw, -, hwt⟩ := eval_total₅ _ ha
        rw [hw] at hv; cases hv
        rw [capConsts_length] at ht₂
        obtain ⟨Ω', hp', ht'⟩ := RT₅.substCaps ps ht₂
        refine ⟨Ω', σq, RT₅.substV (Γ₁ := []) (Δ₁ := []) rfl ht' (.inl hwt), OwnAll.perm ?_ _ hown, hd, hσ, hσ ▸ hwf⟩
        exact hp.trans ((hps.append_right _).trans hp'.symm)
  | letRetK0 hv =>
    intro Ω τ k σq σf hrt hown hd hwf hσ
    dsimp only at hrt hσ ⊢
    cases hrt with
    | letE hs hp hc h₁ h₂ =>
      cases hs
      cases h₁ with
      | retK hc' ha hx =>
        obtain ⟨ps, hps, hΩ⟩ := CapsRT.closed hx
        cases ps with
        | cons _ _ => simp [capConsts] at hps
        | nil =>
          obtain ⟨w, hw, -, hwt⟩ := eval_total₅ _ ha
          rw [hw] at hv; cases hv
          rw [decide_t5cap_false (atom_noCap₅ ha)] at h₂
          exact ⟨_, σq, RT₅.substV (Γ₁ := []) (Δ₁ := []) rfl h₂ (.inl hwt),
            OwnAll.perm (hp.trans (by rw [List.perm_nil.1 hΩ, List.nil_append])) _ hown, hd, hσ, hσ ▸ hwf⟩
  | letKRet0 hv =>
    intro Ω τ k σq σf hrt hown hd hwf hσ
    dsimp only at hrt hσ ⊢
    cases hrt with
    | letK hs hp hc ht₁ ht₂ =>
      cases hs
      cases ht₁ with
      | ret _ ha =>
        obtain ⟨w, hw, -, hwt⟩ := eval_total₅ _ ha
        rw [hw] at hv; cases hv
        exact ⟨_, σq, RT₅.substV (Γ₁ := []) (Δ₁ := []) rfl ht₂ (.inl hwt), OwnAll.perm (by simpa using hp) _ hown,
          hd, hσ, hσ ▸ hwf⟩
      | retCap hΓ _ => simp at hΓ
      | retCapC _ => simp [Ty₅.hasCap, t5cap] at hc
  | op hvs hop =>
    intro Ω τ k σq σf hrt hown hd hwf hσ
    dsimp only at hrt hσ ⊢
    subst hσ
    cases hrt with
    | alloc ha ht =>
      obtain ⟨w, hw, hval, hwt⟩ := eval_total₅ _ ha
      obtain ⟨n, rfl⟩ := canon_int₅ hval hwt
      simp [Atom₅.evalL, hw] at hvs; subst hvs
      have hop₀ := hop
      rw [show [Atom₅.const (.int n)] = [Const.int n].map Atom₅.const from rfl, opStep₅_consts] at hop₀
      obtain ⟨⟨v₀, σ₀⟩, hopL, hv₀⟩ := Option.map_eq_some_iff.1 hop₀
      simp only [Prod.mk.injEq] at hv₀; obtain ⟨rfl, rfl⟩ := hv₀
      have hk : 0 < n := by
        simp only [List.map, opStep, Store.alloc] at hopL
        by_contra hc; rw [if_neg hc] at hopL; simp at hopL
      obtain ⟨v₁, σn, hop', hdn, hwfn, p, rfl, hreg⟩ :=
        alloc_axiom n hk Store.empty (σq ⊎ σf) rfl (disj_empty_left _) (by rw [Store.empty_union]; exact hwf)
      rw [Store.empty_union] at hop'
      simp only [List.map] at hopL
      rw [hopL] at hop'; cases hop'
      obtain ⟨hdnq, hdnf⟩ := (Store.disj_union_right _ _ _).1 hdn
      exact ⟨p :: Ω, σn ⊎ σq, RT₅.substC (Γ₁ := []) (Δ₁ := []) p rfl ht, ⟨σn, σq, hdnq, rfl, ⟨_, hreg.isRegion⟩, hown⟩,
        (Store.disj_union_left _ _ _).2 ⟨hdnf, hd⟩, (Store.union_assoc _ _ _).symm, hwfn⟩
    | load hΓ _ _ _ => simp at hΓ
    | @loadC _ _ _ q _ _ _ _ _ ha ht =>
      obtain ⟨w, hw, hval, hwt⟩ := eval_total₅ _ ha
      obtain ⟨i, rfl⟩ := canon_int₅ hval hwt
      simp [Atom₅.evalL, Atom₅.eval, hw] at hvs; subst hvs
      rw [show [Atom₅.const (.cap q), Atom₅.const (.int i)] = [Const.cap q, Const.int i].map Atom₅.const from rfl,
        opStep₅_consts] at hop
      obtain ⟨⟨v₀, σ₀⟩, hopL, hv₀⟩ := Option.map_eq_some_iff.1 hop
      simp only [Prod.mk.injEq] at hv₀; obtain ⟨rfl, rfl⟩ := hv₀
      simp only [List.map, opStep, Option.map_eq_some_iff] at hopL
      obtain ⟨u, -, hu⟩ := hopL
      cases hu
      exact ⟨Ω, σq, RT₅.substV (Γ₁ := []) (Δ₁ := []) rfl ht (.inl .int), hown, hd, rfl, hwf⟩
    | store hΓ _ _ _ _ => simp at hΓ
    | @storeC _ _ _ q _ _ _ _ _ hp h₁ h₂ ht =>
      obtain ⟨w₁, hw₁, hv₁, ht₁⟩ := eval_total₅ _ h₁
      obtain ⟨i, rfl⟩ := canon_int₅ hv₁ ht₁
      obtain ⟨w₂, hw₂, hv₂, ht₂⟩ := eval_total₅ _ h₂
      obtain ⟨x, rfl⟩ := canon_int₅ hv₂ ht₂
      simp [Atom₅.evalL, Atom₅.eval, hw₁, hw₂] at hvs; subst hvs
      have hop₀ := hop
      rw [show [Atom₅.const (.cap q), Atom₅.const (.int i), Atom₅.const (.int x)] =
        [Const.cap q, Const.int i, Const.int x].map Atom₅.const from rfl, opStep₅_consts] at hop₀
      obtain ⟨⟨v₀, σ₀⟩, hopL, hv₀⟩ := Option.map_eq_some_iff.1 hop₀
      simp only [Prod.mk.injEq] at hv₀; obtain ⟨rfl, rfl⟩ := hv₀
      simp only [List.map] at hopL
      obtain ⟨σr, σs, hrs, rfl, ⟨n, hreg⟩, hos⟩ := OwnAll.extract hp hown
      obtain ⟨hdr, hds⟩ := (Store.disj_union_left _ _ _).1 hd
      rw [Store.union_assoc] at hopL hwf
      have hlk := hreg.lookup_union (σs ⊎ σf)
      have hi : 0 ≤ i ∧ i < n := by
        simp only [opStep, Store.store, hlk] at hopL
        by_contra hc; rw [if_neg hc] at hopL; simp at hopL
      obtain ⟨c, σn, hop', hdn, hwfn, rfl, hreg'⟩ :=
        store_region _ n i x hi σr (σs ⊎ σf) hreg ((Store.disj_union_right _ _ _).2 ⟨hrs, hdr⟩) hwf
      rw [hopL] at hop'; cases hop'
      obtain ⟨hdns, hdnf⟩ := (Store.disj_union_right _ _ _).1 hdn
      exact ⟨_ :: _, σn ⊎ σs, RT₅.substC (Γ₁ := []) (Δ₁ := []) _ rfl ht, ⟨σn, σs, hdns, rfl, ⟨n, hreg'⟩, hos⟩,
        (Store.disj_union_left _ _ _).2 ⟨hdnf, hds⟩, (Store.union_assoc _ _ _).symm, hwfn⟩
    | free hΓ _ _ => simp at hΓ
    | @freeC _ _ _ q _ _ _ hp ht =>
      simp [Atom₅.evalL, Atom₅.eval] at hvs; subst hvs
      have hop₀ := hop
      rw [show [Atom₅.const (.cap q)] = [Const.cap q].map Atom₅.const from rfl, opStep₅_consts] at hop₀
      obtain ⟨⟨v₀, σ₀⟩, hopL, hv₀⟩ := Option.map_eq_some_iff.1 hop₀
      simp only [Prod.mk.injEq] at hv₀; obtain ⟨rfl, rfl⟩ := hv₀
      simp only [List.map] at hopL
      obtain ⟨σr, σs, hrs, rfl, ⟨n, hreg⟩, hos⟩ := OwnAll.extract hp hown
      obtain ⟨hdr, hds⟩ := (Store.disj_union_left _ _ _).1 hd
      rw [Store.union_assoc] at hopL hwf
      obtain ⟨c, σn, hop', hdn, hwfn, rfl, rfl⟩ :=
        free_axiom _ n σr (σs ⊎ σf) hreg ((Store.disj_union_right _ _ _).2 ⟨hrs, hdr⟩) hwf
      rw [hopL] at hop'; cases hop'
      refine ⟨_, σs, RT₅.substV (Γ₁ := []) (Δ₁ := []) rfl ht (.inl .unit), hos, hds, Store.empty_union _, ?_⟩
      exact hwfn
  | appLam hv₁ hv₂ =>
    intro Ω τ k σq σf hrt hown hd hwf hσ
    dsimp only at hrt hσ ⊢
    cases hrt with
    | app _ h₁ h₂ =>
      obtain ⟨w₁, hw₁, -, hwt₁⟩ := eval_total₅ _ h₁
      obtain ⟨w₂, hw₂, -, hwt₂⟩ := eval_total₅ _ h₂
      rw [hw₁] at hv₁; cases hv₁
      rw [hw₂] at hv₂; cases hv₂
      cases hwt₁ with
      | lam _ _ hm hl hb =>
        obtain rfl := mask_one hm hl
        exact ⟨[], σq, RT₅.ofTyped (subst₅ (Γ₁ := []) (Δ₁ := []) rfl hb (.inl hwt₂)), hown, hd, hσ, hσ ▸ hwf⟩
  | appFix hv₁ hv₂ =>
    intro Ω τ k σq σf hrt hown hd hwf hσ
    dsimp only at hrt hσ ⊢
    cases hrt with
    | app _ h₁ h₂ =>
      obtain ⟨w₁, hw₁, -, hwt₁⟩ := eval_total₅ _ h₁
      obtain ⟨w₂, hw₂, -, hwt₂⟩ := eval_total₅ _ h₂
      rw [hw₁] at hv₁; cases hv₁
      rw [hw₂] at hv₂; cases hv₂
      have hfix := hwt₁
      cases hwt₁ with
      | fix _ _ hm hl hb =>
        obtain rfl := mask_two hm hl
        exact ⟨[], σq, RT₅.ofTyped (subst₅ (Γ₁ := []) (Δ₁ := []) rfl
          (subst₅ (Γ₁ := []) (Δ₁ := []) rfl hb (.inl hwt₂)) (.inl hfix)), hown, hd, hσ, hσ ▸ hwf⟩
  | appKLam hv₁ hv₂ hqs hlen =>
    intro Ω τ k σq σf hrt hown hd hwf hσ
    dsimp only at hrt hσ ⊢
    cases hrt with
    | appK h₁ h₂ hx =>
      obtain ⟨ps, rfl, hps⟩ := CapsRT.closed hx
      obtain rfl := evalL_capConsts_eq hqs
      obtain ⟨w₁, hw₁, -, hwt₁⟩ := eval_total₅ _ h₁
      obtain ⟨w₂, hw₂, -, hwt₂⟩ := eval_total₅ _ h₂
      rw [hw₁] at hv₁; cases hv₁
      rw [hw₂] at hv₂; cases hv₂
      cases hwt₁ with
      | lam _ _ hm hl hb =>
        obtain rfl := mask_one hm hl
        rw [capConsts_length] at hb
        obtain ⟨Ω', hp', ht'⟩ := RT₅.substCaps ps (RT₅.ofTyped hb)
        refine ⟨Ω', σq, ?_, OwnAll.perm (hps.trans (by simpa using hp'.symm)) _ hown, hd, hσ, hσ ▸ hwf⟩
        rw [capConsts_length]
        exact RT₅.substV (Γ₁ := []) (Δ₁ := []) rfl ht' (.inl hwt₂)
  | appKFix hv₁ hv₂ hqs hlen =>
    intro Ω τ k σq σf hrt hown hd hwf hσ
    dsimp only at hrt hσ ⊢
    cases hrt with
    | appK h₁ h₂ hx =>
      obtain ⟨ps, rfl, hps⟩ := CapsRT.closed hx
      obtain rfl := evalL_capConsts_eq hqs
      obtain ⟨w₁, hw₁, -, hwt₁⟩ := eval_total₅ _ h₁
      obtain ⟨w₂, hw₂, -, hwt₂⟩ := eval_total₅ _ h₂
      rw [hw₁] at hv₁; cases hv₁
      rw [hw₂] at hv₂; cases hv₂
      have hfix := hwt₁
      cases hwt₁ with
      | fix _ _ hm hl hb =>
        obtain rfl := mask_two hm hl
        rw [capConsts_length] at hb hfix
        obtain ⟨Ω', hp', ht'⟩ := RT₅.substCaps ps (RT₅.ofTyped hb)
        refine ⟨Ω', σq, ?_, OwnAll.perm (hps.trans (by simpa using hp'.symm)) _ hown, hd, hσ, hσ ▸ hwf⟩
        rw [capConsts_length]
        exact RT₅.substV (Γ₁ := []) (Δ₁ := []) rfl (RT₅.substV (Γ₁ := []) (Δ₁ := []) rfl ht' (.inl hwt₂)) (.inl hfix)
  | iteT _ _ =>
    intro Ω τ k σq σf hrt hown hd hwf hσ
    cases hrt with
    | ite _ h₁ _ => exact ⟨Ω, σq, h₁, hown, hd, hσ, hσ ▸ hwf⟩
  | iteF _ _ =>
    intro Ω τ k σq σf hrt hown hd hwf hσ
    cases hrt with
    | ite _ _ h₂ => exact ⟨Ω, σq, h₂, hown, hd, hσ, hσ ▸ hwf⟩
  | caseL hv =>
    intro Ω τ k σq σf hrt hown hd hwf hσ
    cases hrt with
    | case ha h₁ _ =>
      obtain ⟨w, hw, -, hwt⟩ := eval_total₅ _ ha
      rw [hw] at hv; cases hv
      cases hwt with
      | inl _ hx => exact ⟨Ω, σq, RT₅.substV (Γ₁ := []) (Δ₁ := []) rfl h₁ (.inl hx), hown, hd, hσ, hσ ▸ hwf⟩
  | caseR hv =>
    intro Ω τ k σq σf hrt hown hd hwf hσ
    cases hrt with
    | case ha _ h₂ =>
      obtain ⟨w, hw, -, hwt⟩ := eval_total₅ _ ha
      rw [hw] at hv; cases hv
      cases hwt with
      | inr _ hx => exact ⟨Ω, σq, RT₅.substV (Γ₁ := []) (Δ₁ := []) rfl h₂ (.inl hx), hown, hd, hσ, hσ ▸ hwf⟩

end VIRL5
