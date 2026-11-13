/-
  O95 layer L5, Lean arm (amend-24 LV3): THE CONSERVATIVE EXTENSION on ⟶, BOTH directions, through ι.
  An L2 program steps under ⟶₅ exactly as under ⟶₂, the store identical (its ⊢₅ typing at k = 0 is its ⊢₂ typing: `type_ι`,
  Typing5.lean). The shape is L4's CE (VIRL4/CE.lean); the store has no lock table, and the three new rules never fire on an image
  of ι (no `appK`, `retK` or `letK` there).
-/
import VIRL5.Step5

namespace VIRL5
open VIRL1 VIRL2

/-! ## Evaluation commutes with ι. -/

theorem constsOf₅_ι : ∀ vs : List Atom₂, constsOf₅ (ιL vs) = constsOf vs
  | [] => rfl
  | v :: vs => by
      cases v with
      | const c => simp only [ιL, ιA, constsOf₅, constsOf, constsOf₅_ι vs]
      | _ => rfl

mutual
theorem eval_ι : ∀ a : Atom₂, Atom₅.eval (ιA a) = (Atom.eval a).map ιA
  | .var _ => rfl
  | .const _ => rfl
  | .prim p as => by
      have ih := evalL_ι as
      simp only [ιA, Atom₅.eval, Atom.eval, ih]
      cases (Atom.evalL as) with
      | none => rfl
      | some vs =>
          simp only [Option.map_some, Option.bind_some, constsOf₅_ι]
          cases constsOf vs with
          | none => rfl
          | some cs =>
              simp only [Option.bind_some, S₂]
              cases pInterp p cs <;> rfl
  | .lam _ _ => rfl
  | .fix _ _ _ => rfl
  | .pair a₁ a₂ => by
      simp only [ιA, Atom₅.eval, Atom.eval, eval_ι a₁, eval_ι a₂]
      cases Atom.eval a₁ <;> cases Atom.eval a₂ <;> rfl
  | .fst a => by
      simp only [ιA, Atom₅.eval, Atom.eval, eval_ι a]
      cases Atom.eval a with
      | none => rfl
      | some w => cases w <;> rfl
  | .snd a => by
      simp only [ιA, Atom₅.eval, Atom.eval, eval_ι a]
      cases Atom.eval a with
      | none => rfl
      | some w => cases w <;> rfl
  | .inl _ a => by
      simp only [ιA, Atom₅.eval, Atom.eval, eval_ι a]
      cases Atom.eval a <;> rfl
  | .inr _ a => by
      simp only [ιA, Atom₅.eval, Atom.eval, eval_ι a]
      cases Atom.eval a <;> rfl
theorem evalL_ι : ∀ as : List Atom₂, Atom₅.evalL (ιL as) = (Atom.evalL as).map ιL
  | [] => rfl
  | a :: as => by
      simp only [ιL, Atom₅.evalL, Atom.evalL, eval_ι a, evalL_ι as]
      cases Atom.eval a <;> cases Atom.evalL as <;> rfl
end

/-! ## The operations commute with ι. -/

theorem opStep_inv {o : Op} {vs : List Atom₂} {σ : Store} {v : Atom₂} {σ' : Store} (h : opStep o vs σ = some (v, σ')) :
    ∀ a ∈ vs, ∃ c, a = .const c := by
  unfold opStep at h
  split at h <;> simp_all [Option.map_eq_some_iff] <;> grind

theorem mapM_lowerV_ι : ∀ vs : List Atom₂, (∀ a ∈ vs, ∃ c, a = .const c) → (ιL vs).mapM lowerV = some vs
  | [], _ => rfl
  | a :: vs, h => by
      obtain ⟨c, rfl⟩ := h a (by simp)
      simp only [ιL, ιA, List.mapM_cons, lowerV, mapM_lowerV_ι vs (fun b hb => h b (by simp [hb]))]
      rfl

theorem mapM_lowerV_ι_cases : ∀ vs : List Atom₂, (ιL vs).mapM lowerV = some vs ∨ (ιL vs).mapM lowerV = none
  | [] => .inl rfl
  | a :: vs => by
      rcases mapM_lowerV_ι_cases vs with h | h <;> cases a <;> simp [ιL, ιA, List.mapM_cons, lowerV, h]

theorem opStep₅_ι (o : Op) (vs : List Atom₂) (σ : Store) :
    opStep₅ o (ιL vs) σ = (opStep o vs σ).map fun p => (ιA p.1, p.2) := by
  simp only [opStep₅]
  rcases mapM_lowerV_ι_cases vs with h | h
  · rw [h, Option.bind_some]
  · rw [h, Option.bind_none]
    cases hs : opStep o vs σ with
    | none => rfl
    | some p =>
        obtain ⟨v, σ'⟩ := p
        rw [mapM_lowerV_ι vs (opStep_inv hs)] at h
        cases h

/-! ## Inversions of ι. -/

theorem eval_ι_inv {a : Atom₂} {v : Atom₅} (h : Atom₅.eval (ιA a) = some v) : ∃ w, Atom.eval a = some w ∧ v = ιA w := by
  rw [eval_ι] at h
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨w, hw, rfl⟩

theorem evalL_ι_inv {as : List Atom₂} {vs : List Atom₅} (h : Atom₅.evalL (ιL as) = some vs) :
    ∃ ws, Atom.evalL as = some ws ∧ vs = ιL ws := by
  rw [evalL_ι] at h
  obtain ⟨ws, hw, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨ws, hw, rfl⟩

theorem ιA_lam_inv {w : Atom₂} {τ e} (h : ιA w = .lam τ 0 e) : ∃ τ₀ e₀, w = .lam τ₀ e₀ ∧ e = ιE e₀ := by
  cases w <;> simp [ιA] at h
  exact ⟨_, _, rfl, h.2.symm⟩

theorem ιA_fix_inv {w : Atom₂} {τ₁ τ₂ e} (h : ιA w = .fix τ₁ 0 τ₂ e) :
    ∃ τ₁' τ₂' e₀, w = .fix τ₁' τ₂' e₀ ∧ τ₁ = ιT τ₁' ∧ τ₂ = ιT τ₂' ∧ e = ιE e₀ := by
  cases w <;> simp [ιA] at h
  exact ⟨_, _, _, rfl, h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem ιA_const_inv {w : Atom₂} {c} (h : ιA w = .const c) : w = .const c := by
  cases w <;> simp [ιA] at h
  rw [h]

theorem ιA_inl_inv {w : Atom₂} {τ v} (h : ιA w = .inl τ v) : ∃ τ₀ v₀, w = .inl τ₀ v₀ ∧ v = ιA v₀ := by
  cases w <;> simp [ιA] at h
  exact ⟨_, _, rfl, h.2.symm⟩

theorem ιA_inr_inv {w : Atom₂} {τ v} (h : ιA w = .inr τ v) : ∃ τ₀ v₀, w = .inr τ₀ v₀ ∧ v = ιA v₀ := by
  cases w <;> simp [ιA] at h
  exact ⟨_, _, rfl, h.2.symm⟩

/-! ## CE, forward: every ⟶₂ step is a ⟶₅ step of the embedded configuration. -/

theorem ce_pure {e e' : Tm₂} (h : Step e e') (σ : Store) : Step₅ (ιE e, σ) (ιE e', σ) := by
  induction h with
  | letRet hv => rw [ιE_subst]; exact .letRet (by rw [eval_ι, hv]; rfl)
  | letStep _ ih => exact .letStep ih
  | appLam h₁ h₂ => rw [ιE_subst]; exact .appLam (by rw [eval_ι, h₁]; rfl) (by rw [eval_ι, h₂]; rfl)
  | appFix h₁ h₂ =>
      rw [ιE_subst, ιE_subst]; exact .appFix (by rw [eval_ι, h₁]; rfl) (by rw [eval_ι, h₂]; rfl)
  | iteT h₁ h₂ => exact .iteT (by rw [eval_ι, h₁]; rfl) h₂
  | iteF h₁ h₂ => exact .iteF (by rw [eval_ι, h₁]; rfl) h₂
  | caseL h₁ => rw [ιE_subst]; exact .caseL (by rw [eval_ι, h₁]; rfl)
  | caseR h₁ => rw [ιE_subst]; exact .caseR (by rw [eval_ι, h₁]; rfl)

theorem ce_fwd {c c' : Config} (h : Step₂ c c') : Step₅ (ιE c.1, c.2) (ιE c'.1, c'.2) := by
  induction h with
  | pure hs => exact ce_pure hs _
  | letStep _ ih => exact .letStep ih
  | op hvs hop =>
      rw [ιE_subst]
      exact .op (by rw [evalL_ι, hvs]; rfl) (by rw [opStep₅_ι, hop]; rfl)

/-! ## CE, backward: every ⟶₅ step of an embedded configuration IS an embedded ⟶₂ step. -/

theorem ce_bwd {c c' : Config₅} (h : Step₅ c c') :
    ∀ (e : Tm₂) (σ : Store), c = (ιE e, σ) → ∃ e' σ', Step₂ (e, σ) (e', σ') ∧ c' = (ιE e', σ') := by
  induction h with
  | letRet hv =>
      intro e σ hc
      cases e <;> simp [ιE] at hc
      obtain ⟨⟨rfl, he₁, rfl⟩, rfl⟩ := hc
      rename_i e₁ _
      cases e₁ <;> simp [ιE] at he₁
      subst he₁
      obtain ⟨w, hw, rfl⟩ := eval_ι_inv hv
      exact ⟨_, _, .pure (.letRet hw), by rw [ιE_subst]⟩
  | letStep _ ih =>
      intro e σ hc
      cases e <;> simp [ιE] at hc
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
      obtain ⟨e₁', σ', hs, hc'⟩ := ih _ _ rfl
      simp only [Prod.mk.injEq] at hc'
      obtain ⟨rfl, rfl⟩ := hc'
      exact ⟨_, _, .letStep hs, rfl⟩
  | op hvs hop =>
      intro e σ hc
      cases e <;> simp [ιE] at hc
      obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := hc
      obtain ⟨ws, hws, rfl⟩ := evalL_ι_inv hvs
      rw [opStep₅_ι] at hop
      obtain ⟨⟨v₀, σ'⟩, hs, he⟩ := Option.map_eq_some_iff.mp hop
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, _, .op hws hs, by rw [ιE_subst]⟩
  | appLam h₁ h₂ =>
      intro e σ hc
      cases e <;> simp [ιE] at hc
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
      obtain ⟨w₁, hw₁, hι₁⟩ := eval_ι_inv h₁
      obtain ⟨τ₀, e₀, rfl, rfl⟩ := ιA_lam_inv hι₁.symm
      obtain ⟨w₂, hw₂, rfl⟩ := eval_ι_inv h₂
      exact ⟨_, _, .pure (.appLam hw₁ hw₂), by rw [ιE_subst]⟩
  | appFix h₁ h₂ =>
      intro e σ hc
      cases e <;> simp [ιE] at hc
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
      obtain ⟨w₁, hw₁, hι₁⟩ := eval_ι_inv h₁
      obtain ⟨τ₁', τ₂', e₀, rfl, rfl, rfl, rfl⟩ := ιA_fix_inv hι₁.symm
      obtain ⟨w₂, hw₂, rfl⟩ := eval_ι_inv h₂
      exact ⟨_, _, .pure (.appFix hw₁ hw₂), by rw [ιE_subst, ιE_subst]; rfl⟩
  | iteT h₁ h₂ =>
      intro e σ hc
      cases e <;> simp [ιE] at hc
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
      obtain ⟨w, hw, hι⟩ := eval_ι_inv h₁
      obtain rfl := ιA_const_inv hι.symm
      exact ⟨_, _, .pure (.iteT hw h₂), rfl⟩
  | iteF h₁ h₂ =>
      intro e σ hc
      cases e <;> simp [ιE] at hc
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
      obtain ⟨w, hw, hι⟩ := eval_ι_inv h₁
      obtain rfl := ιA_const_inv hι.symm
      exact ⟨_, _, .pure (.iteF hw h₂), rfl⟩
  | caseL h₁ =>
      intro e σ hc
      cases e <;> simp [ιE] at hc
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
      obtain ⟨w, hw, hι⟩ := eval_ι_inv h₁
      obtain ⟨τ₀, v₀, rfl, rfl⟩ := ιA_inl_inv hι.symm
      exact ⟨_, _, .pure (.caseL hw), by rw [ιE_subst]⟩
  | caseR h₁ =>
      intro e σ hc
      cases e <;> simp [ιE] at hc
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
      obtain ⟨w, hw, hι⟩ := eval_ι_inv h₁
      obtain ⟨τ₀, v₀, rfl, rfl⟩ := ιA_inr_inv hι.symm
      exact ⟨_, _, .pure (.caseR hw), by rw [ιE_subst]⟩
  | appKLam _ _ _ _ => intro e σ hc; cases e <;> simp [ιE] at hc
  | appKFix _ _ _ _ => intro e σ hc; cases e <;> simp [ιE] at hc
  | letKRet _ _ _ => intro e σ hc; cases e <;> simp [ιE] at hc
  | letRetK0 _ =>
      intro e σ hc
      cases e <;> simp [ιE] at hc
      obtain ⟨⟨rfl, he₁, rfl⟩, rfl⟩ := hc
      rename_i e₁ _
      cases e₁ <;> simp [ιE] at he₁
  | letKRet0 _ => intro e σ hc; cases e <;> simp [ιE] at hc
  | letKStep _ _ => intro e σ hc; cases e <;> simp [ιE] at hc

/-- LV3 on ⟶, stated whole: an embedded L2 configuration steps under ⟶₅ to c' iff it steps under ⟶₂ to a configuration whose
  embedding is c'. -/
theorem ce_step (e : Tm₂) (σ : Store) (c' : Config₅) :
    Step₅ (ιE e, σ) c' ↔ ∃ e' σ', Step₂ (e, σ) (e', σ') ∧ c' = (ιE e', σ') := by
  constructor
  · intro h; exact ce_bwd h e σ rfl
  · rintro ⟨e', σ', hs, rfl⟩; exact ce_fwd hs

end VIRL5
