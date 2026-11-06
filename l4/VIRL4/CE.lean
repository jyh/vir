/-
  O95 layer L4, Lean arm (amend-21 Q7): THE CONSERVATIVE EXTENSION, on ⟶ (OBJECT-L4 H3 (a)), BOTH directions, through ι.
  A program with no `par`, `newlock`, `acquire` or `release` steps under ⟶₄ exactly as under ⟶₂, the lock table untouched.
  (Its ⊢₄ typing is its ⊢₂ typing: Typing4.lean.)
-/
import VIRL4.Step4

namespace VIRL4
open VIRL1 VIRL2

/-! ## Evaluation commutes with ι. -/

theorem constsOf₄_ι : ∀ vs : List Atom₂, constsOf₄ (ιL vs) = (constsOf vs).bind (·.mapM Const.toL1)
  | [] => rfl
  | v :: vs => by
      cases v with
      | const c =>
          have ih := constsOf₄_ι vs
          simp only [ιL, ιA, constsOf₄, constsOf, Const₄.toL1, ih]
          cases h₁ : Const.toL1 c <;> cases h₂ : constsOf vs <;> simp [List.mapM_cons, h₁]
          all_goals (cases List.mapM Const.toL1 ‹List S₂.C› <;> rfl)
      | _ => rfl

theorem toBool_ι (c : Const) : Const₄.toBool (.c2 c) = Const.toBool c := by
  cases c <;> rfl

mutual
theorem eval_ι : ∀ a : Atom₂, Atom₄.eval (ιA a) = (Atom.eval a).map ιA
  | .var _ => rfl
  | .const _ => rfl
  | .prim p as => by
      have ih := evalL_ι as
      simp only [ιA, Atom₄.eval, Atom.eval, ih]
      cases (Atom.evalL as) with
      | none => rfl
      | some vs =>
          simp only [Option.map_some, Option.bind_some, constsOf₄_ι]
          cases constsOf vs with
          | none => rfl
          | some cs =>
              simp only [Option.bind_some, S₂, pInterp]
              cases cs.mapM Const.toL1 with
              | none => rfl
              | some cs₁ =>
                  simp only [Option.bind_some]
                  cases L1.Prim.interp p cs₁ <;> rfl
  | .lam _ _ => rfl
  | .fix _ _ _ => rfl
  | .pair a₁ a₂ => by
      simp only [ιA, Atom₄.eval, Atom.eval, eval_ι a₁, eval_ι a₂]
      cases Atom.eval a₁ <;> cases Atom.eval a₂ <;> rfl
  | .fst a => by
      simp only [ιA, Atom₄.eval, Atom.eval, eval_ι a]
      cases Atom.eval a with
      | none => rfl
      | some w => cases w <;> rfl
  | .snd a => by
      simp only [ιA, Atom₄.eval, Atom.eval, eval_ι a]
      cases Atom.eval a with
      | none => rfl
      | some w => cases w <;> rfl
  | .inl _ a => by
      simp only [ιA, Atom₄.eval, Atom.eval, eval_ι a]
      cases Atom.eval a <;> rfl
  | .inr _ a => by
      simp only [ιA, Atom₄.eval, Atom.eval, eval_ι a]
      cases Atom.eval a <;> rfl
theorem evalL_ι : ∀ as : List Atom₂, Atom₄.evalL (ιL as) = (Atom.evalL as).map ιL
  | [] => rfl
  | a :: as => by
      simp only [ιL, Atom₄.evalL, Atom.evalL, eval_ι a, evalL_ι as]
      cases Atom.eval a <;> cases Atom.evalL as <;> rfl
end

/-! ## The operations commute with ι (O₂ only; the lock table is carried unchanged). -/

theorem opStep_inv {o : Op} {vs : List Atom₂} {σ : Store} {v : Atom₂} {σ' : Store} (h : opStep o vs σ = some (v, σ')) :
    (∀ a ∈ vs, ∃ c, a = .const c) ∧ ∃ c, v = .const c := by
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

theorem opStep₄_ι (o : Op) (vs : List Atom₂) (σ : Store) (L : List LockSt) :
    opStep₄ (.o2 o) (ιL vs) ⟨σ, L⟩ = (opStep o vs σ).map fun p => (ιA p.1, ⟨p.2, L⟩) := by
  simp only [opStep₄]
  rcases mapM_lowerV_ι_cases vs with h | h
  · rw [h, Option.bind_some]
    cases hs : opStep o vs σ with
    | none => rfl
    | some p =>
        obtain ⟨v, σ'⟩ := p
        obtain ⟨_, c, rfl⟩ := opStep_inv hs
        rfl
  · rw [h, Option.bind_none]
    cases hs : opStep o vs σ with
    | none => rfl
    | some p =>
        obtain ⟨v, σ'⟩ := p
        rw [mapM_lowerV_ι vs (opStep_inv hs).1] at h
        cases h

/-! ## Inversions of ι. -/

theorem eval_ι_inv {a : Atom₂} {v : Atom₄} (h : Atom₄.eval (ιA a) = some v) : ∃ w, Atom.eval a = some w ∧ v = ιA w := by
  rw [eval_ι] at h
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨w, hw, rfl⟩

theorem evalL_ι_inv {as : List Atom₂} {vs : List Atom₄} (h : Atom₄.evalL (ιL as) = some vs) :
    ∃ ws, Atom.evalL as = some ws ∧ vs = ιL ws := by
  rw [evalL_ι] at h
  obtain ⟨ws, hw, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨ws, hw, rfl⟩

theorem ιA_lam_inv {w : Atom₂} {τ e} (h : ιA w = .lam τ e) : ∃ τ₀ e₀, w = .lam τ₀ e₀ ∧ e = ιT e₀ := by
  cases w <;> simp [ιA] at h
  exact ⟨_, _, rfl, h.2.symm⟩

theorem ιA_fix_inv {w : Atom₂} {τ₁ τ₂ e} (h : ιA w = .fix τ₁ τ₂ e) :
    ∃ τ₁' τ₂' e₀, w = .fix τ₁' τ₂' e₀ ∧ τ₁ = Ty₄.ofTy2 τ₁' ∧ τ₂ = Ty₄.ofTy2 τ₂' ∧ e = ιT e₀ := by
  cases w <;> simp [ιA] at h
  exact ⟨_, _, _, rfl, h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem ιA_const_inv {w : Atom₂} {c} (h : ιA w = .const c) : ∃ c₀, w = .const c₀ ∧ c = .c2 c₀ := by
  cases w <;> simp [ιA] at h
  exact ⟨_, rfl, h.symm⟩

theorem ιA_inl_inv {w : Atom₂} {τ v} (h : ιA w = .inl τ v) : ∃ τ₀ v₀, w = .inl τ₀ v₀ ∧ v = ιA v₀ := by
  cases w <;> simp [ιA] at h
  exact ⟨_, _, rfl, h.2.symm⟩

theorem ιA_inr_inv {w : Atom₂} {τ v} (h : ιA w = .inr τ v) : ∃ τ₀ v₀, w = .inr τ₀ v₀ ∧ v = ιA v₀ := by
  cases w <;> simp [ιA] at h
  exact ⟨_, _, rfl, h.2.symm⟩

/-! ## CE, forward: every ⟶₂ step is a ⟶₄ step of the embedded configuration, for ANY lock table. -/

theorem ce_pure {e e' : Tm₂} (h : Step e e') (s : Store₄) : Step₄ (ιT e, s) (ιT e', s) := by
  induction h with
  | letRet hv =>
      rw [ιT_subst]; exact .letRet (by rw [eval_ι, hv]; rfl)
  | letStep _ ih => exact .letStep ih
  | appLam h₁ h₂ =>
      rw [ιT_subst]; exact .appLam (by rw [eval_ι, h₁]; rfl) (by rw [eval_ι, h₂]; rfl)
  | appFix h₁ h₂ =>
      rw [ιT_subst, ιT_subst]; exact .appFix (by rw [eval_ι, h₁]; rfl) (by rw [eval_ι, h₂]; rfl)
  | iteT h₁ h₂ => exact .iteT (by rw [eval_ι, h₁]; rfl) (by rw [toBool_ι]; exact h₂)
  | iteF h₁ h₂ => exact .iteF (by rw [eval_ι, h₁]; rfl) (by rw [toBool_ι]; exact h₂)
  | caseL h₁ => rw [ιT_subst]; exact .caseL (by rw [eval_ι, h₁]; rfl)
  | caseR h₁ => rw [ιT_subst]; exact .caseR (by rw [eval_ι, h₁]; rfl)

theorem ce_fwd {c c' : Config} (h : Step₂ c c') (L : List LockSt) :
    Step₄ (ιT c.1, ⟨c.2, L⟩) (ιT c'.1, ⟨c'.2, L⟩) := by
  induction h with
  | pure hs => exact ce_pure hs _
  | letStep _ ih => exact .letStep ih
  | op hvs hop =>
      rw [ιT_subst]
      exact .op (by rw [evalL_ι, hvs]; rfl) (by rw [opStep₄_ι, hop]; rfl)

/-! ## CE, backward: every ⟶₄ step of an embedded configuration IS an embedded ⟶₂ step, the lock table untouched. -/

theorem ce_bwd {c c' : Config₄} (h : Step₄ c c') :
    ∀ (e : Tm₂) (σ : Store) (L : List LockSt), c = (ιT e, ⟨σ, L⟩) →
      ∃ e' σ', Step₂ (e, σ) (e', σ') ∧ c' = (ιT e', ⟨σ', L⟩) := by
  induction h with
  | letRet hv =>
      intro e σ L hc
      cases e <;> simp [ιT] at hc
      obtain ⟨⟨rfl, he₁, rfl⟩, rfl⟩ := hc
      rename_i e₁ _
      cases e₁ <;> simp [ιT] at he₁
      subst he₁
      obtain ⟨w, hw, rfl⟩ := eval_ι_inv hv
      exact ⟨_, _, .pure (.letRet hw), by rw [ιT_subst]⟩
  | letStep _ ih =>
      intro e σ L hc
      cases e <;> simp [ιT] at hc
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
      obtain ⟨e₁', σ', hs, hc'⟩ := ih _ σ L rfl
      simp only [Prod.mk.injEq] at hc'
      obtain ⟨rfl, rfl⟩ := hc'
      exact ⟨_, _, .letStep hs, rfl⟩
  | appLam h₁ h₂ =>
      intro e σ L hc
      cases e <;> simp [ιT] at hc
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
      obtain ⟨w₁, hw₁, hι₁⟩ := eval_ι_inv h₁
      obtain ⟨τ₀, e₀, rfl, rfl⟩ := ιA_lam_inv hι₁.symm
      obtain ⟨w₂, hw₂, rfl⟩ := eval_ι_inv h₂
      exact ⟨_, _, .pure (.appLam hw₁ hw₂), by rw [ιT_subst]⟩
  | appFix h₁ h₂ =>
      intro e σ L hc
      cases e <;> simp [ιT] at hc
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
      obtain ⟨w₁, hw₁, hι₁⟩ := eval_ι_inv h₁
      obtain ⟨τ₁', τ₂', e₀, rfl, rfl, rfl, rfl⟩ := ιA_fix_inv hι₁.symm
      obtain ⟨w₂, hw₂, rfl⟩ := eval_ι_inv h₂
      exact ⟨_, _, .pure (.appFix hw₁ hw₂), by rw [ιT_subst, ιT_subst]; rfl⟩
  | iteT h₁ h₂ =>
      intro e σ L hc
      cases e <;> simp [ιT] at hc
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
      obtain ⟨w, hw, hι⟩ := eval_ι_inv h₁
      obtain ⟨c₀, rfl, rfl⟩ := ιA_const_inv hι.symm
      exact ⟨_, _, .pure (.iteT hw (by rw [toBool_ι] at h₂; exact h₂)), rfl⟩
  | iteF h₁ h₂ =>
      intro e σ L hc
      cases e <;> simp [ιT] at hc
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
      obtain ⟨w, hw, hι⟩ := eval_ι_inv h₁
      obtain ⟨c₀, rfl, rfl⟩ := ιA_const_inv hι.symm
      exact ⟨_, _, .pure (.iteF hw (by rw [toBool_ι] at h₂; exact h₂)), rfl⟩
  | caseL h₁ =>
      intro e σ L hc
      cases e <;> simp [ιT] at hc
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
      obtain ⟨w, hw, hι⟩ := eval_ι_inv h₁
      obtain ⟨τ₀, v₀, rfl, rfl⟩ := ιA_inl_inv hι.symm
      exact ⟨_, _, .pure (.caseL hw), by rw [ιT_subst]⟩
  | caseR h₁ =>
      intro e σ L hc
      cases e <;> simp [ιT] at hc
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
      obtain ⟨w, hw, hι⟩ := eval_ι_inv h₁
      obtain ⟨τ₀, v₀, rfl, rfl⟩ := ιA_inr_inv hι.symm
      exact ⟨_, _, .pure (.caseR hw), by rw [ιT_subst]⟩
  | op hvs hop =>
      intro e σ L hc
      cases e <;> simp [ιT] at hc
      obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := hc
      obtain ⟨ws, hws, rfl⟩ := evalL_ι_inv hvs
      rw [opStep₄_ι] at hop
      obtain ⟨⟨v₀, σ'⟩, hs, he⟩ := Option.map_eq_some_iff.mp hop
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, _, .op hws hs, by rw [ιT_subst]⟩
  | parL _ _ =>
      intro e σ L hc
      cases e <;> simp [ιT] at hc
  | parR _ _ =>
      intro e σ L hc
      cases e <;> simp [ιT] at hc
  | parDone _ _ =>
      intro e σ L hc
      cases e <;> simp [ιT] at hc

end VIRL4
