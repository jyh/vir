/-
  O95 layer L2, Lean arm. OBJECT-L2 §7 = OBJECT-L1 §8: the L1 → L2 CONSERVATIVE EXTENSION, proved WITHOUT EDITING ANY L1
  DEFINITION (W8 / Y2). An L1 program is read in L2 through the signature embedding ι : Σ₁ → Σ₂ (B₁ ⊆ B₂ by `BTy.ofL1`,
  constants by `Const.ofL1`, P₁ = P₂, O₁ = ∅). This file: ι on types and terms, and its commutation with evaluation and
  substitution (the lemmas clause 2 is paid with, as amend-13 W8 predicted for Lean).
-/
import VIRL2.Adequacy2
import VIRL2.Typing2

namespace VIRL2
open VIRL1

abbrev Tm₁ := Tm L1.S₁
abbrev Atom₁ := Atom L1.S₁
abbrev Ty₁ := Ty L1.S₁.B

def embT : Ty₁ → Ty₂
  | .base b => .base (BTy.ofL1 b)
  | .arr t u => .arr (embT t) (embT u)
  | .prod t u => .prod (embT t) (embT u)
  | .sum t u => .sum (embT t) (embT u)

mutual
def embA : Atom₁ → Atom₂
  | .var n => .var n
  | .const c => .const (Const.ofL1 c)
  | .prim p as => .prim (S := S₂) p (embL as)
  | .lam τ e => .lam (embT τ) (embE e)
  | .fix τ₁ τ₂ e => .fix (embT τ₁) (embT τ₂) (embE e)
  | .pair a b => .pair (embA a) (embA b)
  | .fst a => .fst (embA a)
  | .snd a => .snd (embA a)
  | .inl τ a => .inl (embT τ) (embA a)
  | .inr τ a => .inr (embT τ) (embA a)
def embL : List Atom₁ → List Atom₂
  | [] => []
  | a :: as => embA a :: embL as
def embE : Tm₁ → Tm₂
  | .ret a => .ret (embA a)
  | .letE τ e₁ e₂ => .letE (embT τ) (embE e₁) (embE e₂)
  | .letOp o _ _ _ => nomatch (o : Empty)
  | .app a b => .app (embA a) (embA b)
  | .ite a e₁ e₂ => .ite (embA a) (embE e₁) (embE e₂)
  | .case a e₁ e₂ => .case (embA a) (embE e₁) (embE e₂)
end

theorem embL_map (as : List Atom₁) : embL as = as.map embA := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [embL, ih]

/-! ## ι commutes with substitution -/
mutual
theorem embA_subst : ∀ (a : Atom₁) (k : Nat) (v : Atom₁), embA (a.subst k v) = (embA a).subst k (embA v)
  | .var n, k, v => by
    simp only [Atom.subst, embA]; split_ifs <;> rfl
  | .const c, _, _ => rfl
  | .prim p as, k, v => by simp only [Atom.subst, embA, embL_substL as k v]
  | .lam τ e, k, v => by simp only [Atom.subst, embA, embE_subst e (k + 1) v]
  | .fix τ₁ τ₂ e, k, v => by simp only [Atom.subst, embA, embE_subst e (k + 2) v]
  | .pair a b, k, v => by simp only [Atom.subst, embA, embA_subst a k v, embA_subst b k v]
  | .fst a, k, v => by simp only [Atom.subst, embA, embA_subst a k v]
  | .snd a, k, v => by simp only [Atom.subst, embA, embA_subst a k v]
  | .inl τ a, k, v => by simp only [Atom.subst, embA, embA_subst a k v]
  | .inr τ a, k, v => by simp only [Atom.subst, embA, embA_subst a k v]
theorem embL_substL : ∀ (as : List Atom₁) (k : Nat) (v : Atom₁), embL (Atom.substL k v as) = Atom.substL k (embA v) (embL as)
  | [], _, _ => rfl
  | a :: as, k, v => by simp only [Atom.substL, embL, embA_subst a k v, embL_substL as k v]
theorem embE_subst : ∀ (e : Tm₁) (k : Nat) (v : Atom₁), embE (e.subst k v) = (embE e).subst k (embA v)
  | .ret a, k, v => by simp only [Tm.subst, embE, embA_subst a k v]
  | .letE τ e₁ e₂, k, v => by simp only [Tm.subst, embE, embE_subst e₁ k v, embE_subst e₂ (k + 1) v]
  | .letOp o _ _ _, _, _ => nomatch (o : Empty)
  | .app a b, k, v => by simp only [Tm.subst, embE, embA_subst a k v, embA_subst b k v]
  | .ite a e₁ e₂, k, v => by simp only [Tm.subst, embE, embA_subst a k v, embE_subst e₁ k v, embE_subst e₂ k v]
  | .case a e₁ e₂, k, v => by
    simp only [Tm.subst, embE, embA_subst a k v, embE_subst e₁ (k + 1) v, embE_subst e₂ (k + 1) v]
end

/-! ## ι commutes with evaluation -/
theorem toL1_ofL1 (c : L1.Const) : Const.toL1 (Const.ofL1 c) = some c := by cases c <;> rfl

theorem mapM_toL1 (cs : List L1.Const) : (cs.map Const.ofL1).mapM Const.toL1 = some cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [List.mapM_cons, toL1_ofL1, ih]

theorem constsOf_emb : ∀ (vs : List Atom₁), constsOf (vs.map embA) = (constsOf vs).map (List.map Const.ofL1)
  | [] => rfl
  | .const c :: vs => by
    simp only [List.map, constsOf, embA, constsOf_emb vs]
    cases constsOf vs <;> rfl
  | .var _ :: _ | .prim _ _ :: _ | .lam _ _ :: _ | .fix _ _ _ :: _ | .pair _ _ :: _ | .fst _ :: _ | .snd _ :: _
  | .inl _ _ :: _ | .inr _ _ :: _ => rfl

theorem pInterp_emb (p : L1.Prim) (cs : List L1.Const) :
    pInterp p (cs.map Const.ofL1) = (L1.Prim.interp p cs).map Const.ofL1 := by
  unfold pInterp; rw [mapM_toL1]; rfl

mutual
theorem embA_eval : ∀ (a : Atom₁), (embA a).eval = (a.eval).map embA
  | .var _ => rfl
  | .const _ => rfl
  | .prim p as => by
    simp only [embA, Atom.eval]
    rw [embL_evalL as]
    cases Atom.evalL as with
    | none => rfl
    | some vs =>
      simp only [Option.map_some, Option.bind_some]
      rw [constsOf_emb]
      cases constsOf vs with
      | none => rfl
      | some cs =>
        simp only [Option.map_some, Option.bind_some]
        change Option.map (Atom.const (S := S₂)) (pInterp p (List.map Const.ofL1 cs)) = _
        rw [pInterp_emb]
        change _ = Option.map embA (Option.map (Atom.const (S := L1.S₁)) (L1.Prim.interp p cs))
        cases L1.Prim.interp p cs <;> rfl
  | .lam _ _ => rfl
  | .fix _ _ _ => rfl
  | .pair a b => by
    simp only [embA, Atom.eval, embA_eval a, embA_eval b]
    cases Atom.eval a <;> cases Atom.eval b <;> rfl
  | .fst a => by
    simp only [embA, Atom.eval, embA_eval a]
    cases Atom.eval a with
    | none => rfl
    | some w => cases w <;> rfl
  | .snd a => by
    simp only [embA, Atom.eval, embA_eval a]
    cases Atom.eval a with
    | none => rfl
    | some w => cases w <;> rfl
  | .inl τ a => by simp only [embA, Atom.eval, embA_eval a]; cases Atom.eval a <;> rfl
  | .inr τ a => by simp only [embA, Atom.eval, embA_eval a]; cases Atom.eval a <;> rfl
theorem embL_evalL : ∀ (as : List Atom₁), Atom.evalL (embL as) = (Atom.evalL as).map (List.map embA)
  | [] => rfl
  | a :: as => by
    simp only [embL, Atom.evalL, embA_eval a, embL_evalL as]
    cases Atom.eval a <;> cases Atom.evalL as <;> rfl
end

theorem toBool_emb (c : L1.Const) : Const.toBool (Const.ofL1 c) = L1.Const.toBool c := by cases c <;> rfl

/-! ## ι is injective -/
theorem embT_inj : ∀ {t u : Ty₁}, embT t = embT u → t = u
  | .base a, .base b, h => by cases a <;> cases b <;> first | rfl | simp [embT, BTy.ofL1] at h
  | .arr t₁ t₂, .arr u₁ u₂, h => by simp only [embT, Ty.arr.injEq] at h; rw [embT_inj h.1, embT_inj h.2]
  | .prod t₁ t₂, .prod u₁ u₂, h => by simp only [embT, Ty.prod.injEq] at h; rw [embT_inj h.1, embT_inj h.2]
  | .sum t₁ t₂, .sum u₁ u₂, h => by simp only [embT, Ty.sum.injEq] at h; rw [embT_inj h.1, embT_inj h.2]
  | .base _, .arr _ _, h | .base _, .prod _ _, h | .base _, .sum _ _, h | .arr _ _, .base _, h
  | .arr _ _, .prod _ _, h | .arr _ _, .sum _ _, h | .prod _ _, .base _, h | .prod _ _, .arr _ _, h
  | .prod _ _, .sum _ _, h | .sum _ _, .base _, h | .sum _ _, .arr _ _, h | .sum _ _, .prod _ _, h => by
    simp [embT] at h

theorem ofL1_inj {c d : L1.Const} (h : Const.ofL1 c = Const.ofL1 d) : c = d := by
  cases c <;> cases d <;> simp_all [Const.ofL1]

mutual
theorem embA_inj : ∀ {a b : Atom₁}, embA a = embA b → a = b
  | .var n, .var m, h => by simp only [embA, Atom.var.injEq] at h; rw [h]
  | .const c, .const d, h => by simp only [embA, Atom.const.injEq] at h; rw [ofL1_inj h]
  | .prim p as, .prim q bs, h => by
    simp only [embA, Atom.prim.injEq] at h; obtain ⟨rfl, h⟩ := h; rw [embL_inj h]
  | .lam τ e, .lam τ' e', h => by
    simp only [embA, Atom.lam.injEq] at h; rw [embT_inj h.1, embE_inj h.2]
  | .fix τ₁ τ₂ e, .fix τ₁' τ₂' e', h => by
    simp only [embA, Atom.fix.injEq] at h; rw [embT_inj h.1, embT_inj h.2.1, embE_inj h.2.2]
  | .pair a b, .pair a' b', h => by simp only [embA, Atom.pair.injEq] at h; rw [embA_inj h.1, embA_inj h.2]
  | .fst a, .fst a', h => by simp only [embA, Atom.fst.injEq] at h; rw [embA_inj h]
  | .snd a, .snd a', h => by simp only [embA, Atom.snd.injEq] at h; rw [embA_inj h]
  | .inl τ a, .inl τ' a', h => by simp only [embA, Atom.inl.injEq] at h; rw [embT_inj h.1, embA_inj h.2]
  | .inr τ a, .inr τ' a', h => by simp only [embA, Atom.inr.injEq] at h; rw [embT_inj h.1, embA_inj h.2]
  | .var _, .const _, h | .var _, .prim _ _, h | .var _, .lam _ _, h | .var _, .fix _ _ _, h | .var _, .pair _ _, h
  | .var _, .fst _, h | .var _, .snd _, h | .var _, .inl _ _, h | .var _, .inr _ _, h
  | .const _, .var _, h | .const _, .prim _ _, h | .const _, .lam _ _, h | .const _, .fix _ _ _, h
  | .const _, .pair _ _, h | .const _, .fst _, h | .const _, .snd _, h | .const _, .inl _ _, h | .const _, .inr _ _, h
  | .prim _ _, .var _, h | .prim _ _, .const _, h | .prim _ _, .lam _ _, h | .prim _ _, .fix _ _ _, h
  | .prim _ _, .pair _ _, h | .prim _ _, .fst _, h | .prim _ _, .snd _, h | .prim _ _, .inl _ _, h | .prim _ _, .inr _ _, h
  | .lam _ _, .var _, h | .lam _ _, .const _, h | .lam _ _, .prim _ _, h | .lam _ _, .fix _ _ _, h
  | .lam _ _, .pair _ _, h | .lam _ _, .fst _, h | .lam _ _, .snd _, h | .lam _ _, .inl _ _, h | .lam _ _, .inr _ _, h
  | .fix _ _ _, .var _, h | .fix _ _ _, .const _, h | .fix _ _ _, .prim _ _, h | .fix _ _ _, .lam _ _, h
  | .fix _ _ _, .pair _ _, h | .fix _ _ _, .fst _, h | .fix _ _ _, .snd _, h | .fix _ _ _, .inl _ _, h
  | .fix _ _ _, .inr _ _, h
  | .pair _ _, .var _, h | .pair _ _, .const _, h | .pair _ _, .prim _ _, h | .pair _ _, .lam _ _, h
  | .pair _ _, .fix _ _ _, h | .pair _ _, .fst _, h | .pair _ _, .snd _, h | .pair _ _, .inl _ _, h
  | .pair _ _, .inr _ _, h
  | .fst _, .var _, h | .fst _, .const _, h | .fst _, .prim _ _, h | .fst _, .lam _ _, h | .fst _, .fix _ _ _, h
  | .fst _, .pair _ _, h | .fst _, .snd _, h | .fst _, .inl _ _, h | .fst _, .inr _ _, h
  | .snd _, .var _, h | .snd _, .const _, h | .snd _, .prim _ _, h | .snd _, .lam _ _, h | .snd _, .fix _ _ _, h
  | .snd _, .pair _ _, h | .snd _, .fst _, h | .snd _, .inl _ _, h | .snd _, .inr _ _, h
  | .inl _ _, .var _, h | .inl _ _, .const _, h | .inl _ _, .prim _ _, h | .inl _ _, .lam _ _, h
  | .inl _ _, .fix _ _ _, h | .inl _ _, .pair _ _, h | .inl _ _, .fst _, h | .inl _ _, .snd _, h
  | .inl _ _, .inr _ _, h
  | .inr _ _, .var _, h | .inr _ _, .const _, h | .inr _ _, .prim _ _, h | .inr _ _, .lam _ _, h
  | .inr _ _, .fix _ _ _, h | .inr _ _, .pair _ _, h | .inr _ _, .fst _, h | .inr _ _, .snd _, h
  | .inr _ _, .inl _ _, h => by simp [embA] at h
theorem embL_inj : ∀ {as bs : List Atom₁}, embL as = embL bs → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by simp only [embL, List.cons.injEq] at h; rw [embA_inj h.1, embL_inj h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [embL] at h
theorem embE_inj : ∀ {e f : Tm₁}, embE e = embE f → e = f
  | .ret a, .ret b, h => by simp only [embE, Tm.ret.injEq] at h; rw [embA_inj h]
  | .letE τ e₁ e₂, .letE τ' f₁ f₂, h => by
    simp only [embE, Tm.letE.injEq] at h; rw [embT_inj h.1, embE_inj h.2.1, embE_inj h.2.2]
  | .app a b, .app a' b', h => by simp only [embE, Tm.app.injEq] at h; rw [embA_inj h.1, embA_inj h.2]
  | .ite a e₁ e₂, .ite a' f₁ f₂, h => by
    simp only [embE, Tm.ite.injEq] at h; rw [embA_inj h.1, embE_inj h.2.1, embE_inj h.2.2]
  | .case a e₁ e₂, .case a' f₁ f₂, h => by
    simp only [embE, Tm.case.injEq] at h; rw [embA_inj h.1, embE_inj h.2.1, embE_inj h.2.2]
  | .letOp o _ _ _, _, _ | _, .letOp o _ _ _, _ => nomatch (o : Empty)
  | .ret _, .letE _ _ _, h | .ret _, .app _ _, h | .ret _, .ite _ _ _, h | .ret _, .case _ _ _, h
  | .letE _ _ _, .ret _, h | .letE _ _ _, .app _ _, h | .letE _ _ _, .ite _ _ _, h | .letE _ _ _, .case _ _ _, h
  | .app _ _, .ret _, h | .app _ _, .letE _ _ _, h | .app _ _, .ite _ _ _, h | .app _ _, .case _ _ _, h
  | .ite _ _ _, .ret _, h | .ite _ _ _, .letE _ _ _, h | .ite _ _ _, .app _ _, h | .ite _ _ _, .case _ _ _, h
  | .case _ _ _, .ret _, h | .case _ _ _, .letE _ _ _, h | .case _ _ _, .app _ _, h | .case _ _ _, .ite _ _ _, h => by
    simp [embE] at h
end

/-! ## The step function: complete (stated here, for any Σ, without editing L1) and commuting with ι -/
theorem stepFn_complete {S : Sig} {e e' : Tm S} (h : Step e e') : stepFn e = some e' := by
  induction h with
  | letRet ha => simp [stepFn, ha]
  | @letStep τ e₁ e₁' e₂ hs ih =>
    cases e₁ with
    | ret a => cases hs
    | letOp => cases hs
    | _ => show Option.map _ (stepFn _) = _; rw [ih]; rfl
  | appLam h₁ h₂ => simp [stepFn, h₁, h₂]
  | appFix h₁ h₂ => simp [stepFn, h₁, h₂]
  | iteT ha hb => simp [stepFn, ha, hb]
  | iteF ha hb => simp [stepFn, ha, hb]
  | caseL ha => simp [stepFn, ha]
  | caseR ha => simp [stepFn, ha]

theorem stepFn_emb : ∀ (e : Tm₁), stepFn (embE e) = (stepFn e).map embE
  | .ret a => by simp [embE, stepFn]
  | .letE τ (.ret a) e₂ => by
    simp only [embE, stepFn, embA_eval, Option.map_map]
    congr 1; funext v; simp [embE_subst]
  | .letE τ (.letE τ' e₁ e₃) e₂ => by
    have ih := stepFn_emb (.letE τ' e₁ e₃)
    show Option.map _ (stepFn (embE (.letE τ' e₁ e₃))) = Option.map embE (Option.map _ (stepFn (.letE τ' e₁ e₃)))
    rw [ih, Option.map_map, Option.map_map]; rfl
  | .letE τ (.letOp o _ _ _) e₂ => nomatch (o : Empty)
  | .letE τ (.app a b) e₂ => by
    have ih := stepFn_emb (.app a b)
    show Option.map _ (stepFn (embE (.app a b))) = Option.map embE (Option.map _ (stepFn (.app a b)))
    rw [ih, Option.map_map, Option.map_map]; rfl
  | .letE τ (.ite a e₁ e₃) e₂ => by
    have ih := stepFn_emb (.ite a e₁ e₃)
    show Option.map _ (stepFn (embE (.ite a e₁ e₃))) = Option.map embE (Option.map _ (stepFn (.ite a e₁ e₃)))
    rw [ih, Option.map_map, Option.map_map]; rfl
  | .letE τ (.case a e₁ e₃) e₂ => by
    have ih := stepFn_emb (.case a e₁ e₃)
    show Option.map _ (stepFn (embE (.case a e₁ e₃))) = Option.map embE (Option.map _ (stepFn (.case a e₁ e₃)))
    rw [ih, Option.map_map, Option.map_map]; rfl
  | .letOp o _ _ _ => nomatch (o : Empty)
  | .app a b => by
    simp only [embE, stepFn, embA_eval]
    cases Atom.eval a with
    | none => rfl
    | some w =>
      cases Atom.eval b with
      | none => cases w <;> rfl
      | some v => cases w <;> simp [embA, embE_subst]
  | .ite a e₁ e₂ => by
    simp only [embE, stepFn, embA_eval]
    cases Atom.eval a with
    | none => rfl
    | some w =>
      cases w with
      | const c =>
        simp only [Option.map_some, embA]
        change (match Const.toBool (Const.ofL1 c) with
          | some true => some (embE e₁) | some false => some (embE e₂) | none => none) = _
        rw [toBool_emb]
        cases h : L1.Const.toBool c with
        | none => simp [L1.S₁, h]; rfl
        | some b => cases b <;> simp [L1.S₁, h] <;> exact ⟨_, rfl, rfl⟩
      | _ => rfl
  | .case a e₁ e₂ => by
    simp only [embE, stepFn, embA_eval]
    cases Atom.eval a with
    | none => rfl
    | some w => cases w <;> simp [embA, embE_subst]

/-! ## CLAUSE 2: the steps correspond, and the store is untouched -/

/-- No O₂ operation in evaluation position. -/
def NoOpHead : Tm₂ → Prop
  | .letE _ e₁ _ => NoOpHead e₁
  | .letOp .. => False
  | _ => True

theorem noOpHead_emb : ∀ (e : Tm₁), NoOpHead (embE e)
  | .letE _ e₁ _ => noOpHead_emb e₁
  | .letOp o _ _ _ => nomatch (o : Empty)
  | .ret _ | .app _ _ | .ite _ _ _ | .case _ _ _ => trivial

theorem step₂_pure_inv {e : Tm₂} {σ c} (hn : NoOpHead e) (h : Step₂ (e, σ) c) : ∃ e', Step e e' ∧ c = (e', σ) := by
  generalize hc : (e, σ) = c₀ at h
  induction h generalizing e σ with
  | pure hs => injection hc with h₁ h₂; subst h₁ h₂; exact ⟨_, hs, rfl⟩
  | letStep _ ih =>
    injection hc with h₁ h₂; subst h₁ h₂
    obtain ⟨e₁'', hs, heq⟩ := ih (by exact hn) rfl
    injection heq with h₁ h₂; subst h₁ h₂
    exact ⟨_, .letStep hs, rfl⟩
  | op => injection hc with h₁ h₂; subst h₁; exact hn.elim

theorem step_emb {e e' : Tm₁} (h : Step e e') : Step (embE e) (embE e') :=
  stepFn_sound (by rw [stepFn_emb, stepFn_complete h]; rfl)

theorem step_unemb {e : Tm₁} {e'' : Tm₂} (h : Step (embE e) e'') : ∃ e', Step e e' ∧ e'' = embE e' := by
  have h' := stepFn_complete h
  rw [stepFn_emb] at h'
  obtain ⟨e', h₁, h₂⟩ := Option.map_eq_some_iff.1 h'
  exact ⟨e', stepFn_sound h₁, h₂.symm⟩

/-- OBJECT-L1 §8 CLAUSE 2: `e ⟶₁ e′` iff `⟨ι e, σ⟩ ⟶₂ ⟨ι e′, σ⟩`, for every σ. -/
theorem conservative_steps {e e' : Tm₁} (σ : Store) : Step e e' ↔ Step₂ (embE e, σ) (embE e', σ) := by
  refine ⟨fun h => .pure (step_emb h), fun h => ?_⟩
  obtain ⟨e'', hs, heq⟩ := step₂_pure_inv (noOpHead_emb e) h
  injection heq with h₁; subst h₁
  obtain ⟨x, hx, hxe⟩ := step_unemb hs
  rw [embE_inj hxe.symm] at hx
  exact hx

theorem steps_emb {e e' : Tm₁} (σ : Store) (h : Steps e e') : Steps₂ (embE e, σ) (embE e', σ) := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.pure (step_emb s)) ih

theorem steps₂_unemb {e : Tm₁} {σ c} (h : Steps₂ (embE e, σ) c) : ∃ e', Steps e e' ∧ c = (embE e', σ) := by
  generalize hc : (embE e, σ) = c₀ at h
  induction h generalizing e with
  | refl => subst hc; exact ⟨e, .refl _, rfl⟩
  | step h₁ _ ih =>
    subst hc
    obtain ⟨e'', hs, rfl⟩ := step₂_pure_inv (noOpHead_emb e) h₁
    obtain ⟨x, hx, rfl⟩ := step_unemb hs
    obtain ⟨e', hs', rfl⟩ := ih rfl
    exact ⟨e', .step hx hs', rfl⟩

/-! ## CLAUSE 3: the meaning is L1's, paired with the unchanged store -/
theorem embE_eq_ret {e : Tm₁} {a : Atom₂} (h : embE e = .ret a) : ∃ a₁, e = .ret a₁ ∧ a = embA a₁ := by
  cases e with
  | ret a₁ => simp only [embE, Tm.ret.injEq] at h; exact ⟨a₁, rfl, h.symm⟩
  | letOp o _ _ _ => exact nomatch (o : Empty)
  | _ => simp [embE] at h

/-- OBJECT-L1 §8 CLAUSE 3: `⟦ι e⟧₂ σ = ⟦e⟧₁ >>= (c ↦ ⌊(ι c, σ)⌋)`, for every σ. -/
theorem conservative_den (e : Tm₁) (σ : Store) :
    den₂ (embE e, σ) = (den e).bind fun c => Part.some (embA c, σ) := by
  apply Part.ext; rintro ⟨v, σ'⟩
  rw [Part.mem_bind_iff]
  constructor
  · intro h
    obtain ⟨a, hs, ha⟩ := adequacy₂ h
    obtain ⟨e', hs₁, heq⟩ := steps₂_unemb hs
    injection heq with h₁ h₂; subst h₂
    obtain ⟨a₁, rfl, rfl⟩ := embE_eq_ret h₁.symm
    rw [embA_eval] at ha
    obtain ⟨v₁, hv₁, rfl⟩ := Option.map_eq_some_iff.1 ha
    exact ⟨v₁, by rw [den_of_steps hs₁ hv₁]; exact Part.mem_some _, Part.mem_some _⟩
  · rintro ⟨c, hc, hr⟩
    rw [Part.mem_some_iff] at hr; cases hr
    obtain ⟨a₁, hs₁, ha₁⟩ := adequacy hc
    have h := den₂_of_steps (steps_emb σ hs₁) (a := embA a₁) (v := embA c) (by rw [embA_eval, ha₁]; rfl)
    rw [h]; exact Part.mem_some _

/-! ## CLAUSE 1: the typing is preserved verbatim (⊢₁ e : τ implies ∅-masked ⊢₂ ι e : ι τ) -/
theorem hasCap_embT : ∀ (τ : Ty₁), hasCap (embT τ) = false
  | .base b => by cases b <;> rfl
  | .arr t u | .prod t u | .sum t u => by simp [embT, hasCap, hasCap_embT t, hasCap_embT u]

theorem embT_ne_cap (τ : Ty₁) : decide (embT τ = tcap) = false := by
  have := hasCap_embT τ
  rw [decide_eq_false_iff_not]; intro h; rw [h] at this; exact absurd this (by decide)

theorem mask_empty_rep (n : Nat) : Mask.empty (List.replicate n false) := by
  intro m h; rw [List.getElem?_replicate] at h; split_ifs at h <;> simp at h

theorem split_rep : ∀ (n : Nat), Split (List.replicate n false) (List.replicate n false) (List.replicate n false)
  | 0 => .nil
  | n + 1 => .none (split_rep n)

mutual
theorem typeA_emb : ∀ {Γ : Ctx L1.S₁} {a : Atom₁} {τ : Ty₁}, HasTypeA L1.E₁ Γ a τ → HasTypeA₂ (Γ.map embT) (embA a) (embT τ)
  | _, _, _, .var h => .var (by rw [List.getElem?_map, h]; rfl) (hasCap_embT _)
  | _, .const c, _, .const => by cases c <;> first | exact .int | exact .bool
  | _, .prim p as, _, .prim h => by
    have h' := typeL_emb h
    have e : List.map embT (List.map Ty.base (L1.S₁.pArgs p)) = List.map Ty.base (S₂.pArgs p) := by
      simp only [S₂, List.map_map]; rfl
    rw [e] at h'
    exact .prim h'
  | Γ, _, _, .lam (τ₁ := τ₁) (τ₂ := τ₂) h =>
    .lam (hasCap_embT τ₁) (hasCap_embT τ₂) (mask_empty_rep _) (by simp) (type_emb h)
  | Γ, _, _, .fix (τ₁ := τ₁) (τ₂ := τ₂) h =>
    .fix (hasCap_embT τ₁) (hasCap_embT τ₂) (mask_empty_rep _) (by simp) (type_emb h)
  | _, _, _, .pair h₁ h₂ => .pair (typeA_emb h₁) (typeA_emb h₂)
  | _, _, _, .fst h => .fst (typeA_emb h)
  | _, _, _, .snd h => .snd (typeA_emb h)
  | _, _, _, .inl (τ₂ := τ₂) h => .inl (hasCap_embT τ₂) (typeA_emb h)
  | _, _, _, .inr (τ₁ := τ₁) h => .inr (hasCap_embT τ₁) (typeA_emb h)
theorem typeL_emb : ∀ {Γ : Ctx L1.S₁} {as : List Atom₁} {τs : List Ty₁}, HasTypeL L1.E₁ Γ as τs →
    HasTypeL₂ (Γ.map embT) (embL as) (τs.map embT)
  | _, _, _, .nil => .nil
  | _, _, _, .cons h hs => .cons (typeA_emb h) (typeL_emb hs)
theorem type_emb : ∀ {Γ : Ctx L1.S₁} {e : Tm₁} {τ : Ty₁}, HasType L1.E₁ Γ e τ →
    HasType₂ (Γ.map embT) (List.replicate Γ.length false) (embE e) (embT τ)
  | _, _, _, .ret h => .ret (mask_empty_rep _) (typeA_emb h)
  | Γ, _, _, .letE (τ₁ := τ₁) h₁ h₂ => by
    have h₂' := type_emb h₂
    simp only [List.map_cons, List.length_cons, List.replicate_succ] at h₂'
    refine .letE (split_rep _) (.inr (hasCap_embT τ₁)) (type_emb h₁) ?_
    rw [embT_ne_cap]; exact h₂'
  | _, _, _, .letOp (o := o) _ _ => nomatch (o : Empty)
  | _, _, _, .app h₁ h₂ => .app (mask_empty_rep _) (typeA_emb h₁) (typeA_emb h₂)
  | _, _, _, .ite h h₁ h₂ => .ite (typeA_emb h) (type_emb h₁) (type_emb h₂)
  | _, _, _, .case h h₁ h₂ => .case (typeA_emb h) (type_emb h₁) (type_emb h₂)
end

/-- OBJECT-L1 §8 CLAUSE 1, for closed programs: `⊢₁ e : τ` implies `∅ ; ∅ ⊢₂ ι e : ι τ`. -/
theorem conservative_typing {e : Tm₁} {τ : Ty₁} (h : HasType L1.E₁ [] e τ) : HasType₂ [] [] (embE e) (embT τ) :=
  type_emb h

end VIRL2
