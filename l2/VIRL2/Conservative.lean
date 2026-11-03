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

end VIRL2
