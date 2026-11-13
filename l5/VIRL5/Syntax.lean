/-
  O95 layer L5 (OBJECT-L5, J1 (a); erratum L5-E1), Lean arm (PREDICTIONS-amend-24). The syntax of L1′.
  l5/DECLARATIONS-LEAN.md (and its Addendum 1) declares everything here BEFORE this file: a FRESH type and term syntax beside L2's,
  because L1's `Ty`/`Tm` are closed inductives and L1′ adds a type former (the annotated arrow) and three term formers. The copy of
  L1's formers is the price counted on the line `L5.syntaxCopy` (LV1: L1–L4 are imported, never edited).
  * `Ty₅`: L1's formers over L2's base types, with `arr τ₁ k τ₂` = τ₁ →[k] τ₂ (k lent capabilities; k = 0 is L2's arrow).
  * `Atom₅`/`Tm₅`: L1's formers over S₂'s constants, prims and ops, plus `retK a ds`, `appK a₁ a₂ cs`, `letK τ j e₁ e₂`.
  Binders (index 0 innermost): `lam τ k e` binds x then the k lent capabilities (c_k = #0 … c₁ = #(k−1), x = #k);
  `fix τ₁ k τ₂ e` binds f, x, then the k capabilities (x = #k, f = #(k+1)); `letK τ j e₁ e₂` binds x then c₁′ … c_j′ in e₂
  (cᵢ′ = #(j−i), x = #j); `letE`, `letOp`, `case` as in L1.
-/
import VIRL2.Typing2

namespace VIRL5
open VIRL1 VIRL2

/-- Types of L1′: L2's, with the arrow carrying the number of capabilities it lends. -/
inductive Ty₅ where
  | base (b : BTy)
  | arr (τ₁ : Ty₅) (k : Nat) (τ₂ : Ty₅)
  | prod (τ₁ τ₂ : Ty₅)
  | sum (τ₁ τ₂ : Ty₅)
  deriving DecidableEq, Repr

def t5int : Ty₅ := .base .int
def t5bool : Ty₅ := .base .bool
def t5unit : Ty₅ := .base .unit
def t5cap : Ty₅ := .base .cap

/-- A type mentions `cap` somewhere other than as an arrow's count (L2's `hasCap`, carried up). -/
def Ty₅.hasCap : Ty₅ → Bool
  | .base b => decide (b = .cap)
  | .arr τ₁ _ τ₂ => τ₁.hasCap || τ₂.hasCap
  | .prod τ₁ τ₂ => τ₁.hasCap || τ₂.hasCap
  | .sum τ₁ τ₂ => τ₁.hasCap || τ₂.hasCap

mutual
inductive Atom₅ where
  | var (n : Nat)
  | const (c : Const)
  | prim (p : L1.Prim) (as : List Atom₅)
  | lam (τ : Ty₅) (k : Nat) (e : Tm₅)              -- λ(x:τ)[c₁ … c_k]. e
  | fix (τ₁ : Ty₅) (k : Nat) (τ₂ : Ty₅) (e : Tm₅)  -- fix f(x:τ₁)[c₁ … c_k]:τ₂. e
  | pair (a₁ a₂ : Atom₅)
  | fst (a : Atom₅)
  | snd (a : Atom₅)
  | inl (τ₂ : Ty₅) (a : Atom₅)
  | inr (τ₁ : Ty₅) (a : Atom₅)
inductive Tm₅ where
  | ret (a : Atom₅)
  | letE (τ : Ty₅) (e₁ e₂ : Tm₅)
  | letOp (o : Op) (as : List Atom₅) (τ : Ty₅) (e : Tm₅)
  | app (a₁ a₂ : Atom₅)
  | ite (a : Atom₅) (e₁ e₂ : Tm₅)
  | case (a : Atom₅) (e₁ e₂ : Tm₅)
  | retK (a : Atom₅) (ds : List Atom₅)             -- ret a [d₁ … d_k]       (L5-E1 (3))
  | appK (a₁ a₂ : Atom₅) (cs : List Atom₅)         -- a₁ a₂ [c₁ … c_k], a tail call that lends cs
  | letK (τ : Ty₅) (j : Nat) (e₁ e₂ : Tm₅)         -- let x:τ, c₁′ … c_j′ ⇐ e₁ in e₂   (L5-E1 (4))
end

/-! ## Substitution of a CLOSED value at index k (L1's, with the new binders counted). -/
mutual
def Atom₅.subst : Atom₅ → Nat → Atom₅ → Atom₅
  | .var n, k, v => if n < k then .var n else if n = k then v else .var (n - 1)
  | .const c, _, _ => .const c
  | .prim p as, k, v => .prim p (Atom₅.substL k v as)
  | .lam τ j e, k, v => .lam τ j (Tm₅.subst (k + j + 1) v e)
  | .fix τ₁ j τ₂ e, k, v => .fix τ₁ j τ₂ (Tm₅.subst (k + j + 2) v e)
  | .pair a₁ a₂, k, v => .pair (Atom₅.subst a₁ k v) (Atom₅.subst a₂ k v)
  | .fst a, k, v => .fst (Atom₅.subst a k v)
  | .snd a, k, v => .snd (Atom₅.subst a k v)
  | .inl τ a, k, v => .inl τ (Atom₅.subst a k v)
  | .inr τ a, k, v => .inr τ (Atom₅.subst a k v)
def Atom₅.substL (k : Nat) (v : Atom₅) : List Atom₅ → List Atom₅
  | [] => []
  | a :: as => Atom₅.subst a k v :: Atom₅.substL k v as
def Tm₅.subst (k : Nat) (v : Atom₅) : Tm₅ → Tm₅
  | .ret a => .ret (Atom₅.subst a k v)
  | .letE τ e₁ e₂ => .letE τ (Tm₅.subst k v e₁) (Tm₅.subst (k + 1) v e₂)
  | .letOp o as τ e => .letOp o (Atom₅.substL k v as) τ (Tm₅.subst (k + 1) v e)
  | .app a₁ a₂ => .app (Atom₅.subst a₁ k v) (Atom₅.subst a₂ k v)
  | .ite a e₁ e₂ => .ite (Atom₅.subst a k v) (Tm₅.subst k v e₁) (Tm₅.subst k v e₂)
  | .case a e₁ e₂ => .case (Atom₅.subst a k v) (Tm₅.subst (k + 1) v e₁) (Tm₅.subst (k + 1) v e₂)
  | .retK a ds => .retK (Atom₅.subst a k v) (Atom₅.substL k v ds)
  | .appK a₁ a₂ cs => .appK (Atom₅.subst a₁ k v) (Atom₅.subst a₂ k v) (Atom₅.substL k v cs)
  | .letK τ j e₁ e₂ => .letK τ j (Tm₅.subst k v e₁) (Tm₅.subst (k + j + 1) v e₂)
end

/-- Substitute a list of closed values for #0 … #(n−1), the LAST of the list at #0 (so `substAll [v_x, c₁, …, c_k] e` puts
  c_k at #0 and v_x at #k, the binder order of `lam`, `fix` (after f) and `letK`). -/
def Tm₅.substAll : List Atom₅ → Tm₅ → Tm₅
  | [], e => e
  | v :: vs, e => Tm₅.subst 0 v (Tm₅.substAll vs e)

/-- Values: L1's, over the new atoms. -/
def Atom₅.IsValue : Atom₅ → Prop
  | .const _ | .lam _ _ _ | .fix _ _ _ _ => True
  | .pair a₁ a₂ => Atom₅.IsValue a₁ ∧ Atom₅.IsValue a₂
  | .inl _ a | .inr _ a => Atom₅.IsValue a
  | _ => False

/-! ## The embedding of L2 (ι): every L2 arrow lends 0; ι is the identity on every L2 former. -/
def ιT : Ty₂ → Ty₅
  | .base b => .base b
  | .arr τ₁ τ₂ => .arr (ιT τ₁) 0 (ιT τ₂)
  | .prod τ₁ τ₂ => .prod (ιT τ₁) (ιT τ₂)
  | .sum τ₁ τ₂ => .sum (ιT τ₁) (ιT τ₂)

mutual
def ιA : Atom₂ → Atom₅
  | .var n => .var n
  | .const c => .const c
  | .prim p as => .prim p (ιL as)
  | .lam τ e => .lam (ιT τ) 0 (ιE e)
  | .fix τ₁ τ₂ e => .fix (ιT τ₁) 0 (ιT τ₂) (ιE e)
  | .pair a₁ a₂ => .pair (ιA a₁) (ιA a₂)
  | .fst a => .fst (ιA a)
  | .snd a => .snd (ιA a)
  | .inl τ a => .inl (ιT τ) (ιA a)
  | .inr τ a => .inr (ιT τ) (ιA a)
def ιL : List Atom₂ → List Atom₅
  | [] => []
  | a :: as => ιA a :: ιL as
def ιE : Tm₂ → Tm₅
  | .ret a => .ret (ιA a)
  | .letE τ e₁ e₂ => .letE (ιT τ) (ιE e₁) (ιE e₂)
  | .letOp o as τ e => .letOp o (ιL as) (ιT τ) (ιE e)
  | .app a₁ a₂ => .app (ιA a₁) (ιA a₂)
  | .ite a e₁ e₂ => .ite (ιA a) (ιE e₁) (ιE e₂)
  | .case a e₁ e₂ => .case (ιA a) (ιE e₁) (ιE e₂)
end

theorem ιT_injective : Function.Injective ιT := by
  intro a b h
  induction a generalizing b with
  | base x => cases b <;> simp_all [ιT]
  | arr a₁ a₂ ih₁ ih₂ =>
      cases b with
      | arr b₁ b₂ => simp only [ιT, Ty₅.arr.injEq] at h; rw [ih₁ h.1, ih₂ h.2.2]
      | _ => simp [ιT] at h
  | prod a₁ a₂ ih₁ ih₂ =>
      cases b with
      | prod b₁ b₂ => simp only [ιT, Ty₅.prod.injEq] at h; rw [ih₁ h.1, ih₂ h.2]
      | _ => simp [ιT] at h
  | sum a₁ a₂ ih₁ ih₂ =>
      cases b with
      | sum b₁ b₂ => simp only [ιT, Ty₅.sum.injEq] at h; rw [ih₁ h.1, ih₂ h.2]
      | _ => simp [ιT] at h

theorem ιT_hasCap (τ : Ty₂) : (ιT τ).hasCap = hasCap τ := by
  induction τ with
  | base b => cases b <;> rfl
  | arr _ _ ih₁ ih₂ => simp [ιT, Ty₅.hasCap, hasCap, ih₁, ih₂]
  | prod _ _ ih₁ ih₂ => simp [ιT, Ty₅.hasCap, hasCap, ih₁, ih₂]
  | sum _ _ ih₁ ih₂ => simp [ιT, Ty₅.hasCap, hasCap, ih₁, ih₂]

-- ι commutes with substitution (the lemma CE's step direction runs on).
mutual
theorem ιA_subst : ∀ (a : Atom₂) (k : Nat) (v : Atom₂), ιA (a.subst k v) = (ιA a).subst k (ιA v)
  | .var n, k, v => by
      simp only [Atom.subst, ιA, Atom₅.subst]; split_ifs <;> rfl
  | .const c, _, _ => rfl
  | .prim p as, k, v => by simp only [Atom.subst, ιA, Atom₅.subst, ιL_subst as k v]
  | .lam τ e, k, v => by simp only [Atom.subst, ιA, Atom₅.subst, ιE_subst e (k + 1) v, Nat.add_zero]
  | .fix τ₁ τ₂ e, k, v => by simp only [Atom.subst, ιA, Atom₅.subst, ιE_subst e (k + 2) v, Nat.add_zero]
  | .pair a₁ a₂, k, v => by simp only [Atom.subst, ιA, Atom₅.subst, ιA_subst a₁ k v, ιA_subst a₂ k v]
  | .fst a, k, v => by simp only [Atom.subst, ιA, Atom₅.subst, ιA_subst a k v]
  | .snd a, k, v => by simp only [Atom.subst, ιA, Atom₅.subst, ιA_subst a k v]
  | .inl τ a, k, v => by simp only [Atom.subst, ιA, Atom₅.subst, ιA_subst a k v]
  | .inr τ a, k, v => by simp only [Atom.subst, ιA, Atom₅.subst, ιA_subst a k v]
theorem ιL_subst : ∀ (as : List Atom₂) (k : Nat) (v : Atom₂), ιL (Atom.substL k v as) = Atom₅.substL k (ιA v) (ιL as)
  | [], _, _ => rfl
  | a :: as, k, v => by simp only [Atom.substL, ιL, Atom₅.substL, ιA_subst a k v, ιL_subst as k v]
theorem ιE_subst : ∀ (e : Tm₂) (k : Nat) (v : Atom₂), ιE (e.subst k v) = (ιE e).subst k (ιA v)
  | .ret a, k, v => by simp only [Tm.subst, ιE, Tm₅.subst, ιA_subst a k v]
  | .letE τ e₁ e₂, k, v => by simp only [Tm.subst, ιE, Tm₅.subst, ιE_subst e₁ k v, ιE_subst e₂ (k + 1) v]
  | .letOp o as τ e, k, v => by simp only [Tm.subst, ιE, Tm₅.subst, ιL_subst as k v, ιE_subst e (k + 1) v]
  | .app a₁ a₂, k, v => by simp only [Tm.subst, ιE, Tm₅.subst, ιA_subst a₁ k v, ιA_subst a₂ k v]
  | .ite a e₁ e₂, k, v => by simp only [Tm.subst, ιE, Tm₅.subst, ιA_subst a k v, ιE_subst e₁ k v, ιE_subst e₂ k v]
  | .case a e₁ e₂, k, v => by
      simp only [Tm.subst, ιE, Tm₅.subst, ιA_subst a k v, ιE_subst e₁ (k + 1) v, ιE_subst e₂ (k + 1) v]
end

end VIRL5
