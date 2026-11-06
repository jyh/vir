/-
  O95 layer L4 (OBJECT-L4), Lean arm (amend-21). The syntax: Σ₄ and a FRESH mutual `Atom₄`/`Tm₄`.
  WHY FRESH (l4/DECLARATIONS-LEAN.md): `par e₁ e₂` is a TERM FORMER. L1's `Tm S` is a closed inductive whose ops take ATOMS only,
  and Q1 forbids editing it. So L4 restates L1's six expression formers plus `par` here, and every line of this file is the
  `L4.syntaxCopy` line of C5. `ι` embeds L2's terms; CE (Q7) is stated through it.
  Nothing here edits L1, L2 or L3: every name of theirs is imported.
-/
import VIRL3

namespace VIRL4
open VIRL1 VIRL2

/-- B₄ = B₂ ∪ {lock}. `lock` is NON-linear (OBJECT-L4 H2 (a)); `cap` stays linear. -/
inductive BTy₄ | int | bool | unit | cap | lock
  deriving DecidableEq, Repr

/-- C₄: L2's constants plus the runtime-only lock handles ⟨ℓ⟩ (a lock id). -/
inductive Const₄ | c2 (c : Const) | lockv (l : Nat)
  deriving DecidableEq, Repr

/-- O₄ = O₂ ∪ {newlock, acquire, release} (inputs/L4-programs.md §2). -/
inductive Op₄ | o2 (o : Op) | newlock | acquire | release
  deriving DecidableEq, Repr

def BTy₄.ofB2 : BTy → BTy₄
  | .int => .int | .bool => .bool | .unit => .unit | .cap => .cap

abbrev Ty₄ := Ty BTy₄

def Ty₄.ofTy2 : Ty BTy → Ty₄
  | .base b => .base (BTy₄.ofB2 b)
  | .arr τ₁ τ₂ => .arr (Ty₄.ofTy2 τ₁) (Ty₄.ofTy2 τ₂)
  | .prod τ₁ τ₂ => .prod (Ty₄.ofTy2 τ₁) (Ty₄.ofTy2 τ₂)
  | .sum τ₁ τ₂ => .sum (Ty₄.ofTy2 τ₁) (Ty₄.ofTy2 τ₂)

def t4int : Ty₄ := .base .int
def t4unit : Ty₄ := .base .unit
def t4cap : Ty₄ := .base .cap
def t4lock : Ty₄ := .base .lock

/-- O₄'s arities: O₂'s lifted, and newlock(c) : lock · acquire(ℓ) : cap · release(ℓ, c) : unit. -/
def Op₄.args : Op₄ → List Ty₄
  | .o2 o => (Op.args o).map Ty₄.ofTy2
  | .newlock => [t4cap]
  | .acquire => [t4lock]
  | .release => [t4lock, t4cap]

def Op₄.res : Op₄ → Ty₄
  | .o2 o => Ty₄.ofTy2 (Op.res o)
  | .newlock => t4lock
  | .acquire => t4cap
  | .release => t4unit

mutual
/-- Atoms: L1's ten formers, over Σ₄. -/
inductive Atom₄ where
  | var (n : Nat)
  | const (c : Const₄)
  | prim (p : L1.Prim) (as : List Atom₄)
  | lam (τ : Ty₄) (e : Tm₄)
  | fix (τ₁ τ₂ : Ty₄) (e : Tm₄)
  | pair (a₁ a₂ : Atom₄)
  | fst (a : Atom₄)
  | snd (a : Atom₄)
  | inl (τ₂ : Ty₄) (a : Atom₄)
  | inr (τ₁ : Ty₄) (a : Atom₄)
/-- Expressions: L1's six formers, over Σ₄, PLUS `par` (OBJECT-L4 H1 (a), read by erratum L4-E1): `let x₁:τ₁, x₂:τ₂ ⇐ par e₁ e₂ in e`,
  the two results BOUND one variable each (x₁ = #1, x₂ = #0 in e), never a pair, so no product carries a capability (R-a). -/
inductive Tm₄ where
  | ret (a : Atom₄)
  | letE (τ : Ty₄) (e₁ e₂ : Tm₄)
  | letOp (o : Op₄) (as : List Atom₄) (τ : Ty₄) (e : Tm₄)
  | app (a₁ a₂ : Atom₄)
  | ite (a : Atom₄) (e₁ e₂ : Tm₄)
  | case (a : Atom₄) (e₁ e₂ : Tm₄)
  | par (τ₁ τ₂ : Ty₄) (e₁ e₂ e : Tm₄)
end

/-! ## Substitution of a CLOSED value (L1's, restated; `par` binds two in its body). -/
mutual
def Atom₄.subst : Atom₄ → Nat → Atom₄ → Atom₄
  | .var n, k, v => if n < k then .var n else if n = k then v else .var (n - 1)
  | .const c, _, _ => .const c
  | .prim p as, k, v => .prim p (Atom₄.substL k v as)
  | .lam τ e, k, v => .lam τ (Tm₄.subst (k + 1) v e)
  | .fix τ₁ τ₂ e, k, v => .fix τ₁ τ₂ (Tm₄.subst (k + 2) v e)
  | .pair a₁ a₂, k, v => .pair (Atom₄.subst a₁ k v) (Atom₄.subst a₂ k v)
  | .fst a, k, v => .fst (Atom₄.subst a k v)
  | .snd a, k, v => .snd (Atom₄.subst a k v)
  | .inl τ a, k, v => .inl τ (Atom₄.subst a k v)
  | .inr τ a, k, v => .inr τ (Atom₄.subst a k v)
def Atom₄.substL (k : Nat) (v : Atom₄) : List Atom₄ → List Atom₄
  | [] => []
  | a :: as => Atom₄.subst a k v :: Atom₄.substL k v as
def Tm₄.subst (k : Nat) (v : Atom₄) : Tm₄ → Tm₄
  | .ret a => .ret (Atom₄.subst a k v)
  | .letE τ e₁ e₂ => .letE τ (Tm₄.subst k v e₁) (Tm₄.subst (k + 1) v e₂)
  | .letOp o as τ e => .letOp o (Atom₄.substL k v as) τ (Tm₄.subst (k + 1) v e)
  | .app a₁ a₂ => .app (Atom₄.subst a₁ k v) (Atom₄.subst a₂ k v)
  | .ite a e₁ e₂ => .ite (Atom₄.subst a k v) (Tm₄.subst k v e₁) (Tm₄.subst k v e₂)
  | .case a e₁ e₂ => .case (Atom₄.subst a k v) (Tm₄.subst (k + 1) v e₁) (Tm₄.subst (k + 1) v e₂)
  | .par τ₁ τ₂ e₁ e₂ e => .par τ₁ τ₂ (Tm₄.subst k v e₁) (Tm₄.subst k v e₂) (Tm₄.subst (k + 2) v e)
end

/-! ## Scoping: every variable is bound; `n` binders in scope. -/
mutual
def Atom₄.wf (n : Nat) : Atom₄ → Prop
  | .var m => m < n
  | .const _ => True
  | .prim _ as => Atom₄.wfL n as
  | .lam _ e => Tm₄.wf (n + 1) e
  | .fix _ _ e => Tm₄.wf (n + 2) e
  | .pair a₁ a₂ => Atom₄.wf n a₁ ∧ Atom₄.wf n a₂
  | .fst a | .snd a | .inl _ a | .inr _ a => Atom₄.wf n a
def Atom₄.wfL (n : Nat) : List Atom₄ → Prop
  | [] => True
  | a :: as => Atom₄.wf n a ∧ Atom₄.wfL n as
def Tm₄.wf (n : Nat) : Tm₄ → Prop
  | .ret a => Atom₄.wf n a
  | .letE _ e₁ e₂ => Tm₄.wf n e₁ ∧ Tm₄.wf (n + 1) e₂
  | .letOp _ as _ e => Atom₄.wfL n as ∧ Tm₄.wf (n + 1) e
  | .app a₁ a₂ => Atom₄.wf n a₁ ∧ Atom₄.wf n a₂
  | .ite a e₁ e₂ => Atom₄.wf n a ∧ Tm₄.wf n e₁ ∧ Tm₄.wf n e₂
  | .case a e₁ e₂ => Atom₄.wf n a ∧ Tm₄.wf (n + 1) e₁ ∧ Tm₄.wf (n + 1) e₂
  | .par _ _ e₁ e₂ e => Tm₄.wf n e₁ ∧ Tm₄.wf n e₂ ∧ Tm₄.wf (n + 2) e
end

/-! ## ι : L2's syntax into L4's (the embedding CE is stated through). -/
mutual
def ιA : Atom₂ → Atom₄
  | .var n => .var n
  | .const c => .const (.c2 c)
  | .prim p as => .prim p (ιL as)
  | .lam τ e => .lam (Ty₄.ofTy2 τ) (ιT e)
  | .fix τ₁ τ₂ e => .fix (Ty₄.ofTy2 τ₁) (Ty₄.ofTy2 τ₂) (ιT e)
  | .pair a₁ a₂ => .pair (ιA a₁) (ιA a₂)
  | .fst a => .fst (ιA a)
  | .snd a => .snd (ιA a)
  | .inl τ a => .inl (Ty₄.ofTy2 τ) (ιA a)
  | .inr τ a => .inr (Ty₄.ofTy2 τ) (ιA a)
def ιL : List Atom₂ → List Atom₄
  | [] => []
  | a :: as => ιA a :: ιL as
def ιT : Tm₂ → Tm₄
  | .ret a => .ret (ιA a)
  | .letE τ e₁ e₂ => .letE (Ty₄.ofTy2 τ) (ιT e₁) (ιT e₂)
  | .letOp o as τ e => .letOp (.o2 o) (ιL as) (Ty₄.ofTy2 τ) (ιT e)
  | .app a₁ a₂ => .app (ιA a₁) (ιA a₂)
  | .ite a e₁ e₂ => .ite (ιA a) (ιT e₁) (ιT e₂)
  | .case a e₁ e₂ => .case (ιA a) (ιT e₁) (ιT e₂)
end

/- ι commutes with substitution: the one lemma CE's step clause needs about syntax. -/
mutual
theorem ιA_subst : ∀ (a : Atom₂) (k : Nat) (v : Atom₂), ιA (a.subst k v) = (ιA a).subst k (ιA v)
  | .var n, k, v => by
      simp only [Atom.subst, ιA, Atom₄.subst]
      split_ifs <;> rfl
  | .const _, _, _ => rfl
  | .prim p as, k, v => by simp only [Atom.subst, ιA, Atom₄.subst, ιL_substL as k v]
  | .lam τ e, k, v => by simp only [Atom.subst, ιA, Atom₄.subst, ιT_subst e (k + 1) v]
  | .fix τ₁ τ₂ e, k, v => by simp only [Atom.subst, ιA, Atom₄.subst, ιT_subst e (k + 2) v]
  | .pair a₁ a₂, k, v => by simp only [Atom.subst, ιA, Atom₄.subst, ιA_subst a₁ k v, ιA_subst a₂ k v]
  | .fst a, k, v => by simp only [Atom.subst, ιA, Atom₄.subst, ιA_subst a k v]
  | .snd a, k, v => by simp only [Atom.subst, ιA, Atom₄.subst, ιA_subst a k v]
  | .inl τ a, k, v => by simp only [Atom.subst, ιA, Atom₄.subst, ιA_subst a k v]
  | .inr τ a, k, v => by simp only [Atom.subst, ιA, Atom₄.subst, ιA_subst a k v]
theorem ιL_substL : ∀ (as : List Atom₂) (k : Nat) (v : Atom₂), ιL (Atom.substL k v as) = Atom₄.substL k (ιA v) (ιL as)
  | [], _, _ => rfl
  | a :: as, k, v => by simp only [Atom.substL, ιL, Atom₄.substL, ιA_subst a k v, ιL_substL as k v]
theorem ιT_subst : ∀ (e : Tm₂) (k : Nat) (v : Atom₂), ιT (e.subst k v) = (ιT e).subst k (ιA v)
  | .ret a, k, v => by simp only [Tm.subst, ιT, Tm₄.subst, ιA_subst a k v]
  | .letE τ e₁ e₂, k, v => by simp only [Tm.subst, ιT, Tm₄.subst, ιT_subst e₁ k v, ιT_subst e₂ (k + 1) v]
  | .letOp o as τ e, k, v => by simp only [Tm.subst, ιT, Tm₄.subst, ιL_substL as k v, ιT_subst e (k + 1) v]
  | .app a₁ a₂, k, v => by simp only [Tm.subst, ιT, Tm₄.subst, ιA_subst a₁ k v, ιA_subst a₂ k v]
  | .ite a e₁ e₂, k, v => by simp only [Tm.subst, ιT, Tm₄.subst, ιA_subst a k v, ιT_subst e₁ k v, ιT_subst e₂ k v]
  | .case a e₁ e₂, k, v => by
      simp only [Tm.subst, ιT, Tm₄.subst, ιA_subst a k v, ιT_subst e₁ (k + 1) v, ιT_subst e₂ (k + 1) v]
end

end VIRL4
