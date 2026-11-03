/-
  O95 layer L1 (OBJECT-L1), Lean arm (PREDICTIONS-amend-13 E1–E4). STEPS 1–2: the terms, over a SIGNATURE parameter.
  E1: unscoped de Bruijn indices, extrinsic typing (VIRL1/Typing.lean). Index 0 is the innermost binder.
  Binders: `lam τ e` binds x (index 0) in e; `fix τ₁ τ₂ e` binds x (index 0) and f (index 1) in e; `letE τ e₁ e₂` binds x in
  e₂; `letOp o as τ e` binds x in e. Everything in this file is stated for an ARBITRARY signature `S` (OBJECT-L1 §1).
-/
namespace VIRL1

/-- The signature Σ = (B, P, O) of OBJECT-L1 §1, with the constants that name base-type values.
  `boolTy` and `toBool` are what the core's `if` needs from Σ: the base type it tests and how a constant reads as a boolean. -/
structure Sig where
  B : Type                       -- base types
  C : Type                       -- constants (the literals of base types)
  P : Type                       -- pure operators
  O : Type                       -- effect operators (L1: Empty)
  cTy : C → B
  pArgs : P → List B
  pRes : P → B
  pInterp : P → List C → Option C
  boolTy : B
  toBool : C → Option Bool

/-- Types (OBJECT-L1 §2): base types of Σ and arrows; W3 (ii) adds the product τ₁ × τ₂. -/
inductive Ty (B : Type) where
  | base (b : B)
  | arr (τ₁ τ₂ : Ty B)
  | prod (τ₁ τ₂ : Ty B)
  | sum (τ₁ τ₂ : Ty B)
  deriving DecidableEq, Repr

/-- The arities of effect operators are over types (OBJECT-L1 §1, O). Kept outside `Sig` because they mention `Ty`. -/
structure ESig (S : Sig) where
  oArgs : S.O → List (Ty S.B)
  oRes : S.O → Ty S.B

mutual
/-- Atoms (OBJECT-L1 §2): pure and total on well-typed closed terms. -/
inductive Atom (S : Sig) where
  | var (n : Nat)
  | const (c : S.C)
  | prim (p : S.P) (as : List (Atom S))
  | lam (τ : Ty S.B) (e : Tm S)                   -- λ(x:τ). e
  | fix (τ₁ τ₂ : Ty S.B) (e : Tm S)               -- fix f(x:τ₁):τ₂. e   (x = #0, f = #1)
  | pair (a₁ a₂ : Atom S)                         -- (a₁, a₂)
  | fst (a : Atom S)                              -- π₁ a
  | snd (a : Atom S)                              -- π₂ a
  | inl (τ₂ : Ty S.B) (a : Atom S)                -- inl[τ₂] a  (amend-17: the other summand annotated)
  | inr (τ₁ : Ty S.B) (a : Atom S)                -- inr[τ₁] a
/-- Expressions (OBJECT-L1 §2), in ANF: every operand is an atom. -/
inductive Tm (S : Sig) where
  | ret (a : Atom S)
  | letE (τ : Ty S.B) (e₁ e₂ : Tm S)             -- let x:τ = e₁ in e₂
  | letOp (o : S.O) (as : List (Atom S)) (τ : Ty S.B) (e : Tm S)   -- let x:τ ← o(as) in e
  | app (a₁ a₂ : Atom S)
  | ite (a : Atom S) (e₁ e₂ : Tm S)
  | case (a : Atom S) (e₁ e₂ : Tm S)              -- case a of inl x ⇒ e₁ | inr y ⇒ e₂   (x, y = #0 in their branch)
end

variable {S : Sig}

/-! ## Substitution of a CLOSED value (the only substitution the CBV semantics performs: values are closed, OBJECT-L1 §2).
`a.subst k v` (the matched atom FIRST, so dot notation binds it) replaces index k by v and lowers the indices above k by one. Since v is closed it is never shifted. -/
mutual
def Atom.subst : Atom S → Nat → Atom S → Atom S
  | .var n, k, v => if n < k then .var n else if n = k then v else .var (n - 1)
  | .const c, _, _ => .const c
  | .prim p as, k, v => .prim p (Atom.substL k v as)
  | .lam τ e, k, v => .lam τ (Tm.subst (k + 1) v e)
  | .fix τ₁ τ₂ e, k, v => .fix τ₁ τ₂ (Tm.subst (k + 2) v e)
  | .pair a₁ a₂, k, v => .pair (Atom.subst a₁ k v) (Atom.subst a₂ k v)
  | .fst a, k, v => .fst (Atom.subst a k v)
  | .snd a, k, v => .snd (Atom.subst a k v)
  | .inl τ a, k, v => .inl τ (Atom.subst a k v)
  | .inr τ a, k, v => .inr τ (Atom.subst a k v)
def Atom.substL (k : Nat) (v : Atom S) : List (Atom S) → List (Atom S)
  | [] => []
  | a :: as => Atom.subst a k v :: Atom.substL k v as
def Tm.subst (k : Nat) (v : Atom S) : Tm S → Tm S
  | .ret a => .ret (Atom.subst a k v)
  | .letE τ e₁ e₂ => .letE τ (Tm.subst k v e₁) (Tm.subst (k + 1) v e₂)
  | .letOp o as τ e => .letOp o (Atom.substL k v as) τ (Tm.subst (k + 1) v e)
  | .app a₁ a₂ => .app (Atom.subst a₁ k v) (Atom.subst a₂ k v)
  | .ite a e₁ e₂ => .ite (Atom.subst a k v) (Tm.subst k v e₁) (Tm.subst k v e₂)
  | .case a e₁ e₂ => .case (Atom.subst a k v) (Tm.subst (k + 1) v e₁) (Tm.subst (k + 1) v e₂)
end

/-! ## Well-formedness (step 2): every variable is bound; `n` binders in scope. -/
mutual
def Atom.wf (n : Nat) : Atom S → Prop
  | .var m => m < n
  | .const _ => True
  | .prim _ as => Atom.wfL n as
  | .lam _ e => Tm.wf (n + 1) e
  | .fix _ _ e => Tm.wf (n + 2) e
  | .pair a₁ a₂ => Atom.wf n a₁ ∧ Atom.wf n a₂
  | .fst a => Atom.wf n a
  | .snd a => Atom.wf n a
  | .inl _ a => Atom.wf n a
  | .inr _ a => Atom.wf n a
def Atom.wfL (n : Nat) : List (Atom S) → Prop
  | [] => True
  | a :: as => Atom.wf n a ∧ Atom.wfL n as
def Tm.wf (n : Nat) : Tm S → Prop
  | .ret a => Atom.wf n a
  | .letE _ e₁ e₂ => Tm.wf n e₁ ∧ Tm.wf (n + 1) e₂
  | .letOp _ as _ e => Atom.wfL n as ∧ Tm.wf (n + 1) e
  | .app a₁ a₂ => Atom.wf n a₁ ∧ Atom.wf n a₂
  | .ite a e₁ e₂ => Atom.wf n a ∧ Tm.wf n e₁ ∧ Tm.wf n e₂
  | .case a e₁ e₂ => Atom.wf n a ∧ Tm.wf (n + 1) e₁ ∧ Tm.wf (n + 1) e₂
end

/-- A PROGRAM is a closed, well-formed expression (OBJECT-L1 §3). -/
def Tm.IsProgram (e : Tm S) : Prop := Tm.wf 0 e

/-- Values (OBJECT-L1 §2): constants, λ and fix atoms; W3 (ii): a pair of values. -/
def Atom.IsValue : Atom S → Prop
  | .const _ | .lam _ _ | .fix _ _ _ => True
  | .pair a₁ a₂ => Atom.IsValue a₁ ∧ Atom.IsValue a₂
  | .inl _ a | .inr _ a => Atom.IsValue a
  | _ => False

/-! ## Display forms (step 2): OBJECT-L1 §2's concrete syntax, binders shown as `#n`. -/
section Show
variable [ToString S.C] [ToString S.P] [ToString S.O] [ToString S.B]

def Ty.show : Ty S.B → String
  | .base b => toString b
  | .arr t u => s!"({t.show} → {u.show})"
  | .prod t u => s!"({t.show} × {u.show})"
  | .sum t u => s!"({t.show} + {u.show})"

mutual
def Atom.show : Atom S → String
  | .var n => s!"#{n}"
  | .const c => toString c
  | .prim p as => s!"{p}({String.intercalate ", " (Atom.showL as)})"
  | .lam τ e => s!"λ(_:{τ.show}). {Tm.show e}"
  | .fix τ₁ τ₂ e => s!"fix _(_:{τ₁.show}):{τ₂.show}. {Tm.show e}"
  | .pair a₁ a₂ => s!"({Atom.show a₁}, {Atom.show a₂})"
  | .fst a => s!"π₁ {Atom.show a}"
  | .snd a => s!"π₂ {Atom.show a}"
  | .inl τ a => s!"inl[{τ.show}] {Atom.show a}"
  | .inr τ a => s!"inr[{τ.show}] {Atom.show a}"
def Atom.showL : List (Atom S) → List String
  | [] => []
  | a :: as => Atom.show a :: Atom.showL as
def Tm.show : Tm S → String
  | .ret a => s!"ret {Atom.show a}"
  | .letE τ e₁ e₂ => s!"let _:{τ.show} = {Tm.show e₁} in {Tm.show e₂}"
  | .letOp o as τ e => s!"let _:{τ.show} ← {o}({String.intercalate ", " (Atom.showL as)}) in {Tm.show e}"
  | .app a₁ a₂ => s!"({Atom.show a₁} {Atom.show a₂})"
  | .ite a e₁ e₂ => s!"if {Atom.show a} then {Tm.show e₁} else {Tm.show e₂}"
  | .case a e₁ e₂ => s!"case {Atom.show a} of inl _ ⇒ {Tm.show e₁} | inr _ ⇒ {Tm.show e₂}"
end
end Show

end VIRL1
