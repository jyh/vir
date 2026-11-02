/-
  O95 VIR program, Lean arm (PREDICTIONS-amend-11). STEPS 1–2: the terms of the router FRAGMENT, as a deep embedding.
  D1: UNSCOPED de Bruijn indices (`Atom.var n`), extrinsic typing (VIRP/Typing.lean). Index 0 is the innermost binder.
  Binders: `letLinDec`, `advance` and `readU32` each bind ONE variable in their continuation `e`.
  The runtime value forms `sl`, `tok`, `bool` exist so that the small-step semantics can substitute values; a source program
  (U, F) uses only variables, literals, `magic` and the operators.
-/
namespace VIRP

/-- The types of the fragment. `tok` (the bucket capability) is LINEAR; `slice` is AFFINE (VIRP/Typing.lean). -/
inductive Ty | int | bool | slice | tok
  deriving DecidableEq, Repr

/-- The drop codes (I1). -/
inductive Code | truncated | unauthOrRate
  deriving DecidableEq, Repr

/-- Atoms (A.2's `a`, the fragment's part of it, plus I1's operators). -/
inductive Atom where
  | var (n : Nat)
  | lit (i : Int)
  | bool (b : Bool)
  | sl (off : Nat)                 -- runtime: a slice of the frame buffer at offset `off`
  | tok                            -- runtime: the bucket capability
  | magic                          -- MAGIC (A.1)
  | len (a : Atom)                 -- len(a)
  | ge (a b : Atom)                -- a ≥ b
  | eq (a b : Atom)                -- a = b
  | and (a b : Atom)               -- a ∧ b
  | canAccess (p t : Atom)         -- can_access(p, t)
  | hasTokens (st p : Atom)        -- has_tokens(st, p)
  deriving DecidableEq, Repr

/-- Expressions (A.2's `e`, the fragment). -/
inductive Tm where
  | letLinDec (st p : Atom) (e : Tm)     -- let_lin{dec_tokens(st, p); st'. e}
  | advance (b : Atom) (i : Nat) (e : Tm) -- advance{b; i; s. e}
  | readU32 (b : Atom) (j : Nat) (e : Tm) -- read_u32{b; j; v. e}
  | guard (c : Atom) (ok err : Tm)        -- guard{c; ok; err}
  | ret (st b : Atom)                     -- return{(st, b)}
  | drop (c : Code)                       -- drop{code}
  deriving DecidableEq, Repr

/-! ## Display forms (the dforms of step 2): A.2's concrete syntax, binders shown as `#n` -/
def Atom.show : Atom → String
  | .var n => s!"#{n}" | .lit i => toString i | .bool b => toString b | .sl o => s!"<slice+{o}>" | .tok => "<tok>"
  | .magic => "MAGIC" | .len a => s!"len({a.show})" | .ge a b => s!"{a.show} ≥ {b.show}"
  | .eq a b => s!"{a.show} = {b.show}" | .and a b => s!"({a.show} ∧ {b.show})"
  | .canAccess p t => s!"can_access({p.show}, {t.show})" | .hasTokens s p => s!"has_tokens({s.show}, {p.show})"

def Tm.show : Tm → String
  | .letLinDec s p e => s!"let_lin\{dec_tokens({s.show}, {p.show}); _. {e.show}}"
  | .advance b i e => s!"advance\{{b.show}; {i}; _. {e.show}}"
  | .readU32 b j e => s!"read_u32\{{b.show}; {j}; _. {e.show}}"
  | .guard c o r => s!"guard\{{c.show}; {o.show}; {r.show}}"
  | .ret s b => s!"return\{({s.show}, {b.show})}"
  | .drop .truncated => "drop{ERR_TRUNCATED_FRAME}" | .drop .unauthOrRate => "drop{ERR_UNAUTHORIZED_OR_RATE_LIMITED}"

/-! ## Well-formedness (the _wf rules of step 2): every variable is bound, `n` binders in scope -/
def Atom.wf (n : Nat) : Atom → Prop
  | .var k => k < n
  | .len a => a.wf n
  | .ge a b => a.wf n ∧ b.wf n
  | .eq a b => a.wf n ∧ b.wf n
  | .and a b => a.wf n ∧ b.wf n
  | .canAccess a b => a.wf n ∧ b.wf n
  | .hasTokens a b => a.wf n ∧ b.wf n
  | _ => True

def Tm.wf (n : Nat) : Tm → Prop
  | .letLinDec s p e => s.wf n ∧ p.wf n ∧ e.wf (n + 1)
  | .advance b _ e => b.wf n ∧ e.wf (n + 1)
  | .readU32 b _ e => b.wf n ∧ e.wf (n + 1)
  | .guard c o r => c.wf n ∧ o.wf n ∧ r.wf n
  | .ret s b => s.wf n ∧ b.wf n
  | .drop _ => True

/-! ## Substitution (D1: defined, and its lemmas are the arm's to prove).
  `subst k v` replaces variable `k` by the CLOSED atom `v` and lowers the variables above `k`. Only closed runtime values
  are ever substituted (the small-step semantics substitutes `lit`, `sl` and `tok`), so no shift of `v` is needed. -/
def Atom.subst : Atom → Nat → Atom → Atom
  | .var n, k, v => if n = k then v else if k < n then .var (n - 1) else .var n
  | .len a, k, v => .len (a.subst k v)
  | .ge a b, k, v => .ge (a.subst k v) (b.subst k v)
  | .eq a b, k, v => .eq (a.subst k v) (b.subst k v)
  | .and a b, k, v => .and (a.subst k v) (b.subst k v)
  | .canAccess a b, k, v => .canAccess (a.subst k v) (b.subst k v)
  | .hasTokens a b, k, v => .hasTokens (a.subst k v) (b.subst k v)
  | a, _, _ => a

def Tm.subst : Tm → Nat → Atom → Tm
  | .letLinDec s p e, k, v => .letLinDec (s.subst k v) (p.subst k v) (e.subst (k + 1) v)
  | .advance b i e, k, v => .advance (b.subst k v) i (e.subst (k + 1) v)
  | .readU32 b j e, k, v => .readU32 (b.subst k v) j (e.subst (k + 1) v)
  | .guard c o r, k, v => .guard (c.subst k v) (o.subst k v) (r.subst k v)
  | .ret s b, k, v => .ret (s.subst k v) (b.subst k v)
  | .drop c, _, _ => .drop c

/-- Insert `x` at position `k` of a list (the context/environment counterpart of `subst k`). -/
def ins {α : Type} : Nat → α → List α → List α
  | 0, x, l => x :: l
  | _ + 1, _, [] => []
  | k + 1, x, y :: l => y :: ins k x l

end VIRP
