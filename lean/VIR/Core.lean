/-
  VIR Lean arm, L-IDX. Shallow CPS embedding of the A.2 grammar (PREDICTIONS-amend-2).
  Slices are length-indexed (`Slice n`), as PREDICTIONS.md fixes for L-IDX.
-/
namespace VIR

/-- A zero-copy slice of `n` bytes into a buffer: the L-IDX representation. -/
structure Slice (n : Nat) where
  buf  : ByteArray
  off  : Nat
  fits : off + n ≤ buf.size

/-- `advance` on slices: the A.2 zero-copy slice advance. -/
def Slice.adv {n : Nat} (s : Slice n) (i : Nat) (_h : i ≤ n) : Slice (n - i) :=
  ⟨s.buf, s.off + i, by have := s.fits; omega⟩

/-- Total little-endian 32-bit read at offset `j` (exact when in bounds; Exhibit A.1's "total accessor"). -/
def Slice.rd {n : Nat} (s : Slice n) (j : Nat) : UInt32 :=
  let g := fun k => (s.buf.get! (s.off + j + k)).toUInt32
  g 0 ||| (g 1 <<< 8) ||| (g 2 <<< 16) ||| (g 3 <<< 24)

abbrev Principal := UInt32
abbrev TopicId   := UInt32
/-- Token-bucket state: tokens per principal. -/
abbrev State := Principal → Int

def MAGIC : UInt32 := 0x4D534731

inductive Code | truncated | unauthOrRate
  deriving DecidableEq

/-- Terminal outcomes: `return{(st, slice)}` or `drop{code}`. -/
inductive Out
  | ret  (st : State) (len : Nat) (s : Slice len)
  | drop (c : Code)

/-! ## I1 declared constants -/
def hasTokens (st : State) (p : Principal) : Prop := 0 < st p
instance (st : State) (p : Principal) : Decidable (hasTokens st p) := by
  unfold hasTokens; infer_instance
def decTokens (st : State) (p : Principal) : State := fun q => if q = p then st p - 1 else st q

/-- The ACL is a parameter of the router: `can_access` is uninterpreted (I1). -/
def canAccess (acl : Principal → TopicId → Bool) (p : Principal) (t : TopicId) : Prop := acl p t = true
instance (acl : Principal → TopicId → Bool) (p t) : Decidable (canAccess acl p t) := by
  unfold canAccess; infer_instance

/-! ## The A.2 forms -/
/-- `guard{c; e_ok; e_err}`; the ok branch receives the proof (dependent `if`). -/
def guard (c : Prop) [Decidable c] (ok : c → Out) (err : Out) : Out := if h : c then ok h else err
def readU32 {n : Nat} (s : Slice n) (j : Nat) (k : UInt32 → Out) : Out := k (s.rd j)
def advance {n : Nat} (s : Slice n) (i : Nat) (h : i ≤ n) (k : Slice (n - i) → Out) : Out := k (s.adv i h)
def letLin {α : Type} (x : α) (k : α → Out) : Out := k x
def letAtom {α : Type} (a : α) (k : α → Out) : Out := k a

end VIR
