/-
  O95 VIR program, Lean arm. STEP 6 (the denotation, THE MEANING) and STEP 3 (the small-step semantics, DEFINED).
  D2: ⟦p⟧ : Store → Part (Store × Label), mathlib `Part`, NO FUEL. D3: the store is typed and region-separated — the frame
  buffer, the token-bucket region and the ACL region are separate fields, so their disjointness holds by construction, and
  the I1 operators are DEFINED over them (no uninterpreted operator: V1).
  A drop ABORTS: the top-level meaning returns the store the call was entered with (the x86 drop leaves memory unchanged).
-/
import Mathlib.Data.Part
import VIRP.Syntax

namespace VIRP

/-- The typed, region-separated store. -/
structure Store where
  wire   : List Int           -- the frame buffer region (bytes)
  bucket : Int → Nat          -- the token-bucket region, per sender
  acl    : Int → Int → Bool   -- the ACL region, (sender, topic)

def MAGIC : Int := 0x4D534731

/-- The little-endian 32-bit wire read (out of range reads 0). -/
def rd32 (w : List Int) (o : Nat) : Int :=
  w.getD o 0 + 256 * w.getD (o + 1) 0 + 65536 * w.getD (o + 2) 0 + 16777216 * w.getD (o + 3) 0

/-- `dec_tokens` on the bucket region: one token less for sender `p` (saturating at 0). -/
def Store.dec (σ : Store) (p : Int) : Store :=
  { σ with bucket := fun q => if q = p then σ.bucket q - 1 else σ.bucket q }

inductive Val | int (i : Int) | bool (b : Bool) | sl (off : Nat) | tok
  deriving DecidableEq, Repr

/-- The exit labels: an emit carries the payload slice's offset; a drop its code. -/
inductive Label | emit (off : Nat) | drop (c : Code)
  deriving DecidableEq, Repr

/-- Atom evaluation in an environment (index 0 = head). `none` = ill-sorted (stuck). -/
def Atom.eval (env : List Val) (σ : Store) : Atom → Option Val
  | .var n => env[n]?
  | .lit i => some (.int i)
  | .bool b => some (.bool b)
  | .sl o => some (.sl o)
  | .tok => some .tok
  | .magic => some (.int MAGIC)
  | .len a => match a.eval env σ with
    | some (.sl o) => some (.int ((σ.wire.length : Int) - o)) | _ => none
  | .ge a b => match a.eval env σ, b.eval env σ with
    | some (.int x), some (.int y) => some (.bool (decide (x ≥ y))) | _, _ => none
  | .eq a b => match a.eval env σ, b.eval env σ with
    | some (.int x), some (.int y) => some (.bool (decide (x = y))) | _, _ => none
  | .and a b => match a.eval env σ, b.eval env σ with
    | some (.bool x), some (.bool y) => some (.bool (x && y)) | _, _ => none
  | .canAccess p t => match p.eval env σ, t.eval env σ with
    | some (.int x), some (.int y) => some (.bool (σ.acl x y)) | _, _ => none
  | .hasTokens s p => match s.eval env σ, p.eval env σ with
    | some .tok, some (.int x) => some (.bool (decide (1 ≤ σ.bucket x))) | _, _ => none

/-! ## STEP 6: the denotation -/

/-- The inner meaning: the store at the exit, and the exit label. `Part.none` where evaluation is stuck. -/
def den : Tm → List Val → Store → Part (Store × Label)
  | .letLinDec s p e, env, σ =>
    match s.eval env σ, p.eval env σ with
    | some .tok, some (.int x) => den e (.tok :: env) (σ.dec x)
    | _, _ => Part.none
  | .advance b i e, env, σ =>
    match b.eval env σ with
    | some (.sl o) => den e (.sl (o + i) :: env) σ
    | _ => Part.none
  | .readU32 b j e, env, σ =>
    match b.eval env σ with
    | some (.sl o) => den e (.int (rd32 σ.wire (o + j)) :: env) σ
    | _ => Part.none
  | .guard c ok err, env, σ =>
    match c.eval env σ with
    | some (.bool true) => den ok env σ
    | some (.bool false) => den err env σ
    | _ => Part.none
  | .ret s b, env, σ =>
    match s.eval env σ, b.eval env σ with
    | some .tok, some (.sl o) => Part.some (σ, .emit o)
    | _, _ => Part.none
  | .drop c, _, σ => Part.some (σ, .drop c)

/-- Abort on drop: the store returned is the one the call was entered with. -/
def abort (σ₀ : Store) : Store × Label → Store × Label
  | (σ, .emit o) => (σ, .emit o)
  | (_, .drop c) => (σ₀, .drop c)

/-- ⟦p⟧ : Store → Part (Store × Label), the meaning of a program in environment `env`. -/
def denote (e : Tm) (env : List Val) (σ : Store) : Part (Store × Label) := (den e env σ).map (abort σ)

/-! ## STEP 3: the small-step semantics, DEFINED (never primitive) over closed terms -/

inductive Step : Store → Tm → Store → Tm → Prop where
  | letLinDec {σ s p e x} : s.eval [] σ = some .tok → p.eval [] σ = some (.int x) →
      Step σ (.letLinDec s p e) (σ.dec x) (e.subst 0 .tok)
  | advance {σ b i e o} : b.eval [] σ = some (.sl o) → Step σ (.advance b i e) σ (e.subst 0 (.sl (o + i)))
  | readU32 {σ b j e o} : b.eval [] σ = some (.sl o) →
      Step σ (.readU32 b j e) σ (e.subst 0 (.lit (rd32 σ.wire (o + j))))
  | guardT {σ c ok err} : c.eval [] σ = some (.bool true) → Step σ (.guard c ok err) σ ok
  | guardF {σ c ok err} : c.eval [] σ = some (.bool false) → Step σ (.guard c ok err) σ err

/-- The reflexive-transitive closure. -/
inductive Steps : Store → Tm → Store → Tm → Prop where
  | refl {σ e} : Steps σ e σ e
  | step {σ e σ' e' σ'' e''} : Step σ e σ' e' → Steps σ' e' σ'' e'' → Steps σ e σ'' e''

/-- A terminal configuration and the (inner) result it reports. -/
inductive Final : Store → Tm → Store × Label → Prop where
  | ret {σ s b o} : s.eval [] σ = some .tok → b.eval [] σ = some (.sl o) → Final σ (.ret s b) (σ, .emit o)
  | drop {σ c} : Final σ (.drop c) (σ, .drop c)

end VIRP
