/-
  O95 layer L3 (OBJECT-L3), Lean arm (amend-18). The layout of `world` (inputs/L3-programs.md: NW 64, NS 4, NT 4) and the
  macros RD32 / EXIT / EMIT, as DEFINITIONS this arm states (l3/DECLARATIONS-LEAN.md). Terms are written with NAMES and
  compiled to L2's de Bruijn `Tm₂` by `NT.c` (the innermost binder of a name wins, as in the inputs file's shadowing), so F and U
  read operation for operation as the inputs file writes them. L2 is imported and never edited (Z1).
-/
import VIRL2

namespace VIRL3
open VIRL1 VIRL2

/-! ## The layout (G1 (a), G2 (a), G3 (a)) -/
def NW : Int := 64
def NS : Int := 4
def NTp : Int := 4          -- NT in the inputs file (`NT` is this file's name for named terms)
def A : Int := 3 + NW       -- 67, the ACL's first cell
def K : Int := A + NS * NTp -- 83, the buckets' first cell
def MAGIC : Int := 1297303345

/-! ## Named atoms and expressions (only the forms L3's programs use) -/
inductive NA where
  | v (x : String)
  | i (n : Int)
  | p (o : L1.Prim) (a b : NA)

inductive NT where
  | ret (a : NA)
  | letE (x : String) (τ : Ty₂) (e₁ e₂ : NT)
  | op (x : String) (τ : Ty₂) (o : Op) (as : List NA) (e : NT)
  | ite (a : NA) (e₁ e₂ : NT)

/-- Compile a named atom in scope Γ (innermost first). -/
def NA.c (Γ : List String) : NA → Atom₂
  | .v x => .var (Γ.idxOf x)
  | .i n => .const (.int n)
  | .p o a b => .prim o [a.c Γ, b.c Γ]

def NT.c (Γ : List String) : NT → Tm₂
  | .ret a => .ret (a.c Γ)
  | .letE x τ e₁ e₂ => .letE τ (e₁.c Γ) (e₂.c (x :: Γ))
  | .op x τ o as e => .letOp o (as.map (NA.c Γ)) τ (e.c (x :: Γ))
  | .ite a e₁ e₂ => .ite (a.c Γ) (e₁.c Γ) (e₂.c Γ)

/-! ## Notation for the atoms -/
def add (a b : NA) : NA := .p .add a b
def sub (a b : NA) : NA := .p .sub a b
def mul (a b : NA) : NA := .p .mul a b
def le (a b : NA) : NA := .p .le a b
def lt (a b : NA) : NA := .p .lt a b
def eq (a b : NA) : NA := .p .eq a b
def conj (a b : NA) : NA := .p .and a b

/-! ## The macros (inputs/L3-programs.md "Macros") -/
/-- `RD32(o, x) k`: four loads of the world `w` at cells 3+o … 6+o, then `x` bound to the little-endian sum. -/
def RD32 (w : String) (o : Int) (x : String) (k : NT) : NT :=
  let x0 := x ++ "0"; let x1 := x ++ "1"; let x2 := x ++ "2"; let x3 := x ++ "3"
  .op x0 tint .load [.v w, .i (3 + o)] <|
  .op x1 tint .load [.v w, .i (4 + o)] <|
  .op x2 tint .load [.v w, .i (5 + o)] <|
  .op x3 tint .load [.v w, .i (6 + o)] <|
  .letE x tint (.ret (add (.v x0) (add (mul (.i 256) (.v x1))
      (add (mul (.i 65536) (.v x2)) (mul (.i 16777216) (.v x3)))))) k

/-- `EXIT(c)` on the world `w`: `let w′:cap ← store(w, 1, c) in ret w′`. -/
def EXIT (w : String) (c : Int) : NT :=
  .op "w'" tcap .store [.v w, .i 1, .i c] (.ret (.v "w'"))

/-- `EMIT` on the world `w`: `let w′:cap ← store(w, 1, 0) in let w″:cap ← store(w′, 2, 24) in ret w″`. -/
def EMIT (w : String) : NT :=
  .op "w'" tcap .store [.v w, .i 1, .i 0] <|
  .op "w''" tcap .store [.v "w'", .i 2, .i 24] (.ret (.v "w''"))

end VIRL3
