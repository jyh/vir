import K7.DeflateX86N
import VIRDeflate.Run
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step K5

-- row 378 sizing (EMPIRICAL, not a proof): the deepest letE context (≈ word frames, S1's Match pairs them 1:1) that DEFLATE's
-- step program reaches on five corpus streams, over its whole iteration.
def ctxD : Tm₂ → Nat
  | .letE _ e₁ _ => 1 + ctxD e₁
  | _ => 0

def walk : Nat → Config → Nat → Option (Store × Nat)
  | 0, _, _ => none
  | f + 1, c, mx => match c.1 with
    | .ret _ => some (c.2, mx)
    | _ => match stepFn₂ c.1 c.2 with
      | some c' => walk f c' (max mx (ctxD c'.1))
      | none => none

def iterD : Nat → Store → Nat → Nat → (Nat × Nat × Bool)
  | 0, _, mx, n => (mx, n, false)
  | k + 1, σ, mx, n => match walk 200000 (closeAt 0 stepT, σ) (ctxD (closeAt 0 stepT)) with
    | some (σ', d) => if σ'.H.lookup 0 == σ.H.lookup 0 && d == 0 then (mx, n, true) else iterD k σ' (max mx d) (n + 1)
    | none => (mx, n, true)

def measure (b : Array Nat) : (Nat × Nat × Bool) := iterD 400 (initStore b 64 false 0) 0 0

#eval measure Run.i_stored_empty_final
#eval measure Run.i_fixed_empty_final
#eval measure Run.i_fixed_one_literal
#eval measure Run.i_fixed_overlap_copy
#eval measure Run.i_two_blocks
