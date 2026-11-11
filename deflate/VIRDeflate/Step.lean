/-
OBJECT-DEFLATE under X1 (a): the L2 step program (DECLARATIONS-DEFLATE.md, "The L2 step program", S-1 … S-6, declared before this
file). This file grows per row. FIRST: D4's bit-of-a-byte as an L2 term, a pure top-level `fix` over `Int` with `sub`, `lt`,
`le`, `add` and `mul` only (P unchanged), run by L2's own step function and proved equal to `bitAt` (Bits.lean) on every byte.
l1/ and l2/ are imported and never edited (D2).
-/
import VIRDeflate.Bits
import VIRL2

namespace VIRDeflate.Step
open VIRL1 VIRL2

/-! ## Atoms, in de Bruijn form (these terms are small; the named layer of S-4 comes with the step itself) -/

abbrev ci (n : Int) : Atom₂ := .const (.int n)
abbrev vr (n : Nat) : Atom₂ := .var n
def padd (a b : Atom₂) : Atom₂ := .prim .add [a, b]
def psub (a b : Atom₂) : Atom₂ := .prim .sub [a, b]
def pmul (a b : Atom₂) : Atom₂ := .prim .mul [a, b]
def plt (a b : Atom₂) : Atom₂ := .prim .lt [a, b]
def ple (a b : Atom₂) : Atom₂ := .prim .le [a, b]

def tII : Ty₂ := .prod (.prod tint tint) tint
def tPow : Ty₂ := .arr tint tint
def tStrip : Ty₂ := .arr tII tint

/-- `fix pow2(k:int):int. if k ≤ 0 then 1 else 2 · pow2(k − 1)` — x = #0, pow2 = #1. -/
def POW : Atom₂ :=
  .fix tint tint <|
    .ite (ple (vr 0) (ci 0)) (.ret (ci 1)) <|
      .letE tint (.app (vr 1) (psub (vr 0) (ci 1))) (.ret (pmul (ci 2) (vr 0)))

/-- `fix strip(((n, i), v)) : int` = Bits.lean's `stripTop n i v`, with `pow2` free (de Bruijn #2 under the fix's two binders):
`if n ≤ 0 then v else let p = pow2(i + n) in let w = (if v < p then v else v − p) in strip(((n − 1, i), w))`. -/
def STRIP : Atom₂ :=
  .fix tII tint <|
    .ite (ple (.fst (.fst (vr 0))) (ci 0)) (.ret (.snd (vr 0))) <|
      -- p : #0, x : #1, strip : #2, pow2 : #3
      .letE tint (.app (vr 2) (padd (.snd (.fst (vr 0))) (.fst (.fst (vr 0))))) <|
      -- w : #0, p : #1, x : #2, strip : #3
      .letE tint (.ite (plt (.snd (vr 1)) (vr 0)) (.ret (.snd (vr 1))) (.ret (psub (.snd (vr 1)) (vr 0)))) <|
      .app (vr 3) (.pair (.pair (psub (.fst (.fst (vr 2))) (ci 1)) (.snd (.fst (vr 2)))) (vr 0))

/-- D4: `bitAt v i` as an L2 term with `v` and `i` given as constants:
`let pow2 = POW in let strip = STRIP in let r = strip(((7 − i, i), v)) in let q = pow2(i) in if r < q then 0 else 1`. -/
def bitProg (v i : Int) : Tm₂ :=
  .letE tPow (.ret POW) <|                                              -- pow2 : #0
  .letE tStrip (.ret STRIP) <|                                          -- strip : #0, pow2 : #1
  .letE tint (.app (vr 0) (.pair (.pair (ci (7 - i)) (ci i)) (ci v))) <| -- r : #0, strip : #1, pow2 : #2
  .letE tint (.app (vr 2) (ci i)) <|                                    -- q : #0, r : #1
  .ite (plt (vr 1) (vr 0)) (.ret (ci 0)) (.ret (ci 1))

/-- The integer a terminal `ret` carries, if that is what the term is. -/
def retInt? : Tm₂ → Option Int
  | .ret (.const (.int n)) => some n
  | _ => none

theorem retInt?_eq {t : Tm₂} {n : Int} (h : retInt? t = some n) : t = .ret (ci n) := by
  unfold retInt? at h
  split at h
  · cases h; rfl
  · cases h

end VIRDeflate.Step
