/-
OBJECT-DEFLATE, Appendix S §S4: canonical Huffman codes, the construction and `decode`. D5's CANONICAL-CODE group
(deflate/DECLARATIONS-DEFLATE.md): this file and Kraft.lean.

The representation is S4's assignment itself, kept in the form that assignment produces:
`first[ℓ]` is `next_code[ℓ]` before any symbol takes it, and `syms[ℓ]` lists the symbols of length ℓ in increasing index,
which is the order `next_code[lens[i]]++` hands them codes. So the symbol whose code is the ℓ-bit value `v` is
`syms[ℓ][v - first[ℓ]]` when `first[ℓ] ≤ v < first[ℓ] + bl_count[ℓ]`, and no symbol has it otherwise.
-/
import VIRDeflate.Bits

namespace VIRDeflate

/-- A canonical code, as S4's assignment leaves it. Arrays are indexed by length ℓ ∈ 0..15 (entry 0 unused). -/
structure Code where
  count : Array Nat
  first : Array Nat
  syms : Array (Array Nat)

/-- S4: `bl_count[ℓ] := #{ i : lens[i] = ℓ }` for ℓ ≥ 1, and `bl_count[0] := 0`. -/
def blCount (lens : Array Nat) (l : Nat) : Nat :=
  if l = 0 then 0 else lens.foldl (fun c x => if x = l then c + 1 else c) 0

/-- S4: `code := 0 ; for ℓ in 1..15: code := (code + bl_count[ℓ-1]) << 1 ; next_code[ℓ] := code`. -/
def nextCodes (lens : Array Nat) : Array Nat :=
  ((List.range' 1 15).foldl
    (fun (acc : Nat × Array Nat) l =>
      let c := (acc.1 + blCount lens (l - 1)) <<< 1
      (c, acc.2.push c))
    (0, #[0])).2

/-- The symbols of length ℓ, in increasing index. -/
def symsOf (lens : Array Nat) (l : Nat) : Array Nat :=
  (List.range lens.size).foldl (fun a i => if lens.getD i 0 = l then a.push i else a) #[]

/-- S4's construction with no completeness check: the assignment alone. -/
def assign (lens : Array Nat) : Code :=
  { count := (List.range 16).toArray.map (blCount lens)
    first := nextCodes lens
    syms := (List.range 16).toArray.map (symsOf lens) }

/-- S4: `left := 1 ; for ℓ in 1..15: left := 2·left − bl_count[ℓ]`, stopping at the first ℓ where `left < 0`
(`none` = REJECT "over-subscribed"); otherwise the final `left`. -/
def leftAfter (lens : Array Nat) : Option Int :=
  (List.range' 1 15).foldl
    (fun (acc : Option Int) l =>
      match acc with
      | none => none
      | some left =>
        let left' := 2 * left - (blCount lens l : Int)
        if left' < 0 then none else some left')
    (some 1)

/-- "the code has exactly one symbol, of length 1". -/
def oneSymbolLenOne (lens : Array Nat) : Bool :=
  blCount lens 1 = 1 && (List.range' 2 14).all (fun l => blCount lens l = 0)

/-- How the incomplete clause applies. S4 as written (`normal`); S6's code-length code, *"no exception"* (`strict`);
S4's note on the empty distance code (`dist`): an all-zero distance code is accepted. -/
inductive Mode where
  | normal
  | strict
  | dist
  deriving DecidableEq

/-- S4: `code(lens)`, with its two REJECTs. -/
def code (lens : Array Nat) (mode : Mode := .normal) : M Code :=
  match leftAfter lens with
  | none => reject "over-subscribed"
  | some left =>
    let empty := lens.all (· = 0)
    let exempt := match mode with
      | .normal => oneSymbolLenOne lens
      | .strict => false
      | .dist => oneSymbolLenOne lens || empty
    if left > 0 && !exempt then reject "incomplete" else pure (assign lens)

/-- `decode` as a loop over the code length ℓ: `v` is the ℓ-bit value read so far, MSB first. -/
def decodeGo (C : Code) : Nat → Nat → Nat → M Nat
  | 0, _, _ => reject "invalid code"
  | fuel + 1, l, v => do
    let x ← bit
    let v := 2 * v + x
    let f := C.first.getD l 0
    let n := C.count.getD l 0
    if f ≤ v ∧ v < f + n then
      return (C.syms.getD l #[]).getD (v - f) 0
    else
      decodeGo C fuel (l + 1) v

/-- S4: `decode(C)` — read bits MSB-first until they form a code of C; REJECT "invalid code" if none can (all codes have
length ≤ 15, so after 15 bits none can). -/
def decode (C : Code) : M Nat := decodeGo C 15 1 0

end VIRDeflate
