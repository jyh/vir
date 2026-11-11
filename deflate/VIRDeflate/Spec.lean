/-
OBJECT-DEFLATE, Appendix S §S2–S3, S5–S8 as an executable Lean spec (X4 (a): the arm formalizes THESE bytes).

TWO READINGS, by errata/ERRATA-DEFLATE.md row DEFLATE-E1 (recorded before this file was built):
* `inflateLit` — S read literally: S5's fixed codes go through S4's `code`, completeness REJECTs included. FIXED_D
  (30 symbols of length 5) is incomplete, so every fixed-Huffman block REJECTs "incomplete".
* `inflate` — the repaired reading: S5's fixed codes are S4's assignment with no completeness check; every other clause is
  shared, byte for byte, through the same functions.

LOOPS. S's `repeat … until`, `while` and `loop` are written with a fuel argument set at entry to the number of input bits not
yet read, plus one. Every iteration of each of those loops reads at least one bit (a block header, a `decode`), and `bit`
REJECTs "truncated" when no bit remains, so the fuel cannot run out before a REJECT; running out REJECTs "truncated". That
claim is a lemma OWED (it is not proved here), and it is the only place the fuel can differ from S.
-/
import VIRDeflate.Huffman

namespace VIRDeflate

/-- Bits not yet read, plus one: the fuel for a loop entered now. -/
def fuelNow : M Nat := do
  let e ← read
  let s ← get
  return 8 * e.inp.size - s.pos + 1

/-- S3: `stored()`. -/
def stored : M Unit := do
  align
  let len ← bits 16
  let nlen ← bits 16
  if nlen ≠ len ^^^ 0xFFFF then reject "invalid stored block lengths"
  let e ← read
  let s ← get
  if s.pos / 8 + len > e.inp.size then reject "truncated"
  if s.out.size + len > e.outmax then reject "overflow"
  set ({ pos := s.pos + 8 * len, out := s.out ++ e.inp.extract (s.pos / 8) (s.pos / 8 + len) } : St)

/-- S5: the fixed literal/length lengths: 0..143 → 8, 144..255 → 9, 256..279 → 7, 280..287 → 8. -/
def fixedLLens : Array Nat :=
  (List.range 288).toArray.map fun i => if i < 144 then 8 else if i < 256 then 9 else if i < 280 then 7 else 8

/-- S5: the fixed distance lengths: 0..29 → 5 (30 symbols). -/
def fixedDLens : Array Nat := (List.range 30).toArray.map fun _ => 5

/-- S7's tables. -/
def LBASE : Array Nat := #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163,
  195, 227, 258]
def LEXTRA : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]
def DBASE : Array Nat := #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049,
  3073, 4097, 6145, 8193, 12289, 16385, 24577]
def DEXTRA : Array Nat := #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]

/-- S7's copy, ONE BYTE AT A TIME: `append o[m - dist] to o`, `len` times (overlap repeats, §3.2.3). -/
def copyBack (dist : Nat) : Nat → Array Nat → Array Nat
  | 0, o => o
  | k + 1, o => copyBack dist k (o.push (o.getD (o.size - dist) 0))

/-- S7: `huff(L, D)`'s loop. -/
def huffLoop (L D : Code) : Nat → M Unit
  | 0 => reject "truncated"
  | fuel + 1 => do
    let s ← decode L
    if s < 256 then
      let e ← read
      let st ← get
      if st.out.size = e.outmax then reject "overflow"
      set { st with out := st.out.push s }
      huffLoop L D fuel
    else if s = 256 then
      return ()
    else if s ≤ 285 then
      let len := LBASE.getD (s - 257) 0 + (← bits (LEXTRA.getD (s - 257) 0))
      let d ← decode D
      if d ≥ 30 then reject "invalid distance code"
      let dist := DBASE.getD d 0 + (← bits (DEXTRA.getD d 0))
      let e ← read
      let st ← get
      if dist > st.out.size then reject "distance too far back"
      if st.out.size + len > e.outmax then reject "overflow"
      set { st with out := copyBack dist len st.out }
      huffLoop L D fuel
    else
      reject "invalid literal/length code"

/-- S7: `huff(L, D)`. -/
def huff (L D : Code) : M Unit := do huffLoop L D (← fuelNow)

/-- S6: the ORDER of the code-length code's lengths. -/
def ORDER : List Nat := [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- S6: `cl[ORDER[i]] := bits(3) for i < HCLEN`; the rest stay 0. -/
def readCL : List Nat → Nat → Array Nat → M (Array Nat)
  | [], _, cl => pure cl
  | o :: os, k, cl =>
    if k = 0 then pure cl else do
      let x ← bits 3
      readCL os (k - 1) (cl.set! o x)

/-- Append `x` to `a`, `k` times. -/
def pushN (x : Nat) : Nat → Array Nat → Array Nat
  | 0, a => a
  | k + 1, a => pushN x k (a.push x)

/-- S6: the `while |lens| < HLIT + HDIST` loop. -/
def lensLoop (CL : Code) (total : Nat) : Nat → Array Nat → M (Array Nat)
  | 0, _ => reject "truncated"
  | fuel + 1, lens =>
    if lens.size < total then do
      let s ← decode CL
      let lens' ←
        if s ≤ 15 then pure (lens.push s)
        else if s = 16 then do
          if lens.size = 0 then reject "repeat with no first length"
          let r ← bits 2
          pure (pushN (lens.getD (lens.size - 1) 0) (3 + r) lens)
        else if s = 17 then do
          let r ← bits 3
          pure (pushN 0 (3 + r) lens)
        else do
          let r ← bits 7
          pure (pushN 0 (11 + r) lens)
      if lens'.size > total then reject "invalid bit length repeat"
      lensLoop CL total fuel lens'
    else
      pure lens

/-- S6: `dynamic()`. -/
def dynamic : M Unit := do
  let hlit := (← bits 5) + 257
  let hdist := (← bits 5) + 1
  let hclen := (← bits 4) + 4
  if hlit > 286 ∨ hdist > 30 then reject "too many length or distance symbols"
  let cl ← readCL ORDER hclen (Array.replicate 19 0)
  let CL ← code cl .strict
  let lens ← lensLoop CL (hlit + hdist) (← fuelNow) #[]
  if lens.getD 256 0 = 0 then reject "missing end-of-block"
  let L ← code (lens.extract 0 hlit)
  let D ← code (lens.extract hlit (hlit + hdist)) .dist
  huff L D

/-- S5's fixed codes, by reading: `lit = true` is S read literally (through `code`, checks included — DEFLATE-E1);
`lit = false` is the repaired reading (S4's assignment alone). -/
def fixedCodes (lit : Bool) : M (Code × Code) :=
  if lit then do
    let L ← code fixedLLens
    let D ← code fixedDLens
    pure (L, D)
  else
    pure (assign fixedLLens, assign fixedDLens)

/-- S2: the block loop, `repeat … until BFINAL = 1`. -/
def blocks (lit : Bool) : Nat → M Unit
  | 0 => reject "truncated"
  | fuel + 1 => do
    let bfinal ← bits 1
    let btype ← bits 2
    if btype = 0 then stored
    else if btype = 1 then do
      let (L, D) ← fixedCodes lit
      huff L D
    else if btype = 2 then dynamic
    else reject "invalid block type"
    if bfinal = 1 then return () else blocks lit fuel

/-- Run the spec on input `b` with bound `outmax`: `.ok o` is ACCEPT o, `.error r` is `reject(r)` (S8). -/
def run (lit : Bool) (b : Array Nat) (outmax : Nat) : Except String (Array Nat) :=
  match ((do blocks lit (← fuelNow) : M Unit).run ⟨b, outmax⟩).run ⟨0, #[]⟩ with
  | .ok (_, s) => .ok s.out
  | .error r => .error r

/-- S read literally (DEFLATE-E1's first reading). -/
def inflateLit (b : Array Nat) (outmax : Nat) : Except String (Array Nat) := run true b outmax

/-- The repaired reading (DEFLATE-E1's decision). -/
def inflate (b : Array Nat) (outmax : Nat) : Except String (Array Nat) := run false b outmax

end VIRDeflate
