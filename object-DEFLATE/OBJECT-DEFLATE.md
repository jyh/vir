# OBJECT-DEFLATE — the first application, RFC 1951 inflate as an L2 program (X0(a) X1(a) X2(a) X3(a) X4(a) X5(a) X6(a))

**Drafted 2026-11-06 by the 25th vir head. PINNED 2026-11-11 by the 61st, BEFORE any DEFLATE file on any arm**, on the Captain's
word at the 11-11 council (ask 4, put to him as *"Pin the compiler with DEFLATE first, pin a layer-5 object first, or hold until
you have read the drafts?"*, with the compiler recommended and its departure from O95's named first program, the router, stated
beside it). His words: *"yes accept"*. Every fork is at its stated recommendation: X0 (a) Lean only · X1 (a) one decode step is
the L2 program, and the loop is in the logic · X2 (a) the whole decoder · X3 (a) safety on every input and correctness · X4 (a)
the spec is the object's own text (`APPENDIX-S.md` beside this file, pinned in the same commit) · X5 (a) zlib raw inflate as the
oracle on a corpus pinned by hash, mutations included · X6 (a) n and OUTMAX are parameters.
**He accepted without having read this text or Appendix S.** The record of the sitting says so, and that one word from him at any
sitting re-opens the choice of first program. This pin does not claim his read.
The text from "The draft's own preamble" down is the draft byte for byte, except one redaction: a bus offset is written `@[bus]`.
**Nothing in this file is edited after its pin.** An erratum goes in `errata/ERRATA-DEFLATE.md`. Predictions:
`predictions/PREDICTIONS-amend-23.md`, in this file's commit.

**Declared at the pin, against §0 and §2 below (facts of L1/L2 as built, read at master 1189b49, none of them a fork):**
- **P₂ = P₁ = {add, sub, mul, lt, le, eq, and, or, not, max}** (`l1/VIRL1/L1.lean:15`). There is no shift, no bitwise
  operator, no division and no modulus, and `and`/`or` are on booleans. Appendix S's `bits(k)` (a shift and a mask on a byte)
  is therefore NOT a primitive in L2. Under X1 (a)'s "no language change" it is written with what L2 has: a pure top-level
  recursion (a `fix` body, checked with Δ = ∅, which holds no capability) over `Int` with `sub` and `lt`. That is a choice
  inside the ruled arm, and it is stated here so that it is not found in a proof. A primitive added to P would be a language
  change and a new layer object.
- **`int` is the mathematical `Int`**, unbounded. Inside the logic, DEFLATE has no overflow. The 64-bit gap belongs to the
  compiler (OBJECT-COMPILER, fork C4), not to this object.
- §2's *"termination (a measure on the input cursor)"* is the draft's guess at a ROW, not a clause of the spec. Whether the
  cursor alone suffices is a prediction (amend-23 D3). It is not settled here.

The draft's own preamble, kept as its record:

# OBJECT-DEFLATE — DRAFT, UNPINNED: the first application, RFC 1951 inflate as an L2 program (STATUS-vir row 160)

**Drafted 2026-11-06 ~10:3x PST by the 25th vir head**, on the helm's XF decision (@[bus]): *"DRAFT the DEFLATE object now …
NOT pinned until he has read your map (f90a8e0) and the draft."* The CHOICE is his (11-06 council §E 6: *"DEFLATE is a good first
choice"*). This file is the CONTENT he reads before anything is frozen. Each fork carries a recommendation and a default. **No arm
builds from this file until his "yes" pins it.** Predictions (amend-23) are written after the pin and before the first DEFLATE file.

## 0. What the application inherits, and the limit it meets first
- L2: byte-sized cells in regions, linear capabilities, the semantic triple with a frame rule, and index faults as the only
  faults the types allow (errata L2-E1/E2). The L3 METHOD: a program written in L2, with its properties re-derived in the logic.
- **The limit, stated so nobody discovers it in a proof.** OBJECT-L3 (R-b): *no capability crosses a function boundary*, and a
  λ/fix body is checked with Δ = ∅. Inflate's main loop reads the input and writes the output region on every iteration. **No L2
  `fix` can hold those capabilities across iterations.** L3 met the same wall, and put the n-call property in the LOGIC rather than in
  an L2 loop. Fork X1 decides it for DEFLATE. It is also OBJECT-L2's named L1′ trigger: *"L4 wanting capabilities in function
  types"*. DEFLATE is the first program that wants them.

## 1. The forks
- **X0 — which arms.** (a) LEAN ONLY: the application phase, which is his "in Lean we are actually ready to proceed". The object is
  frozen the same way, so the MetaPRL arm can take it later without a re-pin. (b) both arms now. **Rec (a)**: the MetaPRL arm's queue
  is Y5 to the 11-08 cap, then SLang, then L3 and L4. A two-arm DEFLATE would wait behind all of it. Default (a).
- **X1 — the loop.** (a) ONE DECODE STEP is the L2 program (it decodes one symbol or one block header, given the regions and a
  cursor record), and the loop is an induction in the logic, as for L3's R6. The theorem is about the iteration. (b) L1′:
  capabilities in function types, a new layer object (L2′) BEFORE DEFLATE, so `inflate` is one L2′ term with a real loop. (c) a
  bounded unrolling at a fixed input size. **Rec (a)** for THIS object: no language change, and the L3 method carries over. **Name
  (b) as owed for the COMPILER step**, because a loop in the logic is not a loop in the machine code. The vertical slice to x86
  needs either (b) or a lowering theorem that composes step lowerings. Default (a).
- **X2 — the subset of RFC 1951.** (a) the WHOLE decoder: stored (BTYPE 00), fixed Huffman (01), dynamic Huffman (10), BTYPE 11
  rejected, back-references to distance 32,768. (b) stored + fixed only. (c) stored only. **Rec (a)**: dynamic Huffman (the code-length
  code, canonical code construction) is where the specification work is, and an inflate without it is not DEFLATE. Default (a).
- **X3 — the properties.** (a) **SAFETY on EVERY input** (no index fault, and termination, on any byte string, including
  adversarial ones) AND **CORRECTNESS** (if the spec accepts b with output o, the program returns o; if the spec rejects b, the
  program rejects). (b) correctness on spec-accepted inputs only. **Rec (a)**: a decoder's headline property is what it does on
  hostile input. That is the property hand-written C decoders fail, and the reason the application was chosen. Default (a).
- **X4 — the spec's form.** (a) the object carries the SPEC itself, as pseudo-code transcribed from RFC 1951 §3.2 (as A.3 carried
  the router), frozen with the object. Each arm formalizes THAT text, and a transcription check compares each arm's executable spec
  with it. (b) each arm transcribes the RFC on its own. **Rec (a)**: one frozen text makes "what is DEFLATE" a fact of the object, not
  of an arm. An RFC ambiguity becomes an erratum against the object, not a silent choice. Default (a). **Under (a) the pseudo-code is
  NOT in this draft.** It is written next, as an appendix to this file, and he reads it before the pin, so his "yes" covers the
  text that gets frozen.
- **X5 — the oracle protocol (zlib).** (a) zlib's `inflate` in RAW mode (windowBits −15), at a release pinned by version and
  tarball sha256. It is the ORACLE for the spec, never for the proof: each arm's executable spec must agree with zlib on a corpus
  pinned by hash. Accept or reject must agree, and on accept the bytes must be identical. The corpus: (i) the RFC's own examples;
  (ii) a fixed seed text compressed by zlib at levels 0–9 and strategies default · filtered · huffman-only · RLE · fixed;
  (iii) N mutations of (ii) (bit flips, truncations, distance > window, over-subscribed and incomplete code sets) to exercise
  rejection. (b) (i)+(ii) only. **Rec (a)**: rejection is half of X3 (a), and only malformed inputs test it. A disagreement is a
  finding against the arm's spec, or an erratum against the object, and is recorded before any repair. Default (a).
- **X6 — the bounds.** (a) input length and the output region's size OUTMAX are PARAMETERS, and the properties are ∀ over them. A
  stream whose output would exceed OUTMAX is REJECTED by both the spec and the program. That is a declared deviation from the RFC,
  which has no bound. (b) a fixed OUTMAX. **Rec (a)**. Default (a).

## 2. What the rows would be (G-style, at the recommendations; written fully at the pin)
the spec's transcription check against the object's text and against zlib on the corpus (X4, X5) · the step program's typing in ⊢₂ ·
the step's triple (each case: stored copy, a literal, a length/distance copy within the window, end of block, a header) · the
loop's safety on every input, and its termination (a measure on the input cursor) · correctness against the spec (the step relation
simulates the spec's) · rejection agreement · the canonical-code construction's lemmas (Kraft completeness and over-subscription) ·
one concrete run per corpus class reproduced by evaluation · `#print axioms` within the standard three.

## 3. What this object does not contain
compression · the zlib and gzip wrappers (headers, Adler-32, CRC-32) · preset dictionaries · a streaming or incremental API ·
performance · the x86 lowering (the compiler step, after X1 (b) or a composition theorem) · any ffmpeg component (O101, CANDIDATE).

## 4. What would show this draft unfair or premature
a fork ruled after the first DEFLATE proof file · a corpus chosen after an arm's spec disagreed with zlib · the spec's pseudo-code
edited after the pin (an erratum is a separate file) · X1 (a) chosen because the L3 machinery exists. X1's rec is stated against
that convenience, on the object: L2 cannot express the loop.
