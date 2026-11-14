# LV8 / LV9 — DEFLATE over the library: the per-mode map (Lean arm, written BEFORE any Deflate5 code)

Written 2026-11-13 by the 72nd vir head on the sealed branch `l5-lean`, after bitR's Addendum 4 (17d0ca1) and before any
`l5/VIRL5/Deflate5*.lean` exists. The fork that shapes it was posted on the bus at the same hour, and this map executes arm (A).

## The rule this map obeys (arm (A): chunked calls at the pinned per-step fuel)
- LV8's statements are the ones on master at caf23c0 (`SafetyStmt`, `CorrectStmt` in deflate/VIRDeflate/Statements.lean; `safety`;
  `deflate_driver`'s L2 statement in k7/K7/DeflateDriver.lean). Only the LANGUAGE moves: the step term is a `Tm₅`, run by a ⟶₅
  step function `run₅` at the SAME fuel `KSTEP = 512`, with the same `initStore`, `modeOf`, `outOf`, `reasonOf` and the same world
  layout. No statement is weakened. The existential bound N may change, because it is existential in the statement.
- A loop that DEFLATE spreads ACROSS steps (one item per step) becomes ONE routine call per step on at most C items. The mode still
  loops across steps until its count reaches 0. C is a constant per routine, written here BEFORE the code. If a step at that C
  does not fit KSTEP (Fit₅ says so), C is cut by an addendum to this file, never by raising KSTEP.
- Every routine use goes through its triple (LV8: 0 lemmas that unfold a routine body). A call sits inside the world region:
  the world capability is LENT, and the routine's index arguments name the sub-range (R-a: DEFLATE has ONE region).

## The map (mode → library, with C; "—" = no routine fits, kept as written)
| mode | per-step item now | becomes | C |
|---|---|---|---|
| TABLE (0) | one bit-table cell by `BITc` | **dropped**: nothing reads the table once READ and DECODE use bitR; mode 0 goes straight to HDR's work (LV9 counts TABLE's nodes as removed). The BT cells stay in the layout, unread | — |
| READ (2) | one bit, from the TABLE (BT + 8·v + bi) | **bitR** on (by, bi, min(k, C)), acc += value · wt, wt ·= 2^got; the cells read change from the table to the input byte (declared here, the "design fact for LV8" BANK-71 named) | C_bit = 4 |
| DECODE (14) | one bit (as READ does) + one code test | **bitR** with k = 1 for the bit; the code test stays hand-written (data-dependent, per bit) | 1 |
| SCOPY (10) | one byte input → output | **copyWithinR** (same world, forward; the ranges never overlap here, and the routine does not need that) on min(pending, C) bytes | C_copy = 32 |
| COPY (19) | one back-reference byte | **copyWithinR** on min(pending, C) bytes, overlap allowed (RFC 1951's order is the routine's own) | C_copy = 32 |
| FIXLENS (6) | one fixed length, from 5 constant runs | **fillR** on the current run, min(run left, C) cells | C_fill = 32 |
| REP (27) | one repeated code length | **fillR** with the repeated value, min(pending, C) cells | C_fill = 32 |
| BUILD phase 0, ZERO | count[j] := 0, j < 16 | **fillR** over the 16 counts in one call (16 ≤ C) | C_fill |
| BUILD phases 1–4 (COUNT, NEXT, LEFT, SYMS) | histogram, prefix sums, Kraft check, slot scatter | — (data-dependent per item: no library routine is this loop) | — |
| HDR, HDRB, HDRD, SHDR, SLEN, SNLEN, DHDR, CLREAD, CLPUT, LENS, LSYM, LREP, SYM, SYMD, LENX, DSTD, DSTX | one decision | — (no loop; bits they need come through READ requests as now) | — |

**Not used by DEFLATE:** `cmpR`, `scanR` (they are the router's, LV8 (b)), `copyR` (two regions; DEFLATE has one). LV9 is per
program and per routine, so a routine one program does not use reads 0 there and is not a falsification (LV9 asks ≥ 1 call per PROGRAM).

## Infrastructure owed before Deflate5 (each its own file, red first where a harness count reads it)
1. `Run5.lean`: `stepFn₅` (a function), sound and complete for ⟶₅, and `run₅`. DEFLATE's `stepS` is defined by `run₂`, so L5
   needs its own (L2's `stepFn₂_complete` is DEFLATE's Fit.lean; the L5 one is new and stated the same way).
2. `Fit5.lean`: each re-expressed mode's step fits KSTEP at its C (the counted-steps argument of Fit.lean over ⟶₅, with a routine
   call counted by a COST clause in its triple, not by unfolding it: LV8 forbids the unfolding). ⚠️ The routines' triples state
   no cost today. Adding a step bound to each triple is an addendum to DECLARATIONS-LEAN, made before Fit5 needs it.
3. Then `Deflate5.lean` (the step term over the library) and the carried statements.

## What would show this map wrong
a mode whose collapse needs a lemma about a routine's body (LV8 FALSIFIED: the library did not abstract) · a C that cannot fit
KSTEP with any value ≥ 1 (the chunked arm fails, and the fork goes back to (B) for his word) · READ's change of cells read
changing an observable (`CorrectStmt` compares only output and the DONE/REJECT outcome, so it should not) · a statement that has to
change beyond its language to go through.

## ADDENDUM 1 (same head, same hour, before any Deflate5 or Cost5 code): C_bit = 1, not 4
DEFLATE's own counted bound for one `BITc` call is `bit_stepsN`: **≤ 250 ⟶₂ steps** (deflate/VIRDeflate/Fit.lean). Four bits per
step is > 1000 steps, against KSTEP = 512. So **C_bit = 1**: READ takes one bit per step through bitR, as it takes one bit per step
from the table now. READ's collapse is then the TABLE (dropped, and its 2048 cells' fill steps with it) and the table read per bit
(replaced by the call); its per-bit loop across steps stays. LV9 counts what is removed; it does not need READ's step count to fall.
This is the map's own rule ("C is cut by an addendum, never by raising KSTEP"), applied before any code.

## ADDENDUM 2 (the 72nd head, after the unseal and BEFORE any Deflate5 code): TABLE is KEPT, lifted and unread
Correct.lean's simulation invariant `Rel` carries `bits : BitsUpTo f 2048`, the TABLE's contents (Correct.lean around line 224).
Dropping TABLE changes Rel and the opening steps of every run, and re-proves the invariant for no gain in LV8's statements. So
**TABLE stays as `lift tableN`**: it fills the table, and after READ and DECODE call bitR nobody reads it. LV9 does NOT count it as
removed. READ's and DECODE's collapse is the table READ per bit, replaced by the call. Pricing read at the same time: Correct's
SCOPY is `scopy_next` (one byte) + `scopy_run` (induction on k). Chunked, it becomes c ≤ 32 bytes per step, and Rel holds at each
chunk boundary (pos + 8c, out.push of c bytes). COPY has the same shape (Correct.lean around line 1719). Both changes stay inside
the mode's own lemmas.

## ADDENDUM 3 (the 73rd head, before Deflate5): the lift, bridge (i), and why chunking keeps N
- **Lift5.lean**: `run₅_ι : run₅ n (ιC c) = ιC (run₂ n c)` at every fuel n, from `stepFn₅_ι` (CE both ways plus the soundness and
  completeness of both step functions). Every lifted mode's `stepS` fact therefore carries by one rewrite at KSTEP.
- **Bridge5.lean** (bridge (i)): `Sole σ p L` (the store owns one region and no other cell). `RegionAt.world` and `World.regionAt`
  convert between the routines' absolute contents and DEFLATE's relative ones on a Sole store. `initStore_sole` holds. Every step
  must also preserve Sole: that is owed per mode, alongside its World lemma.
- **Chunking keeps the statements' bounds.** SafetyStmt is `∃ k ≤ N b.size om` and CorrectStmt is `∃ k`. Both bound the step count
  from ABOVE, so a run that takes fewer steps (≤ 32 bytes per SCOPY/COPY step) satisfies the same N. Correct.lean consumes SCOPY and
  COPY only through `scopy_run` (l.980) and `copy_run` (l.1717), and their callers (l.1094, l.1945) use only the end state.
  Bridge (ii) is therefore those two inductions plus one chunk-step lemma each, as Addendum 2 priced it.

## ADDENDUM 4 (the 73rd head): four modes done in DEFLATE's terms, and what remains
Each of these has its chunked ⟶₅ term, both branch triples over RegionAt (no content premise, LV7), a Cost₅ within the dispatch's
share, the run at every fuel above that cost (`run_of_triple₅`), and the World form on a Sole store (bridge (i)):

| mode | file | routine | chunk | cost (⟶₅ steps) |
|---|---|---|---|---|
| SCOPY | Scopy5, ScopyCost5, ScopyRun5, ScopyWorld5 | copyWithinR | min(PEND, 32) | 4·c + 13 ≤ 141 |
| COPY | Copy5, CopyRun5 | copyWithinR (overlap allowed: cwF is the forward copy) | min(PEND, 32) | 4·c + 12 ≤ 140 |
| REP | Rep5 | fillR | min(PEND, 32) | 3·c + 13 ≤ 109 |
| BUILD ZERO | Zero5 | fillR | all 16 − j remaining, INDEX := 16 | 3·(16 − j) + 8 ≤ 56 |

ZERO keeps BUILD's step structure: the next step meets DEFLATE's own end branch (PHASE := 1, INDEX := 0) unchanged, so Correct's
BUILD cases move only by the count of ZERO steps. BUILD's phases 1–4 stay lifted.
Remaining for LV8: FIXLENS (fillR, the chunk must stop at each of the run boundaries 144/256/280/288/318); READ and DECODE (bitR,
C_bit = 1); then the assembly: the dispatch over Tm₅ with the lifted modes by `run₅_ι`, `stepS₅`, and Correct's SCOPY/COPY/REP/
ZERO cases re-proved over `chunk_run` (Addendum 3) with each mode's World lemma, plus the Sole preservation every lifted mode owes.

## ADDENDUM 5 (the 74th head, after READ and DECODE and BEFORE any assembly code): the assembly by REFINEMENT
READ and DECODE are done (Decode5, ReadRun5, DecodeRun5 at 6d4e8a4): both triples, Cost₅ (READ 276 / 6, DECODE 280 / 8 ⟶₅
steps, each ≤ KSTEP − 29 = 483), the run at fuel, and the World form. **All of LV8's re-expressed modes are now proved in
DEFLATE's terms.** For the assembly, this addendum REPLACES Addendum 3's plan of re-proving Correct's chunked cases over
`chunk_run`. DEFLATE's two proved statements are used as they stand, through `stepSafe`, `safety` and `correct`. Correct.lean and
Safety.lean are not opened.
- **The step.** `stepT₅` loads MODE and dispatches over the 28 modes, as `dispN modes` does. SCOPY, COPY, REP, FIXLENS, READ and
  DECODE use their Tm₅ terms, and BUILD's phase dispatch uses zeroT₅ at phase 0. Every other mode is DEFLATE's own NT, lifted by ι.
  `stepS₅` and `iterS₅` are `stepS` and `iterS` with run₅ in place of run₂, at the same KSTEP and the same world capability.
- **The one per-mode obligation, `Refine₅`.** On a store with `World σ p L0 f`, `Sole σ p L0` and `Inv b om lit f`, for every
  non-terminal mode: `∃ j ≥ 1, ∃ σ', stepS₅ p σ = some σ' ∧ iterS p j σ = some σ'`. The count j is 1 for a lifted mode (`run₅_ι`)
  and for READ and DECODE (the bit bitR returns is the table's bit, from Inv). It is c = min(PEND, 32) for SCOPY, COPY and REP,
  the cells up to the run boundary for FIXLENS, and 16 − INDEX for ZERO. Each case is the mode's World lemma, set against DEFLATE's
  own per-step lemma iterated j times, which is `chunk_run`'s shape on the DEFLATE side.
- **Owed beside it.** (i) A store is determined by World and Sole: two Sole stores with the same contents are equal. (ii) Every
  DEFLATE step preserves Sole (Addendum 3's "Sole preservation", now owed once, on the DEFLATE side, for the whole step).
- **SafetyStmt₅** follows from `stepSafe` + Refine₅. A DEFLATE run keeps World ∧ Inv (StepSafe) and Sole (ii), and each L5 step
  takes ≥ 1 DEFLATE step, so the L5 run reaches DONE or REJECT within the same N.
- **CorrectStmt₅** follows from `correct` + `safety` + determinism. DONE and REJECT are fixpoints of stepS (`dispN` returns the
  world unchanged on an unmatched mode). The L5 run visits a subsequence of DEFLATE's run, so both reach the same first terminal
  store, with the same mode and output.
- **What would show this wrong:** a Refine₅ case that needs a bound Inv does not give (DECODE's table bounds and SCOPY's output
  room are the likeliest to check first); a step whose store World and Sole do not determine; a terminal mode that is not a
  fixpoint of stepS. Any one of these sends the case back to Addendum 3's route for that mode only.

## ADDENDUM 6 (the 74th head, after the outer argument and the lifted cases): a FINDING — Inv does not carry the table
Built (addee84 and above): `safety₅_of : Refine₅ → SafetyStmt₅` and `correct₅_of : Refine₅ → CorrectStmt₅` (Outer5); the
dispatch (Assembly5, Dispatch5); owed items (i) `sole_world_eq` and (ii) `stepS_sole` (SolePres5: DEFLATE's step only loads and
stores, `opFree_stepT` by `decide`); and **Refine₅ on 21 lifted modes plus every terminal or absent mode** (`refine_lifted`).
**The finding, which is the first item on this addendum's own "what would show it wrong" list:** Safety's `Inv` says only that
each TABLE cell is 0 or 1 (`InvG.bits`). That cell 8v + i holds `bitAt v i` is `BitsUpTo f 2048`, which lives in Correct's `Rel`.
Correct proves `Rel` along the spec program's simulation (`Sim`), not as a per-step invariant, and neither `StepSafe` nor
`ModeSafe` exports which cells a step writes. So READ's and DECODE's Refine₅ (the bit from bitR is DEFLATE's table bit) has no
premise to stand on. SCOPY, COPY, REP, FIXLENS and BUILD ZERO never read the table and are unaffected.
- **Fork, posted with the recommendation, proceeding on (T):** (T) a table invariant `Tab f := f cMODE ≠ mTABLE → BitsUpTo f
  2048`, shown preserved by every DEFLATE step (TABLE's own run establishes it, as `table_run` does; every other mode writes
  only cells outside [20, 2068)), and added to Refine₅'s hypothesis and to the outer argument's run invariant. (A3) for READ and
  DECODE only: re-prove their cases inside Correct's simulation. (K) keep READ and DECODE reading the table (no bitR in DEFLATE;
  LV9's count for bitR moves to the router alone).
- (T) is per-mode work on DEFLATE's own step lemmas, outside Correct and Safety. It does not change any statement.
