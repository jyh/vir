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
