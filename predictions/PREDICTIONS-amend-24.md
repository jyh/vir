# PREDICTIONS amendment 24 — layer L5, the standard library (OBJECT-L5)

Written 2026-11-13 by the 71st vir head, AFTER the OBJECT-L5 pin (vir a35589c, `object-L5/OBJECT-L5.md` blob fd022757) and BEFORE
either arm's first L5 file, as the 11-13 council's ruling orders. Every clause assumes J1–J5 at (a), and all five were ruled so.
The labels are LV1–LV11 (layer five), chosen because no label of that form exists in this repository at the pin.

**What was known when this was written**, so that no prediction can claim to be blind to it: both arms closed L4 (Lean 4017931,
MetaPRL d257d2f29; RESULTS-10, where the MetaPRL arm's Q5 wf rate came in at 41/6 against L2's 42/6, FALSIFIED by one label, and
its Q4 direction REVERSED). DEFLATE and the compiler are Lean-only and on master (RESULTS-11, RESULTS-12): S1, S2, their
composition, K5's no-overflow, the generic loader, K7-a's router through S1∘S2, and the driver's L2 half (`driver_l2`,
`deflate_driver`). S3 waits on the x86lean C3 library. No L5 file exists on either arm (the pin's own census, with controls).
**The rule from the 11-06 council binds L5 too:** past ~100 tactic applications in one proof, the arm stops and systematizes, and
tactic-building time is a SEPARATE ledger line. No row below predicts a tactic count.

## Declarations owed by each arm before its first L5 file (posted on the bus, quoted into the L5 RESULTS)
Each arm's L4-closed sha (LV1's base); where the L1′ type former, ⊢₅ and the conservative-extension theorem live (files, sha);
whether L1′ EXTENDS ⊢₂'s types in place or is a new type and judgement with an embedding of ⊢₂ (this choice decides how LV1 is
read, and it is declared, not discovered); the form of a capability-annotated arrow (a list, a multiset, or a Δ in the existing
form); the five routines' names and their triples, before their proofs.

## The predictions (scored by the harness from the artifacts; each extractor added red first, before scoring)
- **LV1 (L1–L4 untouched, W8 at L5).** W8 over `l1/`, `l2/`, `l3/`, `l4/` (Lean) and `virl1_*`…`virl4_*` (MetaPRL), from the
  L4-closed sha to the L5-closed sha: 0 definitions edited on both arms. L1′ is built as a NEW type former and judgement with an
  embedding of ⊢₂, not as an edit of L2's types. **FALSIFIED** for an arm by ≥ 1 edited definition; an arm that declared "in
  place" is FALSIFIED BY ITS DECLARATION, and the RESULTS print that cause beside the count.
- **LV2 (no new axiom or prim).** Lean: `#print axioms` within propext · Classical.choice · Quot.sound for every L5 theorem.
  MetaPRL: 0 prims in `virl5_*`, framework files beside. **FALSIFIED** by ≥ 1.
- **LV3 (CE both directions, the second non-identity CE).** Every `Γ ; Δ ⊢₂ e : τ` is a ⊢₅ judgement with capability-free
  arrows, and the program steps under ⟶₅ exactly as under ⟶₂ (OBJECT-L5 J1 (a): *"every L2 program means what it meant"*).
  HOLDS on both arms; C5 reported. **FALSIFIED** for an arm if the theorem needs a premise beyond ⊢₂.
- **LV4 (the fix rule is where L1′ pays).** Of the L1′ semantic-typing proof's cases, the `fix` case (a body checked with its
  annotated Δ, OBJECT-L5 J1 (a)) has the largest C5 on BOTH arms. Direction predicted; the ratio to the next case is reported.
- **LV5 (Lean pays in transport at the call).** Lean: CAST_RE (`count.py`, the L3 Z2 extractor: `HEq`/`cast`/`Eq.mpr`/`Eq.rec`/`▸`/
  `≍` …) over the L1′ files reads ≥ 1, and ≥ half of the hits sit in the application or `fix` case (where an annotated Δ meets the
  caller's split). **FALSIFIED** if 0, or if fewer than half sit there. MetaPRL: reported, no direction.
- **LV6 (MetaPRL pays in well-formedness).** MetaPRL's `[wf]` per-rule rate over the L1′ rules ≥ its L2 rate (42/6), read on
  the same reading as amend-21 Q5. Lean: no analogue (reported 0). The prediction is made knowing that Q5 at L4 FALSIFIED by one
  label; it is not softened for that.
- **LV7 (a routine's premise names sizes, never contents).** Each of the five routines (copy, fill, compare, bounded scan, the bit
  reader) has a triple whose precondition names only its regions, their sizes and its index bounds: no premise on the contents
  (DEFLATE's D7 shape, OBJECT-L5 §2). **FALSIFIED** for a routine by one such premise, on either arm.
- **LV8 (the library abstracts).** DEFLATE and the router re-expressed over the library carry their original theorems (Lean:
  `safety`, `deflate_driver`'s L2 statement, `router_refines`' source statement; MetaPRL, where DEFLATE was never built: the router's run_tokens₄, `n4_v`) with 0 new
  lemmas that unfold a routine's body: every use of a routine goes through its triple. **FALSIFIED** by ≥ 1 such lemma
  (OBJECT-L5 §2, "the library has not abstracted").
- **LV9 (the code collapses).** Re-expressed over the library, DEFLATE's L2 step program and the L3 router each contain ≥ 1 call
  to a routine where they hand-coded the loop before; the AST nodes removed are COUNTED (per program, per routine). Direction
  (> 0 on each) predicted; the count is reported.
- **LV10 (no duplication at J2 (a)).** Among the five routines, the number that differ from another ONLY in an int encoding of
  their element (J2's polymorphism trigger) is 0. **FALSIFIED** by ≥ 1, and a falsification is the measured duplication that
  OBJECT-L5 names as polymorphism's trigger (a fork for a sitting, not a change made here).
- **LV11 (the compiler takes L1′ without a per-routine lemma; scored after S3).** The compiler's L1′ extension states ONE
  ∀-program theorem per stage (K2's form), and the closure's capability words are covered by the generic layout premise (K6's
  population widened by a declaration, not by a lemma per routine). **FALSIFIED** by ≥ 1 per-routine lemma in the compiler.
  UNSCORED until S3 closes; it is written now so that it precedes the extension.
- C1–C6 keep their amend-1..23 definitions on the L5 files and are reported without direction.

## What would show this amendment unfair
an L5 proof file on either arm with a commit time before this file's sha · OBJECT-L5 edited after its pin · an arm that reads the
other's L5 files · a count taken from files or a sha the arm did not name first · the two arms given different goal-state
affordances · LV5's or LV6's reading changed after the first L1′ file (each extractor is the one named here, added red first) ·
LV8's original theorems restated in a weaker form to make the re-expression go through (the statements are the ones on master at
caf23c0, cited by name).
