# MAP — what the router work showed, and what L4 pins (one page, for review)

Written 2026-11-06 by the 25th vir head, the day L4 was pinned. Every figure below is a row of a RESULTS file, which is
named. This page adds no measurement of its own. Its limits are listed at the bottom.

## 1. What the router work demonstrated (programs 1–3, then L1–L3)
- **The frozen-object method works as an instrument.** One frozen appendix, two arms that did not read each other's work, and
  predictions pinned before the first proof. Every count is re-derived from the artifacts by `harness/reproduce.sh`, which reads
  rc 0 over 22 files. The method also caught its own slips: the conventions written after a proof are each marked in their file.
- **Each logic pays somewhere different, and the places can be measured.** Lean pays at dependent indices: 20 HEq at
  `slice_fuse` (P1), and 0 on a flat slice, so that cost comes from the representation (P1b). Program 3's boundary costs Lean
  54 coercions (T1), and the subtype accounts for all 54 (F1). CTT pays in well-formedness: 7 wf obligations on program 3 (T2),
  and 13 against 9 on program 1, a margin flagged as provisional (P2). The trusted base is equal on both arms (P4, B2, B3).
- **A.4 as written is not a refinement.** paris's kernel-checked witnesses show it (P5, E2/E3). A.4 AS REPAIRED refines F for
  all states, and `compose/` joins that to the specification as ONE term from U to x86-64 (`lowered_refines_U`). Rate limiting
  holds at the machine over two calls (`two_emits_same_sender`), and every exit has a witness (RESULTS-3, SUMMARY).
- **The general language holds the router, and the cost shows up where we said it would.** L1, the typed pure core, closed on
  both arms. L2, the imperative core with linear capabilities and a frame rule, closed on Lean: 205 theorems within the standard
  three axioms, and Y5 semantic typing with no fuel and no bounds. Inside L2, the router costs 3,874 proof tokens against 1,617 in
  the special language (Z9). Two of the size predictions failed: Z4 (R3 was not the largest proof) and Z8-R8 (17 lines > 15)
  (RESULTS-6/7/8).
- **The council's open finding, Y5 on MetaPRL.** The same soundness theorem costs MetaPRL far more. MetaPRL has needed three
  carvings (D8, D9, D8a), which are invariants Lean gets from its intrinsic typing. This is the extrinsic-against-intrinsic
  hypothesis, with tooling as a confound. SLang (amend-20) is the experiment that separates the two causes. Y5 runs to the 11-08
  cap and stops early if a fourth gap appears.

## 2. What L4 pins (object-L4/OBJECT-L4.md · inputs/L4-programs.md · predictions/PREDICTIONS-amend-21.md)
- **Language.** Structured `par e₁ e₂` (H1). A non-linear `lock` handle: `newlock` consumes a capability, `acquire` returns it and
  `release` gives it back. The lock's invariant is a predicate on one region, stated in the logic and never in a type (H2).
- **Meaning.** Small-step interleaving ⟶₄, with no denotation at L4 (H3). The triple quantifies over every interleaving, and the
  conservative-extension theorem is stated on ⟶. Deadlock freedom is outside partial correctness by declaration, so nobody should
  count it as missing.
- **Programs (H4).** N1, a locked counter that ends at 2. N2, a lock-free race, which must be ILL-TYPED. N3, a release that breaks
  the invariant, which must have NO triple. N4, the L3 router run by two threads sharing a locked bucket region, with run_tokens₄
  over every interleaving.
- **H5.** Region invariants cannot state N1's 2 or N4's token bound. Those VALUE claims are therefore configuration invariants on
  ⟶₄*, and the logic proves SAFETY: no data race, no negative bucket, and the invariant re-established at every release. Ghost
  state (b) is the named L4′.
- **Predictions Q1–Q8.** L1–L3 stay untouched, and no axiom or prim is added. The parallel rule costs Lean ≤ 3× its frame rule.
  The interleaving tax falls on the configuration invariants. MetaPRL's wf rate at L4 is at least its L2 rate. Typing alone
  excludes data races. CE holds both ways. Deadlock is exhibited and reported.

## 3. Where DEFLATE sits — a correction to "DEFLATE's step 1 if L4 is the compiler's object"
**L4 is not DEFLATE's object.** Inflate is sequential: it needs byte cells, loops, bounds and a sliding window, which is L2
(regions, load/store, `fix`) plus the L3 method. It needs no `par` or lock, so L4 neither helps nor blocks it. L4 is the layer
for the concurrent router, and later for the SMTP receiver's sessions.
The honest step 1 for DEFLATE is its own object: RFC 1951's decoder as the spec, zlib's `inflate` as the reference oracle, and
the program written in L2. Pinning that object is a separate decision.
**The compiler is not built either.** What exists is ONE hand lowering, A.4, proved against x86lean for program 1. A VIR → x86-64
compiler for L2 programs is the open first item in his list, and DEFLATE would be the first program run through it.

## Limits
Section 1 summarises verdicts scored under the readings their RESULTS files state. It re-reads none of them. The MetaPRL
columns for L2 Y5 and for L3 are OPEN. Section 3 is the seat's reading of the object, not a ruling.
