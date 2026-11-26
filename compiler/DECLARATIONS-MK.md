# DECLARATIONS — amend-28's instruments (the MetaPRL compiler arm, option (iii))

Written 2026-11-25 by the 91st vir head, **before any S1 count of the MetaPRL arm exists** (mojave's S1 proofs began at 21:41 PST; the
arm has posted no count). Each instrument is declared here before it reads either arm's stage.

## MK4 — size, per stage (S1, S2, S3)
- **Measure:** in-layer PROOF CLOSURE in C5 tokens, l4/DECLARATIONS-LEAN Addendum 7's measure. A closure is the fixpoint over proof
  blocks named by whole identifier. Short names also match, so the figure is an UPPER BOUND: on the Lean S1, `WN.trans` enters through
  `.trans`. Every row prints beside it the root alone, the closure with definitions, the file, and the imported names not followed.
- **Lean half: `count.py --arm vircl <vir root>`** (selftest ARM69, mutant: a one-pass closure, KILLED).
  - S1 = `s1_refines` and S2 = `s2_refines`, both over compiler/VIRC.
  - S3 = `s3_refines` over s3/S3, with VIRC, L1 and L2 imported. Beside it, S3c = `s3_refines_from_s2`, the composed form.
  - The Lean figures are measured but NOT published until scoring, so the arm cannot read a target.
- **MetaPRL half: declared at the arm's first stage close, before its counts are read, as metaprll4 was.** It is the same closure over
  the arm's stage modules, with the stage roots posted by the arm. Its fixture follows the ARM57 pattern.
- **Verdict:** MetaPRL / Lean ≥ 3 at each stage on the PRIMARY. The beside readings are printed, and none of them decides.

## MK5 — wf/typing share
Declared with MK4's MetaPRL half: a classifier over the arm's interactive rules in its S1–S3 modules, by STATEMENT, with its population
printed and a red fixture.
