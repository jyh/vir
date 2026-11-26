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
- **`count.py --arm mk5 <tree>`**, with `VIR_MK5_PREFIXES` set to the arm's stage-module prefixes (posted by the arm). Selftest ARM70
  has two mutants, both KILLED: classification by NAME, and classification of the whole statement instead of the conclusion.
- **Classified by the GOAL's CONCLUSION**, which is the text after the rule's last `>-`.
  - wf = a membership `X in T` with no `=` before its `in`, or a `type`/`Type` judgement.
  - An equality `a = b in T` counts as eq, not wf.
  - `interactive_rw` is printed beside the count and kept out of the population. Commented-out rules are not counted.
- **Verdict:** wf ≥ 20 % of the population.
- **Population control, read 2026-11-25 AFTER the row was written and before any compiler-arm count.** On the arm's L4 modules
  (`virl4_`) at d257d2f29, mk5 reads 1,127 rules, 378 wf (type 28 + member 350), 335‰, and 409 eq. So 20 % sits below what the arm's
  own L4 already shows. The row is not moved. RESULTS-17 will print this beside MK5's verdict, because a threshold below the arm's
  base rate is weak evidence for "where MetaPRL pays".
