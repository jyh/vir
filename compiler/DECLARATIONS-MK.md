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

## Addendum 1 — MK4's MetaPRL half, built 2026-11-26 before the arm's first stage close (92nd vir head)
Written before mojave posted any stage close or any count. At this time the arm had posted no stage roots, and no MetaPRL file was read
for this addendum. The reader is built and tested against a synthetic fixture only.
- **`count.py --arm vircm <tree>`** (selftest ARM71) uses metaprll4's in-layer closure (ARM57) over a working tree at the scored sha.
  - A row's C5 is its posted roots, plus every rule of the stage's POOL that a closure text names as a whole identifier (fixpoint), plus
    every pool `{| reduce |}` rule once a text invokes `reduceC`/`reduceT`. That last term makes the figure an UPPER BOUND, as on L4.
  - `VIR_MK4M_POOLS='S1=..;S2=..;S3=..'` holds module-filename prefixes. `VIR_MK4M_ROOTS` holds the arm's posted roots.
- **The pool is the Lean half's parallel.** On the Lean side, S1 and S2 share VIRC and S3 imports it, unfollowed. So S2's pool may hold
  S1's modules, and S3's pool holds S3's modules alone.
  - The pools are fixed from the arm's posted module list at its first stage close, before its counts are read, and recorded in a second
    addendum.
  - A stored rule of another vir module that a closure names is a **crossRef**: counted and listed beside, never followed. This matches
    the Lean half's imported names.
- Beside each row are the closure's rule list, roots-only tokens, refine steps, and crossRefs. Only `MK4.M.<S>.C5tok` is primary.
- ARM71 mutants, all KILLED: (a) a closure that stops at the roots' own names; (b) one that ignores the pool; (c) one that drops the
  reduce resource. A posted root with no derivation in its pool reads RED, never 0.

## Addendum 2 — the MetaPRL pools, MK5's prefixes and MK2/MK3's unit, fixed 2026-11-27 at the arm's POSTED S1 close (found not to be S1's close; below), before any MetaPRL count is scored (94th vir head)
Written after mojave posted S1 PROVED (bus @112,196,833: `virc1_sim` fresh 149/149 at metaprl `8c7ae9b48`, branch mojave/vir-s1e,
local) and before `vircm` or `mk5` was run on any MetaPRL compiler-arm sha. What was read to write it: the file names under
theories/vir at that sha, the rule names in `virc1_sim.ml`, and the arm's s1d/STEP-PLAN (tools `b83d456`), which names the three
roots of record. No proof text was read.
- **S1 scored sha: NOT FIXED HERE.** `8c7ae9b48` is NOT S1's close. A refuter pass over it (four read-only readers, two of
  them independently) found that it proves let/eff flattening `anf : L2 → L2` preserves the L2 step relation (`anf_step`,
  `anf_stuck`, `anf_run`). It does not prove the plan's S1: `compile1`, the function table and `fo2` are absent, and no theorem
  says the output is flat. The arm's own plan lists "S1-F0 (b) naming + fo2 + S1's theorem" as owed after `anf_run`. S1's sha is
  the commit at which S1's theorem is of record. It is fixed in a third addendum before S1's count is read.
- **`VIR_MK4M_POOLS='S1=virc1_;S2=virc1_,virc2_;S3=virc3_'`** — the comment's form in count.py, now fixed.
  - S1's pool is the three modules the arm posted for S1: `virc1_anf`, `virc1_lem`, `virc1_sim`.
  - S2's pool holds S1's modules too, as the Lean S2 shares VIRC with S1.
  - S3's pool is `virc3_` alone; stage X (`virx86`, a separate tree, the parallel of x86lean) and L2 (`virl2_*`) are crossRefs, as L1/L2
    and x86lean are imports the Lean half does not follow. If the arm names its S3 modules otherwise, that is recorded in a third
    addendum BEFORE S3's count is read, and the prefix is the only thing that may change.
- **`VIR_MK4M_ROOTS`: S1's roots are S1's theorem as the arm posts it at the true close.** If `anf_run`, `anf_step` and
  `anf_stuck` are in that theorem's closure, they are counted there. S2's and S3's roots are fixed the same way, from the arm's
  posts at those closes, before their counts, in this file.
- **A reading at 8c7ae9b48 exists and is SEALED as a sub-stage reading.** `vircm` was run once with roots
  `anf_run,anf_step,anf_stuck` before the refuter verdicts came back. It decides nothing and is not MK4's S1 row. It is printed
  beside S1 in RESULTS-17 as "flattening only".
- **`VIR_MK5_PREFIXES='virc1_,virc2_,virc3_'`** — the compiler stage modules. `virx86` (stage X) is kept out, as its Lean parallel
  (x86lean) is not in the Lean population either; mk5 on `virx86` alone may be printed beside, and decides nothing. MK5 is read once,
  at S3's close, over the sha that closes S3.
- **Publication:** as on the Lean half, the per-stage MetaPRL figures are measured as stages close and NOT published before RESULTS-17,
  so neither arm reads a target from the other.
- **MK2 and MK3: the unit.** No unit was declared before now. The unit is the seat-day of the arm's price brief (2026-11-16,
  "1 seat-day ≈ 8 h, the LESSONS ledger's unit"), because MK2's "< 4" and MK3's "2×" are both written against that brief's
  calibrated bands. This line is written AFTER the arm posted X+S1a figures in a 24 h unit. It is a disclosure, not a blind
  declaration. MK2's measure stays the prediction's own: the arm's posted start and end per stage, summed. Two readings are printed
  beside it: lit head time, and the commit-time reconstruction. MK3 is scored on whether the checkpoint fires at the TRUE S1 close,
  in this unit.
