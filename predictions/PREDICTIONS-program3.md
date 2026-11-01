# Predictions, PROGRAM 3 (the A.1/A.2 safety theorem, inputs/program3-inputs.md K1–K4). Written by vir 2026-11-01, BEFORE either arm's first proof on program 3

**Every extractor convention is fixed IN ADVANCE.** This is the point of program 3: P2's verdict was provisional only because its C2 conventions post-dated the proofs. The harness is `harness/count.py` at the sha this file is committed with (the same commit adds the program-3 extractors, red-first on a fixture: selftest ARM9). No later harness change applies to program 3 unless it is an amendment that says it post-dates a proof.
- **Lean C1coe** = the occurrences of `↑`, `.val`, `Subtype.val` and `.property` in the ELABORATED term of `theorem VIR.route_acl_safe` (`lean/out/terms.txt`, `#print` of that theorem). The HEq class (with `≍`) is reported beside it as P3.C1heq.
- **Lean C2** = `(by ` side proofs in the scored theorem's source block (P3.C2cond).
- **MetaPRL C2** = C2gen: the direct children of each refine (`=== CHILDREN k:`), skipping `omegaT` closers and applying the path rule to the lemma replay (RESULTS-2 addendum 3). MetaPRL C1 = cast tokens in `steps/*.mp` (as for programs 1–2).
- C3 = the aux rules used by the scored chain, C4 = axioms beyond the standard three, C5chain = whitespace tokens of the scored chain.

## The predictions
- **T1 (Lean pays the boundary as coercions, §5.1):** Lean C1coe ≥ 1, and MetaPRL C1 = 0. **FALSIFIED if** Lean C1coe = 0.
- **T2 (CTT pays the boundary as well-formedness, §5.1 "Gate 2"):** MetaPRL C2genWf ≥ 1, strictly greater than Lean's P3.C2cond. **FALSIFIED if** MetaPRL C2genWf ≤ Lean P3.C2cond.
- **T3 (a safety proof needs no fusion rules):** C3strict = 0 on both arms (no aux rewrite rule is used). **FALSIFIED for an arm if** its scored chain uses an aux rule.
- **T4:** C4 = 0 on both arms.
- **T5 (exploratory, no direction):** C5chain on both arms, and whether a case split proves K3 directly (expected yes on both).

After this file's sha is posted, it is never edited. Amendments are new files, dated, saying which proofs preceded them.
