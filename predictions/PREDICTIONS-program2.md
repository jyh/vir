# Preregistered predictions for PROGRAM 2 (O95), pinned BEFORE either arm's first proof on it

Inputs: `inputs/program2-inputs.md` (same commit). Counts and extractors: PREDICTIONS.md + amend-1..6, unchanged. The program-1 figures are the baseline (RESULTS-1).
Representation, fixed now (the conflict of interest is declared as for program 1): the Lean arm is scored on L-IDX shallow (`router2_fusion`) and also reports L-DEEP (`router2_fusion_deep_steps`). MetaPRL stays on mojave's model (B).

- **Q1 (Lean pays more at a DYNAMIC index):** C1heq on L-IDX's program-2 path ≥ program 1's 5, because the indices now carry a variable offset (`n − 12 − (off − 12)` vs `n − off`, equal only under `12 ≤ off`). MetaPRL C1 = 0. **FALSIFIED if** L-IDX C1heq < 5.
- **Q2 (both pay in side conditions):** C2cond strictly greater than in program 1 on BOTH arms (Lean > 3, MetaPRL C2genCond > 10), because the guard's bound must reach the slice step. **FALSIFIED for an arm if** its C2cond ≤ its program-1 figure.
- **Q3 (a context-dependent rewrite is needed):** each arm needs ≥ 1 aux rule BEYOND its program-1 set: a rewrite whose side condition comes from an enclosing guard. L-DEEP's `Step` has no hypothesis context, so **C3deep ≥ 6**. **FALSIFIED for an arm if** its program-2 C3 equals its program-1 C3 under the same reading.
- **Q4 (MetaPRL F1 recurs):** the conditional rewrite's condition mentions a READ-bound variable (`off`), so MetaPRL again cannot fire it under that binder without first unfolding the reads, and M-F1 recurs. **FALSIFIED if** the MetaPRL chain fires it under the binder directly.
- **Q5 (exploratory, no direction):** C5chain and C6 for both arms. Whether a case-split shortcut exists (expected yes).

After this file's sha is posted, it is never edited. Amendments are new files, dated, saying which proofs preceded them.
