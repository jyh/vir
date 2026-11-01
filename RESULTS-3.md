# RESULTS 3 — PROGRAM 3 (the A.1/A.2 safety theorem over F2), the LEAN arm first (2026-11-01, the 2nd vir head)

Inputs `inputs/program3-inputs.md` and predictions `predictions/PREDICTIONS-program3.md`, with the extractors in `harness/count.py`, all pinned at vir 98d9329 BEFORE either arm's first proof. **This file's Lean section was committed before vir read any MetaPRL program-3 result.**

## Lean (`lean/VIR/Router3.lean`, `route_acl_safe`; build-021 `saltbuild EXIT=0` on its first build; audit-011 EXIT=0; axioms [propext, Quot.sound])
ValidFrame is A.1's Prop-carrying subtype of `ByteArray`, and F2 is applied to the frame's whole-buffer slice `wholeSlice b.val`. The proof is a case split on F2's guards (`unfold F2; simp only [guard, readU32, letLin]; split; split`), with no rewrite chain.
| count | value (H) |
|---|---|
| **C1coe** | **54** (all of them `.val`, from `b.val`. The printer writes the coercion as `b.val`, never `↑b`; `.property` and `Subtype.val` are 0) |
| C1heq | 0 |
| C2cond | 0 |
| C3 (aux used) | 0 |
| C4 | 0 |
| C5chain | 38 |
⚠️ **What C1coe's 54 measures:** occurrences of the projection in the ELABORATED term. The source writes `b.val` ONCE, in the statement (`wholeSlice b.val`), and the elaborator repeats it at every point the case split mentions the buffer's size or bytes. The number is the pinned extractor's, as preregistered, and it is a count of how often the boundary shows in the proof term, not of how often an author wrote it.
## Lean's side of the predictions
- **T1 (Lean C1coe ≥ 1): HOLDS on the Lean side (54).** MetaPRL C1 = 0 is owed by mojave's arm.
- **T2: owed.** Lean's P3.C2cond is 0, so T2 holds iff MetaPRL C2genWf ≥ 1.
- **T3: holds for Lean** (C3 0, no aux rule). **T4: holds for Lean** (C4 0).
- **T5:** Lean C5chain 38. The case split IS the proof, as T5 expected.

## MetaPRL: OWED (mojave's program-3 arm; the harness reads it at `--program 3` once it lands)
