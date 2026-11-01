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
| C5chain | ~~38~~ **32** (addendum 1: 6 of the 38 tokens were Rules.lean's header) |
⚠️ **What C1coe's 54 measures:** occurrences of the projection in the ELABORATED term. The source writes `b.val` ONCE, in the statement (`wholeSlice b.val`), and the elaborator repeats it at every point the case split mentions the buffer's size or bytes. The number is the pinned extractor's, as preregistered, and it is a count of how often the boundary shows in the proof term, not of how often an author wrote it.
## Lean's side of the predictions
- **T1 (Lean C1coe ≥ 1): HOLDS on the Lean side (54).** MetaPRL C1 = 0 is owed by mojave's arm.
- **T2: owed.** Lean's P3.C2cond is 0, so T2 holds iff MetaPRL C2genWf ≥ 1.
- **T3: holds for Lean** (C3 0, no aux rule). **T4: holds for Lean** (C4 0).
- **T5:** Lean C5chain ~~38~~ **32** (addendum 1). The case split IS the proof, as T5 expected.

## MetaPRL: OWED (mojave's program-3 arm; the harness reads it at `--program 3` once it lands)

## ADDENDUM 1 (2026-11-01, the 2nd vir head): a harness defect in C5chain found at row 25, plus amend-9 scored
**The defect (vir's own):** the Lean extractor concatenates every `VIR/*.lean` in sorted order and splits the result into declaration blocks. A proof that is the LAST declaration of its file therefore absorbed the NEXT file's header (`import …`, `namespace …`) and its own `end VIR`. Only C5chain read those tokens. **No C1, C2, C3, C3deep or C4 figure moved.** The figures it inflated:
- route_acl_safe 38 → **32** (6 tokens of Rules.lean's header)
- router2_fusion 202 → **196** (RESULTS-2 Q5)
- router2z_fusion 220 → **214** (RESULTS-2 addendum 4)
- route_acl_safe_flat 40 → 34

Program 1's C5chain (84) and every deep chain are unchanged, because none of them ends its file. **Fixed:** a sentinel declaration between files, and a chain that ends at its namespace's `end`. Selftest ARM10 is red-backwards: the pre-fix harness FAILS it, and the fixed one passes (rc 0). **Copies corrected in place:** RESULTS-2 (Q5 · the program-2 table · addendum 4) · SUMMARY-first-act (Q5) · this file's table and T5. No verdict depended on C5chain, because Q5 and T5 are exploratory.

**amend-9 (pinned at vir bbeac50 BEFORE the variant), scored on `route_acl_safe_flat`** (build-022 `saltbuild EXIT=0`, audit-012; axioms [propext, Quot.sound]):
- **F1 HOLDS:** P3F.C1coe **0**. With ValidFrame as a hypothesis on a bare buffer, the 54 coercions vanish, so Lean's boundary cost on program 3 is the SUBTYPE REPRESENTATION, the same shape as P1b for slices.
- **F2 HOLDS:** the proof builds with `hv` CLEARED before it. ValidFrame's refinement carries NO load in K3, because F2 re-checks the length and the magic itself. ⇒ **A finding about the object:** in A.1's `route_acl_safe` the subtype is decoration, and the guards in the term already discharge it.
- **F3, read both ways:** on the letter it is FALSIFIED (34 ≠ 32). The difference is exactly the 2 tokens of the preregistered `clear hv`, so the remaining script is token-for-token the same. *(F3's own text quotes "38", the leaky figure. A prediction file is never edited, so the correction lives here.)*
