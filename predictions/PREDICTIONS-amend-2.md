# Amendment 2 to PREDICTIONS.md (2026-11-01 00:3x, vir)

**WRITTEN BEFORE THE LEAN ARM'S FIRST PROOF.** At this commit `lean/` holds a lakefile and a toolchain file and no `.lean` source.

## A degree of freedom the predictions left open, closed now
PREDICTIONS.md fixed the Lean SLICE representation (L-IDX, L-FLAT). It did not fix the TERM representation, and that choice moves C3 (aux rules) and C2.
**Fixed:** the Lean arm uses a SHALLOW, continuation-passing embedding. Each VIR form (`guard` · `read_u32` · `advance` · `let_lin` · `let_atom` · `return` · `drop`) is a Lean definition, HOAS binders are Lean functions, and `guard` is a dependent `if` (its ok-branch receives the proof).
I4 is proved as EQUALITY OF DENOTATIONS (`U b0 st = F b0 st` in `Out`), which I4 allows ("the arm says which").
The 7 GIVEN rules are stated and proved as Lean theorems over this embedding. An AUX rule is a theorem named `aux_*` that the I4 proof uses.

## What this does to the predictions, said in advance
- **P3 is now at risk on the Lean side, and that is the point of saying so before the proof.** In a shallow embedding several E8 commutations (a pure read past a guard, an advance past a let_lin) may hold by `rfl` or by `split`, and the proof may need no stated lemma for them. If Lean's C3 ≤ 2, P3 is FALSIFIED for Lean. The result post will say whether the absorption came from the embedding.
- **P1 is unaffected.** `slice_fuse` still relates `Slice (n - i - j)` and `Slice (n - (i + j))`, which are not definitionally equal for variable `n i j`.
- A DEEP embedding (PHOAS) of A.2 is NOT built in this campaign's first act. It goes on the queue as a later variant if the comparison needs it.
