# L4 C5: where the tokens are (SEALED; a note for RESULTS-10 at the unseal, never a score)

Written 2026-11-06 by the 28th vir head, AFTER the figures in `harness/l4-counts-lean.tsv` (6fcfef8) were taken. **Everything below
is POST-HOC.** It explains the declared figures and is reported beside them. It does not replace them and adds no measure to any Q-row
(addendum 7 fixed the measure first). Reproduce: `l4_closure` from `harness/count.py` over `l4/VIRL4`, tokens per block grouped by file.

## Q3: par₄_rule 1,398 vs L2 frame 237 (5.90×, over the 3× line on PRIMARY)
- **frame (L2):** 4 blocks. `frame` 155 and three store-algebra lemmas 82. L2's `Triple` quantifies the frame store σf in its own
  definition, so `frame` just re-associates the store and re-uses `h`. It does no induction.
- **par₄_rule (L4):** 12 blocks. `safe₄_par` 627 is the interleaving induction on the step index (either side steps, or the join).
  The other blocks are `par₄_rule` 126, `safe₄_mono` 125, `glob_frame_out`/`glob_frame_in` 237 and `safe₄_ext` 109 (the lock table only
  grows), plus five smaller ones.
- **Reading.** The parallel rule needs an induction that the frame rule never did, because L2's triple builds the frame in and ⟶₄'s
  interleaving cannot be built in. Root-only (b) is 126 vs 155 and holds; file-level (d) is 7,273 vs 595 and does not. RESULTS gives
  the PRIMARY verdict and states (b)'s disagreement beside it.

## Q4: V 8,395 > S 7,557 (1.11; root-only (b) reverses, 418 vs 1,141)
- **By file.** V: RouterV.lean 7,036 · Values.lean 1,346 · Safe.lean 13. S: **Rules4.lean 4,883** · Programs.lean 1,355 ·
  Router4.lean 1,280 · Safe.lean 39.
- **Reading.** 65% of S's closure is the RULE LIBRARY (`safe₄_*`, `*₄_rule`). It is reusable and paid once for every program. V has no
  library: `th_step` 1,292 and `R4_step` 1,183 are N4's own configuration invariant. Outside the library, program-specific S is
  2,635 against V's 8,382 (3.2×). **This split is post-hoc and is not scored.** It shows that the direction Q4 predicted holds with a
  much larger margin per program than the declared ratio shows, and that the declared ratio is narrow because S pays for a library V
  never needed.
- The two closures share one block (`Ext.refl`, 13 tokens).

## Limits
Closure resolution is by name, including the last dotted component. Every member of the four closures was checked to appear as a
token in another member (0 members reached only through a differently qualified token), but a local binder that shares a lemma's
name would still pull that lemma in. The library/program split above follows file boundaries, not a rule from the bytes.
