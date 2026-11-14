# L5 — the Lean arm's scores so far (amend-24), each read by a harness arm against a reading DECLARED before its count

The RESULTS file for L5 comes when both arms close. These are the Lean cells, and each one points at its record.

| prediction | Lean cell | how it is read | record |
|---|---|---|---|
| LV2 (no new axiom) | **HOLDS**: audit-040, 243 rows, 0 outside the three, 0 sorryAx; control audit-040c reads sorryAx | `count.py --arm l5` (ARM60), the newest non-control audit | l5/out/counts-l5.tsv |
| LV4 (the fix case is the largest) | **FALSIFIED**: the larger fix arm (`pres₅.appKFix`, 151 C5 tokens) against the largest other arm (`pres₅.op`, 722), ratio 0.209. Robust to the cut: the two fix arms summed (264, BESIDE) are still below `op`, and appKFix also trails progress's `letK` (163) and `letE` (160) | DECLARATIONS-LEAN Addendum 7 (b362542, before the count); `count.py --arm l5` (ARM60, red first, nested-arm mutant KILLED). Arms 15 + 17 = the Step₅ and RT₅ constructor counts | l5/out/counts-l5.tsv |
| LV8 (the library abstracts) | DEFLATE: **HOLDS** (safety₅ and correct₅, 0 lemmas that unfold a routine body). Router: **VACUOUS** (0 calls: V-F8) | LV8-MAP Addenda 8 and 10 | l5/VIRL5/Final5.lean, Router5.lean |
| LV9 (the code collapses) | **FALSIFIED** for both: DEFLATE 7 calls, −88 nodes; router 0 and 0 | DECLARATIONS-LEAN Addendum 6; `count.py --arm lv9` (ARM59) | l5/out/counts-lv9.tsv; LV8-MAP Addendum 11 |

Why LV4 falls (a reading, not a count): the memory operations share ONE ⟶₅ rule (`Step₅.op`), so preservation's op arm carries
alloc, load, store and free together, each with its own store reasoning. The fix rule's L1′ cost (the annotated Δ) is real, but
it is smaller than that. LV1, LV3, LV5, LV6, LV7, LV10 and LV11 are not read here.
