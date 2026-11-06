# PREDICTIONS amendment 21 — layer L4, concurrency (locks) (OBJECT-L4)

Drafted 2026-11-04 by the 18th vir head as §4 ("amend-20") of the L4 programs draft; PINNED 2026-11-06 by the 25th as this file,
in the same commit as `object-L4/OBJECT-L4.md` and `inputs/L4-programs.md`, BEFORE either arm's first L4 file. It is amend-21
because amend-20 went to SLang (PUBLIC #40, 11-05). Every clause assumes H1–H5 at their recommendations, and all five were ruled so;
no clause below is re-drafted. Q1–Q8 below are the draft's bytes.

**What was known when this was drafted (11-04):** the Lean L2 arm was complete on a sealed branch; the Lean L3 arm was built and
sealed; the MetaPRL arm was building L2 (Y5 not closed). No L4 file existed on either arm.

**What was known AT THE PIN (2026-11-06 ~10:1x PST), added beside the draft's paragraph above:** the Lean L3 arm is PUBLIC
(#41, RESULTS-8: Z4 and Z8-R8 FALSIFIED on the Lean column). The MetaPRL arm posted its L3 declarations (ae4c349b2) and is in
L2's Y5 step 8 (preservation, part 118g, virl2_sem 379/379 at 09:11), capped 11-08 EOD with a fourth-gap stop (council 11-06);
its L2 carries three carvings (D8 · D9 · D8a) that the Lean arm gets from its types. **So Q5's base, MetaPRL's L2 wf-premise rate,
is read from the L2 rules as declared and amended, and the count is taken when the arm's L2 is declared closed or unreached.**
No L4 file exists on either arm: `git log --all -S` in this repository reads 0 commits for `newlock`, `acquire` and `par e`
(control `y5_closed` 6), and 0 for `newlock` and `virl4` across every ref of the MetaPRL arm's own working clone
(the one holding its branch mojave/vir-l2, tip 54a2abe21 at 09:44; control `y5` 63, `wfs2` 27).
**One clause is WIDENED at the pin, said here and nowhere silently:** Q1's MetaPRL population names `virl1_*`/`virl2_*` only,
because it was drafted before L3 had MetaPRL files; it is read as `virl1_*`/`virl2_*`/`virl3_*`, the same three layers it names
for Lean. Nothing else in Q1–Q8 is changed.
**The rule from the 11-06 council binds L4 too:** past ~100 tactic applications in one proof, the arm stops and systematizes, and
tactic-building time is a SEPARATE ledger line. No Q-row below predicts a tactic count; the line is reported beside C5.

## Declarations owed by each arm before its first L4 file
Each arm's L3-closed sha (Q1's base) and its own L4 declarations file, as amend-18 asked for L3.

## The predictions
- **Q1 (L1–L3 untouched).** W8 over `l1/`, `l2/`, `l3/` (Lean) and `virl1_*`/`virl2_*` (MetaPRL), from the L3-closed sha to
  the L4-closed sha: 0 definitions edited on both arms. **FALSIFIED** for an arm by ≥ 1.
- **Q2 (no new axiom or prim).** Lean: within the standard three. MetaPRL: 0 prims in `virl4_*`, framework files beside.
- **Q3 (the parallel rule is cheap where the frame rule was cheap).** Each arm proves the parallel rule from ⟶₄ with no
  side condition naming a region. C5 is reported per arm. Predicted: the Lean proof's C5 ≤ 3 × its L2 frame rule's.
  **FALSIFIED** if > 3×.
- **Q4 (the interleaving tax lands in the configuration invariants).** The C5 of N1-V + N4-V exceeds the C5 of N1-S + N4-S
  on BOTH arms. Direction is predicted, the ratio is reported.
- **Q5 (MetaPRL pays in well-formedness again).** MetaPRL's [wf] obligations in the L4 rules exceed the count at L2 for the
  same number of rules (per-rule rate, wf premises / rules). Predicted: rate₄ ≥ rate₂. Lean: no analogue (reported 0).
- **Q6 (no data race from typing).** Both arms prove: a typed configuration never has two threads with a load/store on one
  cell outside a held lock. Predicted: HOLDS on both, with no assumption beyond ⊢₄.
- **Q7 (CE both directions).** HOLDS on both arms; reported C5.
- **Q8 (exploratory) deadlock is outside partial correctness.** Each arm exhibits one deadlocking program that satisfies
  `{emp} e {_. False}`. Reported; it is stated so that no reader counts deadlock freedom as missing.

