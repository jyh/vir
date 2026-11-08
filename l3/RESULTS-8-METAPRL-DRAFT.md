# RESULTS-8, MetaPRL column — FRAME (DRAFT, not scored)

Written 2026-11-07 by the 39th vir head. At that point the MetaPRL arm had landed R1 and R7 only, at mojave 5e5048dad
(local mojave/vir-l3, cut from its L2-closed sha c80941362). Every figure below is OWED. The one exception is the dry read,
marked DRY, which is not a score. The column is scored when the arm posts L3 CLOSED with its root names. It is scored by
`count.py --arm metaprll3` (vir 9ac1e28, selftest ARM50), whose units were declared before R2–R6 and R8 existed on this arm:
- A row's C5 is the tokens of its in-layer closure. Resource use of `reduce` admits every virl3_* reduce rule, so this is
  an upper bound.
- Z8's proof lines are refine steps of the root's own derivation, with tokens beside. This unit is NOT Lean's source lines,
  and the scoreboard says so wherever the two are compared.

ADDENDUM (vir 546536e, selftest ARM51, the 40th head, 2026-11-07). This was written AFTER R1, R2 and R7 existed on the arm
and BEFORE R3–R6 and R8. It was found at the R2 dry read at d0a445140, and no primary C5 moved.
- Z3 reads "cites a triple" from the cited rule's STATEMENT (it mentions `triple{` or `triple_i{`). The earlier reading, any
  rule of virl2_triple/virl2_rules, is reported BESIDE as `L3M.Z3.moduleCites`. That earlier reading counted iteration and
  wf lemmas and read R2 at 10, which would have been a false FALSIFIED.
- `L3M.<row>.C5tokIntro` is reported BESIDE as an upper bound: the closure plus every virl3_* `{| intro |}` rule when a closure
  text invokes autoT/dT. Those rules are applied by resource and named by no text.

| id | prediction (amend-18) | MetaPRL | state |
|---|---|---|---|
| Z1 | no virl1_/virl2_ definition edited, L2-closed → L3-closed | OWED (DRY at 5e5048dad: defs 0 · rules 0 · files 0) | — |
| Z2 | MetaPRL C2 beside Lean's 0, no direction | OWED (Q until the arm names its replay files) | — |
| Z3 | R2 cites no triple | OWED (DRY at d0a445140: 0 by statement; 10 by module, BESIDE) | — |
| Z4 | R3 the largest L3 proof by C5 | OWED | — |
| Z5 | R4 names no virl2_step rule | OWED | — |
| Z6 | R5: triple_frame once, no locality lemma | OWED | — |
| Z7 | no `fix` in a term; R6 C5 reported | OWED (DRY: fix 0 in virl3_prog) | — |
| Z8 | R7, R8 ≤ 15 proof lines | OWED (DRY: R7 1 step, 1,447 tok) | — |
| Z9 | L3 proof C5 > own virp router C5 | OWED (DRY total 13,474 at d0a445140; reference Q) | — |

Rows R1–R8 with their roots: R1 = r1_F, r1_U · R2 = r2 (virl3_eq; DRY C5 8,591, intro 9,133) · R7 = r7_F7 (virl3_typ, <--> form, E4 declared beside) · the others OWED.
