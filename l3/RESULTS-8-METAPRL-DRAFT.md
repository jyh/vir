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
| Z8 | R7, R8 ≤ 15 proof lines | OWED (DRY: R7 1 step, 1,447 tok); R8's cell is scored INFORMED (see BLINDNESS below) | — |
| Z9 | L3 proof C5 > own virp router C5 | OWED (DRY total 13,474 at d0a445140; reference Q) | — |

Rows R1–R8 with their roots: R1 = r1_F, r1_U · R2 = r2 (virl3_eq; DRY C5 8,591, intro 9,133) · R7 = r7_F7 (virl3_typ, <--> form, E4 declared beside) · the others OWED.

## BLINDNESS (the arm's own declaration, 2026-11-08 ~01:10 PST; written before any of R3–R6 or R8 is scored)

The MetaPRL arm declared that it opened two Lean L3 files in vir's public tree: `l3/VIRL3/R3False.lean` (lines 1–60, the two
L3-E1 witnesses and their proofs) and `l3/VIRL3/Refusals.lean` (lines 1–84, R7's proof, R8's store and R8's proof), plus a
listing of the file names under `l3/`. It looked for its own statement of R8 and opened the wrong tree. Its declarations
(`DECLARATIONS-METAPRL-ae4c349b2.md`, "What the arm had read") say it has read no file under `l3/`; from that time that is
false for those two files. The time and the extent of the read are the arm's own report (Q); nothing in the record can
check them. This is the V-F5 class, in the opposite direction: there vir leaked to the arm, here the arm read vir.

How each row is read at scoring:
- **R8 and its Z8 cell: INFORMED**, labelled in the scoreboard as W3 (ii) was. R8's store is not given by the inputs file
  (row R8 fixes only "magic correct, sender = NS"), so its cells and the proof's route are information the arm did not have.
  R8's C5 is reported, and Z9's total is reported both with it and without it.
- **Any MetaPRL statement or proof of L3-E1's two witnesses, if the arm builds one: INFORMED** (the same read covered them).
- **R7: not affected**, on the condition that `r7_F7`'s statement and stored proof at L3 CLOSED are byte-identical to the
  arm's commit 5e5048dad (2026-11-07 17:30 -0800, before the read). A difference moves R7 to INFORMED.
- **R3: not affected**, on the condition that the proof exported is the one the arm posted as proved in session at 01:07:52,
  before the read. The evidence is that post's bus timestamp and the arm's script hashes, not an independent record, and
  the row carries that limit beside its figure.
- **R4, R5, R6: BLIND.** The arm reports that their Lean files were not opened.
