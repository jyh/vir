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

ADDENDUM (selftest ARM53, the 42nd head, 2026-11-08). This was written AFTER R1, R2, R3 and R7 existed on the arm and BEFORE R4
existed, and AFTER vir read lines 1–20 of the arm's R4 plan (a plan, no proof), which says R4 reuses R3's path lemmas. It was
found at the R3 dry read at 10b8ddbab, by running Z5's reader on R3. No primary C5 moved.
- Z5's old reader counted every name of `virl2_step` in the closure. On R3 it read 66, and two kinds of error sat in that
  figure. It counted value encoders (`unfold_capv`, `unfold_a_unit`), which are not step rules. And no `step2_*` appears in any
  text: they are reduce rules, fired by resource through the arm's own `l3_dstep3`, so a name reading cannot see them.
- `L3M.Z5.stepInR4`, the primary, now counts step rules (`step2_*`) and the step's unfolds (l2step, l2iter, l2run, reach, effop).
  BESIDE: `allNames` (the old reading), `stepStated` (rules in the closure stated over `l2step{`, `l2iter{` or `reach{`, the one
  reading that sees a step taken by resource) and `rootStep` (the root's own text, the like of Lean's proof-text count).
  Z5's FALSIFIED clause is read on the primary and `stepStated` together, by hand, with the named rules printed.

| id | prediction (amend-18) | MetaPRL | state |
|---|---|---|---|
| Z1 | no virl1_/virl2_ definition edited, L2-closed → L3-closed | OWED (DRY at 5e5048dad: defs 0 · rules 0 · files 0) | — |
| Z2 | MetaPRL C2 beside Lean's 0, no direction | OWED (Q until the arm names its replay files) | — |
| Z3 | R2 cites no triple | OWED (DRY at d0a445140: 0 by statement; 10 by module, BESIDE) | — |
| Z4 | R3 the largest L3 proof by C5 | OWED (DRY at 10b8ddbab: R3 304,503 against the largest other row so far, R1 9,911; R4–R6 and R8 not yet landed) | — |
| Z5 | R4 names no virl2_step rule | OWED | — |
| Z6 | R5: triple_frame once, no locality lemma | OWED | — |
| Z7 | no `fix` in a term; R6 C5 reported | OWED (DRY: fix 0 in virl3_prog) | — |
| Z8 | R7, R8 ≤ 15 proof lines | OWED (DRY: R7 1 step, 1,447 tok); R8's cell is scored INFORMED (see BLINDNESS below) | — |
| Z9 | L3 proof C5 > own virp router C5 | OWED (DRY total 13,474 at d0a445140; reference Q) | — |

Rows R1–R8 with their roots: R1 = r1_F, r1_U · R2 = r2 (virl3_eq; DRY C5 8,591, intro 9,133) · R7 = r7_F7 (virl3_typ, <--> form, E4 declared beside) · the others OWED.

## BLINDNESS (the arm's own declaration, 2026-11-08 ~01:09–01:10 PST; written before any of R3–R6 or R8 is scored)

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
  arm's commit 5e5048dad (2026-11-07 17:30 -0800, before the read). A difference moves R7 to INFORMED. Read at scoring by
  `VIR_L3M_FROZEN='R7=5e5048dad'` (`L3M.R7.frozenSame`, selftest ARM52).
- **R3: not affected**, on the condition that the proof exported is the one the arm posted as proved in session at 01:07:52,
  before the read. The evidence is that post's bus timestamp and the hashes the arm posted at 01:14:49 (sha256/16:
  `all-r3.mp` ce68b8ad1295468c · `r3.mp` 9e874374143c3f7a · `virl3_eq.ml` 9980407f1fdd38be; latest mtime among the 25 files
  listed, 01:07:06). The arm re-hashes at its export commit and posts any difference. These are the arm's own readings, not an
  independent record, and the row carries that limit beside its figure. `virl3_eq.ml` can be checked against the export.
- **R4, R5, R6: BLIND.** The arm reports that their Lean files were not opened.

### The two byte checks, DRY at mojave 10b8ddbab (2026-11-08, the 42nd vir head; re-run at L3 CLOSED)

- **R7:** `L3M.R7.frozenSame` 1 and `frozenClosureEdited` 0 against 5e5048dad. The condition holds at this sha.
- **R3:** the committed `theories/vir/virl3_eq.ml` at 10b8ddbab hashes to the posted 9980407f1fdd38be. vir also re-hashed all 25
  posted inputs on disk, with the expected values parsed from the bytes of the arm's post: 25 equal, 0 differ, 0 missing.
  24 of the 25 mtimes are as posted. `virl3_eq.ml` reads 03:42:20, not the posted 00:36:56; the arm's R3 post reports a mutant
  build followed by a byte-identical restore, which accounts for that, and the bytes are what the check reads. So R3 is read
  as **not affected**. The limit stays beside the figure: the time of the read is the arm's report (Q), and a hash shows the
  inputs did not change after the arm posted them, not when the proof was found.
- **Statement:** `r3` is stated under `store_ok{s}` and `l3_lay{s; p; f}`: region p live at 87 cells holding f(0..86), bytes
  3..66 in [0,256), sender and topic below 4. That is L3-E1's reading (OBJECT-L3 §3.3's layout), so Z4 is scored against
  the statement the erratum names.
