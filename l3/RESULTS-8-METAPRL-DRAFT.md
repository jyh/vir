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
- Z6's `localityCited` matches `virl2_*` names containing "local", and at 10b8ddbab no such name exists, so that row cannot
  fire (selftest ARM54). `L3M.Z6.localityPop` prints the population. `L3M.Z6.unionStated` names the `virl2_*` rules in R5's
  closure stated over `st_union{`, and Z6 is read by hand against that list. Written before R5 exists on the arm.

ADDENDUM (the 44th head, 2026-11-08; STATUS 197). Written AFTER R1–R5, R7 and R8 exist on the arm and BEFORE R6, and before any
row is scored; vir has seen the DRY totals, so this fixes no figure's direction.
- Z9 compares the L3 proof C5 with the arm's "own virp program-1 router C5". amend-18's knowledge paragraph says that router "is
  complete on both arms". **On the MetaPRL arm it is not, and it was not at the pin.** The arm's virp line stops at branch
  `mojave/virp-s1`, tip 2894647f2 (2026-11-02): the 22 constructs, the two programs as deep terms, S1–S3 of the separation model
  and numerals for the semantics. It holds no proof about the router. `U_eq_F` (case-insensitive, `.ml`/`.mli` under `theories/vir`)
  reads 0 on all 265 refs of the arm's clone, with control `router_fuse` 1. RESULTS-5's MetaPRL column already read "not yet built".
- **Z9's MetaPRL cell is therefore NOT SCORABLE as written: reported so, neither HOLDS nor FALSIFIED.** vir does not choose a
  substitute reference after seeing the totals. Reported BESIDE, with no verdict: the L3 total with and without R8, and the arm's
  shallow program-1 proof (`vir.ml`, the RESULTS-1 MetaPRL column; quoted as `metaprl C5tok` 280 from
  harness/metaprl-counts-2026-11-01.tsv, whitespace tokens, 10 refines, the unit of `L3M.*.C5tok`), which is a different language
  from virp and so is not the like of Lean's 1,617. The 1,236 in RESULTS-2's Q5 is PROGRAM 2 in the LEXICAL unit (its whitespace
  figure is 688; program 1's lexical figure is 487; RESULTS-3 addendum 6), so it is not a second figure for this proof. `virp-s1` is not counted, because it carries no router proof. FINDINGS V-F6.

| id | prediction (amend-18) | MetaPRL | state |
|---|---|---|---|
| Z1 | no virl1_/virl2_ definition edited, L2-closed → L3-closed | OWED (DRY at 5e5048dad: defs 0 · rules 0 · files 0) | — |
| Z2 | MetaPRL C2 beside Lean's 0, no direction | OWED (Q until the arm names its replay files) | — |
| Z3 | R2 cites no triple | OWED (DRY at d0a445140: 0 by statement; 10 by module, BESIDE) | — |
| Z4 | R3 the largest L3 proof by C5 | OWED (DRY at 2d63bef28, every root landed: R3 304,503 against R6 172,497, R5 166,062 and R4 163,558, each of those three closures carrying R3's path lemmas through R4) | — |
| Z5 | R4 names no virl2_step rule | OWED (DRY at 8e6b250c2: primary `stepInR4` 7, `stepStated` 13, `rootStep` 0, so the root's own text names none and its closure does. `stepNames` (selftest ARM55) gives the 7 sites: `unfold_effop` in R3's five path lemmas l3_F_p1b/p2b/p3a/p3b/p5, `unfold_reach` in l3_nofault, `unfold_l2iter` in l3_stuck_iter. As DRY-read the FALSIFIED clause "no step rule in its proof tree" is met, by way of R3's path lemmas and the bridge `l3_trun_den`. The hand read at L3 CLOSED decides) | — |
| Z6 | R5: triple_frame once, no locality lemma | OWED (DRY at 8e6b250c2: `frameApps` 1, `localityCited` 0 on a population of 0, `unionStated` 1 = `triple_intro`, the triple's own introduction rule, which is not a locality lemma of an operation; as DRY-read Z6 holds) | — |
| Z7 | no `fix` in a term; R6 C5 reported | OWED (DRY at 2d63bef28: fix 0 in virl3_prog; R6 C5 172,497 over 87 rules = both posted roots; BESIDE, `r6` alone 15,257 over 41 rules, `r6_seq` alone 164,481 over 72) | — |
| Z8 | R7, R8 ≤ 15 proof lines | OWED (DRY at df4888004: R7 1 step, 1,447 tok; R8 1 step, 595 tok at the root, closure 11,046 tok over 43 rules, so the root step carries none of the run, which lives in helpers); R8's cell is scored INFORMED (see BLINDNESS below) | — |
| Z9 | L3 proof C5 > own virp router C5 | OWED (DRY total 370,060 at 2d63bef28, every virl3_* derivation; 363,318 at df4888004 before R6's 31 rules, and 358,921 at 8e6b250c2 before R8's 23; NOT SCORABLE as written, the reference does not exist on this arm: see the 44th head's ADDENDUM) | — |

Rows R1–R8 with their roots: R1 = r1_F, r1_U · R2 = r2 (virl3_eq; DRY C5 8,591, intro 9,979) · R3 = r3 (DRY C5 304,503) · R4 = r4 (virl3_tri; DRY C5 163,558, root 5,721 tok, 1 step) · R5 = r5_agree, r5_frame (DRY C5 166,062, roots 2,504 tok, 2 steps) · R7 = r7_F7 (virl3_typ, <--> form, E4 declared beside) · R8 = r8 (virl3_tri; DRY C5 11,046, INFORMED) · R6 = r6, r6_seq (virl3_run; DRY C5 172,497, roots 551 tok, 2 steps; the arm reports BLIND, Q).

Byte checks at 8e6b250c2 (10b8ddbab an ancestor): `virl3_eq.ml`, `virl3_eq.prla` and `virl3_typ.ml` unchanged from 10b8ddbab, and `virl3_eq.ml` still hashes to the posted 9980407f1fdd38be; R7 frozenSame 1, closureEdited 0; Z1 0/0/0. The arm's "blind" for R4–R6 is its own report (Q).

Dry read of R8 at df4888004 (STATUS 200; 8e6b250c2 an ancestor; only `virl3_tri.ml` and `.prla` differ; `virl3_tri.ml` = the posted d6ae0d67c18e42c2). R7 frozenSame 1, closureEdited 0; Z1 0/0/0; 133 rules, `virl3_tri` 56 as posted; R3 still the largest (304,503). Every row of the 8e6b250c2 reading is byte-identical except `C5tokIntro` (+516 on each, the four new intro rules the layer-wide upper bound admits) and the totals. The store, by hand against inputs/L3-programs.md: alloc 87 = K+NS; cell 0 = 24 (LEN); cells 3..6 = 49,71,83,77, the little-endian bytes of 1297303345; cell 7 = 4 = NS (sender), topic 0. The ACL load is at 67+16 = 83, in range; the bucket load is at 83+4 = 87, one past the region. `r8` concludes "not triple" over the no-fault `triple`, not `triple_i`, as OBJECT-L3 reads R8.
**A limit for the R8 row at scoring:** the arm's statements give typing (R1) and a fault (`r8_stuck`: `is_fault{c}`, any fault) and the refuted triple. The row's words "INDEX-FAULTS at the bucket load" are stated by no MetaPRL rule; they are this hand arithmetic plus the arm's mutant report (Q). `is_ifault` exists in `virl2_triple` and is not cited. Lean's `F8_stuck` pins the stuck term (a load at 83 + 4), so the two R8 cells do not carry the same statement, and the scoreboard says so beside them.

Dry read of R6 at 2d63bef28 (STATUS 201; df4888004 an ancestor; the diff is `virl3_run.ml/.mli/.prla` new, `MetaprlInfo` +1 line, and `virl3_tri.mli` +4 declares of operators `virl3_tri.ml` already defines; `virl3_tri.ml` and `.prla` unchanged; `virl3_run.ml` = the posted 0666f598471b174d, `virl3_tri.mli` = the posted 52ce689bd13737d7). R7 frozenSame 1, closureEdited 0; Z1 0/0/0; 164 rules (133 + the 31 posted); `L3M.rows.rooted` 8, every row. Against df4888004 every R1–R5, R7, R8 C5 is byte-identical; `C5tokIntro` moves +167 on each row (the layer-wide upper bound admits R6's intro rules).
By hand against OBJECT-L3 §3 item 5, DECLARATIONS E4 and inputs/L3-programs.md: `l3_wr` writes cells 0 and 3..66, so the ACL (67..82) and buckets (83..86) are untouched, as E4 reads. `l3_emc`'s four conditions are `l3_fpost`'s case tree in order, and F's guards: 24 ≤ LEN, the magic, the ACL cell = 1, 0 < bucket. `r6_cons` is a conservation law (count + final bucket = initial bucket), so the count cannot be vacuous: an always-false `l3_em` could not prove it against `l3_fpost`'s decrement.
**A limit for the R6 row at scoring:** the row is carried by TWO roots that share a definition, not by one theorem. `r6_seq` gives the n instances of R4 at the worlds of the fold (`l3_calls`, under `l3_wsok`); `r6` gives the bound over the same fold with no wire hypothesis and does not cite R4. What joins them is that `l3_calls` and `l3_cnt` unfold over the same `l3_wr`/`l3_fpost` fold, and a reader has to read both definitions to see it. The primary C5 is the union (172,497, as the two roots were posted); 164,481 of it is `r6_seq`, nearly all R4's closure, and the counting argument alone is 15,257. Report the split beside the cell, or R6 reads as a proof ~11× the size of its own argument. The arm's `virl3_tri.mli` edit touches a shared interface, so the row waits on the L3 CLOSED whole-chain replay (a byte diff cannot see name capture: RESULTS-11 Addendum 1).

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
