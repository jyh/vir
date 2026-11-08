# RESULTS-8 — layer L3, the router as an L2 program (O95; OBJECT-L3 at vir 18df3a4; amend-18; erratum L3-E1)

**Both columns.** The Lean column was UNSEALED 2026-11-05 on the MetaPRL arm's L3 declarations (the Captain's pace ruling (C), 11-05);
the MetaPRL column was scored 2026-11-08 (its own section below). Every Lean figure is a row of `l3/out/counts-l3.tsv`
(`harness/count.py --arm l3 l3`) or `l3/out/counts-z1.tsv` (`--arm w8 --base dc95b53`), or is labelled as something else. Lean
L2-closed sha: dc95b53.

## The declarations (amend-18), both written before the arm's first L3 file, neither arm reading the other's
| arm | file | commit (time) | sha256/16 |
|---|---|---|---|
| Lean | `l3/DECLARATIONS-LEAN.md` | vir 9de7857 (2026-11-03), SEALED until the MetaPRL post | bf6646d9fec4a931 |
| MetaPRL | `theories/vir/DECLARATIONS-L3-METAPRL.md` in mojave's metaprl clone, copied byte for byte to `l3/DECLARATIONS-METAPRL-ae4c349b2.md` | ae4c349b2 (2026-11-05 16:13 PST) on mojave/vir-l2, parent 265c1b8e1, 0 `virl3_` files at it | ae80ac5b7c42aef0 |

Both hashes were re-read at the unseal (the Lean file at 9de7857 and at the branch tip, the MetaPRL file at ae4c349b2). The
MetaPRL arm's post of its declarations said it had not read anything under `l3/`, any Lean L3 file or branch, or the Lean
declarations; it had read ERRATA-L3 at fcaae75, whose L3-E1 names the Lean arm's R3False file and two lemma names (declared by
that arm). The Lean branch was not pushed until after that post. The MetaPRL declarations defer one item: the L2-closed sha, to
be posted with counts before its first `virl3_` file.

## The rows (inputs/L3-programs.md R1–R8), Lean
| row | theorem(s) | file |
|---|---|---|
| R1 | `F_typed` · `U_typed` · `U_tx_typed` — `(w:cap) ; {w} ⊢₂ · : cap` | VIRL3/Typing.lean |
| R2 | `R2` — ⟦U⟧₂ ≠ ⟦F⟧₂, one witness world (U's bucket 0, F's 1) | VIRL3/Inequality.lean |
| R3 | `R3` — ⟦U_tx⟧₂ = ⟦F⟧₂ on every store whose world has sender and topic in [0, 4) (L3-E1's reading; the theorem assumes LESS than `layout`) | VIRL3/Rollback.lean, VIRL3/Sym.lean |
| R4 | `R4` — {RegionAt p 87 f} F {v. v = ⟨p⟩ ∧ RegionAt p 87 (postF f p)}, layout's pure part as hypotheses | VIRL3/RouterTriple.lean |
| R5 | `R5_contents` (postF agrees with f off the bucket and out cells) · `R5_frame` (beside any R, by `frame`) | VIRL3/RouterTriple.lean |
| R6 | `R6` — over any list of in-range frames, sender s's emits ≤ its initial tokens; `R6_call` (each call is R4) | VIRL3/Trace.lean |
| R7 | `R7` — the variant ending `ret 1` has no type | VIRL3/Refusals.lean |
| R8 | `R8` — sender = NS index-faults at the bucket load; no triple whose precondition admits that world (proved WF, not assumed) | VIRL3/Refusals.lean |
| L3-E1 | `R3_false_order` · `R3_false_alias` — R3 as pinned is false | VIRL3/R3False.lean |

All 10 row theorems present (`L3.rows.present` 10). `audit-001`: 14 theorems, each within propext · Classical.choice ·
Quot.sound (R7: propext only); control `control_sorry` prints sorryAx (`L3.control` 1). The transcription check
(`harness/transcribe_l3.py`, selftest ARM37): F, U, U_tx built from the inputs file's TEXT equal the Lean terms, SAME ×3.

## The predictions (amend-18 Z1–Z9), Lean
| | prediction | Lean | verdict |
|---|---|---|---|
| Z1 | no L2 (or L1) definition edited, dc95b53 → L3 tip | **0** L2 · **0** L1 (`counts-z1.tsv`; positive control 2fccab7 → 8c3320f reads 17) | HOLDS |
| Z2 | transport casts on the L3 files = 0 | **0** (`L3.Z2.casts`, CAST_RE) | HOLDS |
| Z3 | R2 by evaluation, citing no triple | **0** `Triple` in Inequality.lean; R2 cites `run₂_steps` · `den₂_of_steps` · `soundness₂_steps` only | HOLDS |
| Z4 | R3 is the largest L3 proof by C5 | R3 (Rollback+Sym) **851** tokens; R4+R5 (RouterTriple) **1,170** (`L3.Z4.*`) | **FALSIFIED** |
| Z5 | R4 from the rules, no ⟶₂ in its proof | **0** step tokens in R4's proof (`L3.Z5.stepInR4`) | HOLDS |
| Z6 | R5's caller half is one `frame`, no locality lemma | `frame` **1**, locality lemmas **0** (`L3.Z6.*`) | HOLDS |
| Z7 | R6 in the logic; no `fix` in a term | `fix` in the terms **0**; R6 is a structural induction over `List` | HOLDS; R6 C5 **696** reported (`L3.C5.Trace`) |
| Z8 | R7, R8 each ≤ 15 proof lines | R7 **8** · R8 **17** (`L3.Z8.*`; R8's world-is-WF lemmas, 21 lines with their statements, BESIDE) | R7 HOLDS · **R8 FALSIFIED** |
| Z9 | L3 proof C5 > virp program-1 router C5 | **3,874** (the R1–R8 files) against **1,617** (virp Router · Exits · Sep · Trace) | HOLDS (scope beside: virp WITH its language files is 7,055) |

## What the Lean arm found, for the paper
- **L3-E1 was found by writing R3's proof, not by running it**: the ANF order of F's loads (before its guard) and the overlap of
  the ACL rows with the buckets for topics ≥ NT are invisible in virp's U = F, where loads are total and drops abort.
- **L2 has no `if` rule and no pure-`let` rule.** R4 derives both from `pure_step_rule` with L1's `determinism`
  (`ite_true_rule`, `ite_false_rule`, `letRet_rule`); that is where `L3.Z5.stepInFile` (2) comes from, BESIDE R4's own 0.
- **Two methods, one arm:** R3 is an equality of meanings and is proved by SYMBOLIC RUNS (`simp` through `run₂`, the world's
  lookups as rewrite rules, five branches); R4 is a triple and is proved by the RULES. The rules proof is the larger (Z4).

## Limits
- C5 rows are whitespace tokens per FILE, comments stripped; R3's figure includes the symbolic-run kit in Sym.lean, R4's
  includes R5 and the frame-field definitions. A per-theorem split could order Z4 differently; it is not what Z4's extractor
  reads, and the extractor was fixed (ARM38) before these figures were taken.
- `L3.Z5.stepInFile` counts the capitalised forms only; the helper's `step₂_ret_none` (lowercase) is a fourth token beside it.
- R4 and R6 carry layout's pure part as Lean hypotheses (sender, topic in range), not as `⌜·⌝` inside the assertion.
- R6 bounds emits by the INITIAL tokens with the initial bucket non-negative; frames are written by the caller between calls
  (cells [p, p + 67)), and the bound is about R4's post-states, each call justified by `R6_call`.

## The MetaPRL column, scored 2026-11-08 by the 46th vir head

Every MetaPRL figure below is a row of `l3/out/counts-l3m.tsv`, or is labelled as something else:
`VIR_L3M_FROZEN='R7=5e5048dad' VIR_L3M_ROOTS='R1=r1_F,r1_U;R2=r2_F_den,r2_U_den,r2;R3=r3;R4=r4;R5=r5_agree,r5_frame;R6=r6,r6_seq;R7=r7_F7;R8=r8_stuck,r8'
harness/count.py --arm metaprll3 --base c80941362 --ext 2d63bef28 <clone of the arm's tree>`. c80941362 is the arm's L2-closed sha (its repair
of the D-S10 name capture, RESULTS-11 Addendum 1); 2d63bef28 is the sha the arm named when it posted L3 CLOSED. The command was re-run
at scoring and reproduced byte for byte. The roots are the ones in the arm's closing post. The dry reads used `R2=r2` and `R8=r8`; with those,
the only rows that move are the root-only rows of R2 and R8 and `Z8.R8Steps`, and every closure is the same. The frame this was scored against, written
before the rows it governs, is `l3/RESULTS-8-METAPRL-FRAME.md` (its addenda, the BLINDNESS section and the byte checks).

**L3 CLOSED, as the arm reports it (Q).** Whole-chain `check_all` over `virl3_*` in one session: typ 23, eq 54, tri 56, run 31, so 164 of 164
GROUNDED, 0 INCOMPLETE, 0 PRIM, no BASE-ERR. The file is `l3/check-l3closed.out` in the arm's tools tree (not committed when this was read; sha256/16
03afd8aae2fe391b). `L3M.rules` 164 agrees (H = Q), and every row R1–R8 has its posted roots stored (`L3M.rows.rooted` 8). What this does and does not establish
is the first limit below.

**Byte checks at 2d63bef28:** R7 `frozenSame` 1 and `frozenClosureEdited` 0 against 5e5048dad, so R7 is not affected by the arm's declared read. `virl3_eq.ml` hashes to
the posted 9980407f1fdd38be, `virl3_tri.ml` to d6ae0d67c18e42c2, `virl3_run.ml` to 0666f598471b174d, `virl3_tri.mli` to 52ce689bd13737d7. So R3 is read as not affected, with
the frame's limit. Labels: **R8 and its Z8 cell INFORMED** (FINDINGS M-F12); R4, R5, R6 BLIND by the arm's report (Q). No L3-E1 witness exists on this arm.

| | prediction (amend-18) | MetaPRL | verdict | Lean, from above |
|---|---|---|---|---|
| Z1 | no L1/L2 definition edited | defs **0** · rules **0** · files **0**, c80941362 → 2d63bef28 (`L3M.Z1.*`) | HOLDS | HOLDS |
| Z2 | MetaPRL C2 beside Lean's 0, no direction | **not reported**: the arm named no replay files for it. The `0` in `L3M.Z2.C2` is a placeholder marked Q, not a measurement | no verdict is owed | HOLDS (0 casts) |
| Z3 | R2 by evaluation, citing no triple | **0** rules stated over a triple in R2's closure (`L3M.Z3.tripleCites`); module reading 10, BESIDE, the wf and iteration lemmas that sit in those modules | HOLDS | HOLDS |
| Z4 | R3 the largest L3 proof by C5 | R3 **304,503** against the next, R6 **172,497** (`L3M.Z4.*`) | HOLDS, on the closure | **FALSIFIED** |
| Z5 | R4 names no step rule in its proof tree | **7** step-rule sites in R4's closure (`L3M.Z5.stepInR4`), 13 rules stated over the step (`stepStated`), 0 in the root's own text (`rootStep`) | **FALSIFIED** (hand read below) | HOLDS |
| Z6 | R5: one frame, no locality lemma | `triple_frame` **1**; the name row is empty on a population of 0, so by hand: `r5_frame` is `triple_frame` then `r4`, and `unionStated`'s one rule is `triple_intro`, the triple's own introduction | HOLDS | HOLDS |
| Z7 | no `fix` in a term; R6 C5 reported | `fix` **0** in `virl3_prog`; R6 C5 **172,497** (split below) | HOLDS | HOLDS, 696 |
| Z8 | R7, R8 ≤ 15 proof lines | R7 **1** · R8 **2** refine steps at the root (this arm's unit, not Lean's lines) | R7 HOLDS · R8 HOLDS (**INFORMED**) | R7 HOLDS · R8 **FALSIFIED** |
| Z9 | L3 proof C5 > own virp router C5 | L3 total **370,060**; the reference does not exist on this arm | **NOT SCORABLE as written** (FINDINGS V-F6) | HOLDS |

Tallies across the rows with a verdict on MetaPRL: Z1, Z3, Z4, Z6, Z7, Z8 HOLD, with R8 INFORMED; Z5 FALSIFIED; Z2 no verdict; Z9 not scorable. The Lean arm's
FALSIFIED rows are Z4 and R8's cell of Z8. **The arms disagree on Z4, Z5 and Z8's R8 cell.** Z5 is a difference of route: each arm took a different one (below). Z4 and Z8 are also read in different units, so those two are not like-for-like results: Lean's C5 is per file and MetaPRL's is
an in-layer closure of stored derivations; Lean's Z8 counts source lines and MetaPRL's counts refine steps. No ratio between the columns is claimed.

### What the arm's R4 is (Z5's hand read)
The prediction was that the router triple would be proved by sequencing OBJECT-L2 §5's rules. On this arm it is not. `r4` opens with `triple_intro`, the triple's own semantic introduction, and reaches
the terminal configurations through `l3_trun_den` and the arm's symbolic runs of the program. The arm said this would be the route before it proved R4 (its R3 post: "semantic: den2_adequate + reach_det, then triple_intro").
Of the eleven program rules of `virl2_rules` (`triple_let`, `triple_conseq`, `triple_step`, `triple_gstep`, `triple_if_t`, `triple_if_f`, `triple_app`, `triple_load`, `triple_store`, `triple_free`, `triple_alloc`), **no
stored derivation in any `virl3_*` module names one (0 of 164; control `l3_trun_den` fires in `r4`)**. That reading is by name over the stored text and it is complete for these eleven: none of them carries a resource annotation in `virl2_rules.ml` (the file's five annotations are on other rules), so a use would have to name it. The three triple rules the layer does name are `triple_intro` (`r4`),
`triple_frame` (`r5_frame`) and `triple_elim` (`r8`). `L3M.Z5.stepNames` gives the seven step sites, all in helpers `r4` reaches: `unfold_effop` in R3's five path lemmas `l3_F_p1b`, `l3_F_p2b`, `l3_F_p3a`, `l3_F_p3b`, `l3_F_p5`, `unfold_reach` in `l3_nofault`,
`unfold_l2iter` in `l3_stuck_iter`. So Z5 is FALSIFIED by the proof's route, not by a stray use. What Z5 tests is whether a triple on this L2 gets built through the rules, and at this layer on this arm it did not.

### Where the tokens are
`virl3_eq`, the module that holds R3 and its path lemmas, is **329,628** of the layer's 370,060 stored tokens, and R3's own closure is 304,503. R3's ten path lemmas were driven by the arm's symbolic stepper `l3_dstep3`, and the arm's session script for R3 (`all-r3.mp`, in its tools tree) is 2.9 MB,
so these figures size what is stored, not what was authored. R4's, R5's and R6's closures overlap R3's through the shared path lemmas, so the Z4 comparison is between overlapping sets. **By the root's own text Z4 reverses**: R4 5,721 tokens, R1 2,894, R5 2,504,
R7 1,447, R8 1,246, R3 783, R2 634, R6 551. The primary was fixed before R3 existed on this arm and it is the closure; the root reading is reported beside it and it is not scored.

R6 is two roots joined by a shared definition (`l3_wr`/`l3_fpost` fold): `r6_seq` (n instances of R4) closes at **164,481** tokens over 72 rules and `r6` (the bound, which does not cite R4) at **15,257** over 41 (`l3/out/counts-l3m-r6-split.tsv`).
The union is 172,497 over 87 rules. Read the bound's own cost as 15,257; R6's cell reads about 11× that because it carries R4's closure.

### Limits (MetaPRL column)
- **"GROUNDED" here is `check_all`, quoted from the arm (Q), and RESULTS-6 records that `check_all` does not replay a stored proof against changed definitions; the replay is `status_all`.** The arm's replays, also Q: `virl3_tri` 56/56 and `virl3_run` 31/31 FRESH at 2d63bef28 itself, each in its own session (asked for at scoring, because `virl3_tri.mli` gained four `declare`s after that module's earlier replay; log `l3/fresh-2d63.log` in the arm's tools tree, sha256/16 60bf6865f43e6aca); `virl3_typ` 23/23 at 5e5048dad and `virl3_eq` 54/54 at 10b8ddbab, and `virl3_typ*`, `virl3_eq*` and `virl3_prog*` have no byte difference from those commits to 2d63bef28 (`git diff`, measured). No single session replayed all four modules at 2d63bef28.
- **Of amend-18's C1–C6, this column reports C5 (per module, `L3M.C5tok.*`) and C4's prims (`L3M.prims` 0), as RESULTS-7's MetaPRL column did.** C1, C2, C3 and C6 are not reported on this arm at L3: no extractor was built for them and the arm named no replay files for C2.
- **C5 is an upper bound on each row:** a `reduce` use admits every `virl3_*` reduce rule whether fired or not, and other resources are not modelled (`L3M.*.C5tokIntro` beside).
- **Z8's unit is the refine step of the root's own stored derivation.** R8's root is 2 steps and 1,246 tokens; its closure is 11,046 tokens over 43 rules, because the run lives in helpers. A step is not a Lean line.
- **R8 is INFORMED and the two arms' statements differ.** `r8_stuck` states `is_fault` (any fault), and "index-faults at the bucket load" is hand arithmetic plus the arm's mutant report (Q). Lean's `F8_stuck` pins the stuck term.
- **The arm's blindness for R4–R6 and the time of its declared read are its own report (Q).** A hash shows inputs unchanged after the arm posted them, not when a proof was found.
- **2d63bef28 is on the arm's local branch** (push disabled), so a reader without that tree cannot re-run the table above until the arm publishes it.
- **The `R6` row carries two theorems, not one** (split above); a reader has to read `l3_calls` and `l3_cnt` to see they share the fold.
