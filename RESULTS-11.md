# RESULTS-11: the SLang scoreboard, amend-20 SL1–SL8 and amend-22 D1–D4, MetaPRL arm

**This frame was written 2026-11-07 by the 33rd vir head, after the MetaPRL arm's SLang act 1 (mojave/slang 41de5e05d:
`vir_slang`, definitions and well-formedness only) and BEFORE any L1-stage file (`vir_l1slang`), the generic induction rule, or
the L1 rule exist.** Every L1 figure below is OWED. The frame fixes how each row is read, so that the reading cannot be shaped by
the L1 figures. One reading rule (SL3 on bound names, below) was written AFTER act 1's read, which is what raised it. That is
declared, and it is the only rule here written after any SLang figure existed.

**FILLED 2026-11-07 by the 37th vir head at f1c3d89e9**, the sha the arm named for SL6's landing. The rules below were all fixed
before that sha; the final column is read under them unchanged. Every scored row HOLDS at f1c3d89e9 **except SL1, which
Addendum 1 re-scores FALSIFIED** at the arm's repair sha c80941362 (the f1c3d89e9 sha carries an L2 regression the SL1 instrument
could not see). Every other row is unchanged there.

The Lean arm takes no act (amend-20). Its comparator is amend-19 I3's 509 tokens (RESULTS-9).

## The run
`VIR_SLANG_ROOT=<the arm's L1 rule> count.py --arm slangm --base 73bd3ac0d --ext <the arm's named sha> <clone>`, with count.py
from vir ccc4fdd or later (ARM46 + ARM47), and NO VIR_SLANG_FW/L1, so the stages are read MEASURED. If the measured stages are
not exactly {vir_slang} / {vir_l1slang}, that is a finding, posted before scoring. Every figure is read at a sha the arm named on
the bus. A figure from any other sha is void.

## Rows

| row | falsifier (amend-20 / amend-22, quoted in short) | harness row(s) | reading at 41de5e05d (act 1, framework only) | FINAL, at f1c3d89e9 (SL6 landed; the arm's named sha) |
|---|---|---|---|---|
| SL1 | ≥ 1 pre-existing definition, rule or `.prla` changes | SLM.SL1.rulesEdited / defsEdited / prlaChanged; otherChanged BESIDE | 0 / 0 / 0; MetaprlInfo (one line, module list) BESIDE | 0 / 0 / 0 ⇒ ~~HOLDS~~ **SUPERSEDED by Addendum 1: FALSIFIED** (33 / 6 / 4 at c80941362); otherChanged 2 BESIDE: MetaprlInfo + virl1_induct.mli (D-S10; its .ml/.prla were byte-unchanged vs 73bd3ac0d, but it broke L2 replays by name capture) |
| SL2 | a prim is added; grounded under REPLAY | SLM.SL2.newPrims; SL2.grounded is Q (the arm's status_all) | 0 new prims; the arm posted 24/24 FRESH, 24 GROUNDED | 0 new prims ⇒ **HOLDS**; status_all FRESH per stage from the arm's commits: fw 47/47 (f131274f9; vir_slang byte-unchanged since), l1 28/28 (1272ee7fb; unchanged since), sl6 34/34 (f1c3d89e9, check_all 34 grounded) |
| SL3 | the framework module(s) name an L1 operator or a `virl1_`/`virl2_` term | SLM.SL3.hits (scored); SLM.SL3.binderOnly BESIDE; hand read | hits 1 = `kids`, a bound name only (binderOnly 1); by hand: no L1 term applied, no nat sort literal ⇒ HOLDS at this sha | hits 1 = `kids`, binderOnly 1; vir_slang byte-unchanged since f131274f9, whose by-hand read (no L1 term, no nat sort literal) carries ⇒ **HOLDS** |
| SL4 | the L1 rule's derivation goes through a recogniser (`wfs`, `is_tyterm`, `isNum`) | SLM.SL4.recogHits over the closure from ROOT; SL4.control beside | Q (no root yet); control 3 | ROOT l1s_induction: recogHits **0**, control 3 (isNum, is_tyterm, wfs), closure 23 rules, rootStatement 0 ⇒ **HOLDS**; closure and vir_l1slang unchanged since 1272ee7fb, and vir_l1sl6 is downstream of it (extends Vir_l1slang), so no SL6 rule can enter it |
| SL5(a) | L1 stage C5 > 25,332 tok | SLM.SL5.L1.C5tok | 0 (no L1 stage) | **5,728** ≤ 25,332 ⇒ **HOLDS** (11.25× Lean's 509) |
| SL5(b) | framework + L1 C5 > 69,794 tok | SLM.SL5.total.C5tok | framework 649 so far | fw 1,895 + L1 5,728 = **7,623** ≤ 69,794 ⇒ **HOLDS** (14.97×) |
| SL6 | a direction (type · atom · expression × both) not proved | Q: the arm's six rule names, each read in its `.prla` | not reached | **6/6 proved** (stored derivations; mojave's two false-statement mutants red backwards, 32/34). VIR_SLANG_SL6 in slot order: sl6_type_fwd · sl6_type_bwd · sl6_atom_fwd · sl6_atom_bwd · sl6_expr_fwd · sl6_expr_bwd. Hand read (vir_l1sl6.ml ll.84–94, 216–229): (0, is_tyterm) · (2, wfs{0}) · (3, wfs{2}), matching the sort map (vir_l1slang.ml l.5) and wfs's codes (virl1_induct.ml l.54: 0 atom, 2 expression); ⇒ is `t ∈ L1SLang{k} ⊢ t ∈ L1Lang{sig1} ∧ R t = btrue`, ⇐ its converse ⇒ **HOLDS** |
| SL7 | reported only | Q | not stated | not stated (no set-type layer) — nothing to report |
| SL8 | reported | SLM.SL8.{fw,l1,sl6}.{rules,steps} | fw 24 rules / 24 steps | fw 47/47 · l1 28/28 · sl6 34 rules / 73 steps, sl6 C5 107,361 tok (reported, never in SL5) · unstaged 3 · extras 24,516 BESIDE (stale subtrees, not the proof) |
| D1 | = SL5(a) | SL5.L1.C5tok | — | 5,728 ≤ 25,332 ⇒ **HOLDS** |
| D2 | L1 stage ≤ 5,090 tok | SL5.L1.C5tok | — | 5,728 > 5,090 ⇒ **HOLDS** (margin 638 tok, 12.5 %) |
| D3 | attribution follows SL4 × D1 | — | — | SL4 and D1 both HOLD ⇒ the saving is attributed to the removed recognisers |
| D4 | the tactic line, BESIDE, never in C5 | Q: the arm's ledger line (l2/slang/TACTIC-LEDGER.md) | tooling T1 (vir_walk) is UNSTAGED: 3 rules, out of every stage | the arm's line: all SL6 tactic building generated (l2/sl6/gen_r.py, gen_e.py, lib.py, gen_b.py, gen_n.py); drive sl6.mp 1,066,418 bytes, generated; stage wall time ≤ 52 min (14:08–15:00 PST, not split script/tool). BESIDE, no direction, never in C5 |

## The joint reading (amend-22 §4), scored at f1c3d89e9
D1 and D2 both HOLD: 5,090 < 5,728 ≤ 25,332. That is the stated prediction: **both causes are real, and the encoding is the larger.**
SL4 holds, so D3 attributes the saving to the removed recognisers. D2's margin is small (638 tokens over the floor), and SL5 counts
stored proofs only: the arm's proof search lives in generated ML tactics, on D4's line. SL6's own C5 (107,361) is ~19× the L1 rule's
and is a check on the stage, priced apart from it by the SL6 reading rule below; it is reported and enters no bound.
The run: `VIR_SLANG_ROOT=l1s_induction VIR_SLANG_SL6=<the six names> count.py --arm slangm --base 73bd3ac0d --ext f1c3d89e9 <clone>`,
count.py from vir 803a9ef; stages MEASURED exactly {vir_slang} / {vir_l1slang} / {vir_l1sl6}.

## Reading rules fixed here
- **SL3 on bound names (written after act 1, declared).** amend-20's SL3 says the module *names* no L1 operator or `virl1_`/`virl2_`
  term. A name in binder position (`x. body`, `{x: T | …}`, `x: T * …`, a comma list ending in one) is a variable, not that term.
  So a hit that `SLM.SL3.binderOnly` lists is checked BY HAND. If every occurrence is bound and no term of that spelling is applied,
  it does not falsify SL3. `SLM.SL3.hits` itself is never reduced, and is quoted beside the verdict with the hand read's line
  cites. A hit with ANY term-position occurrence falsifies SL3 as written.
- **SL3's second method.** D-S2 makes sorts numerals, and a hard-coded L1 sort number would be invisible to a name reader. So the
  framework text is read by hand for nat literals in sort position at every scored sha, with line cites.
- **SL5 counts stored proofs only.** ML tactic code is D4's line. The tooling's 3 unstaged rules stay out by stage.
- **Departures D-S1..D-S4 ride BESIDE**, each quoted with the amend-20 sentence it departs from. None changes a falsifier.
- **SL4's absence** is quoted with the control (3 recognisers derived from l1_induction) beside it.
- **SL6's own stage (written 2026-11-07 after the L1 stage landed at 1272ee7fb and BEFORE any SL6 rule, declared).** The arm put
  SL6 in a new module (vir_l1sl6) so vir_l1slang stays byte-identical. SL5(a) prices "the per-form rule and everything L1-specific
  under it", and SL6 checks that stage from outside it. So a NEW module that is neither fw nor l1 and holds a `VIR_SLANG_SL6`
  statement is stage `sl6`: its rules count for SL6's slots and get their own SL8 line (`SLM.SL8.sl6.*`), and they never enter
  SL5(a) or (b) (ARM49).

## Departures (the arm's, declared before the proofs they touch)
D-S1 explicit variable sort `SLang{ssig; vs; s}` · D-S2 sorts are nat · D-S3 children as a sort-indexed tuple (SKids, kidl) ·
D-S4 a node carries its signature ENTRY, not an index (Img's map must be closed, itt_image img_type), so the L1 rule splits on
membership in ssig1.

## Limits
SL3's reader matches names and cannot tell a binder from a term, so `binderOnly` and the hand read carry that distinction.
SL5 is C5 over stored derivations, not effort. The tactic line is reported without direction. Every SLang figure is from a local
mojave branch until that branch is public. Until then these counts stay outside reproduce.sh, as the MetaPRL L1 files did.
SL1's instrument compares bytes. A declaration that captures a name changes what an unchanged file means without changing its
bytes, so a 0 / 0 / 0 reading does not show that pre-existing proofs still replay (Addendum 1).

## Addendum 1 (2026-11-07, the 38th vir head): SL1 re-scored at c80941362, FALSIFIED

**Written after every SLang figure. It changes no reading rule; it applies SL1's own falsifier at the sha the arm named for the
repair.**

**What happened** (the arm's account, bisected by it with one instrument, `l2/check-l2.sh`; vir did not re-drive the replays).
D-S10 (2246bce1f) adds `declare argl{'t}` to `virl1_induct.mli`. `virl2_typing` already declares `argl{'al}`. The bare name
`argl` in `virl2_cons1` and the `virl2_sem*` family (which extend both L1 and L2) then resolved to L1's declaration. That
happened in `.ml` statements and in `.prla` stored tactic text, which is re-parsed in the module's context. Nothing errored at
build. At 73bd3ac0d all 19 L2 modules were GROUNDED (1,362 rules). At 2246bce1f and at f1c3d89e9: cons1 50/54 · semt 39/48 ·
sems 84/94 · semr 139/153 · sem 414/542. No published L2 figure is affected: RESULTS-7's MetaPRL column predates D-S10.

**So the f1c3d89e9 reading was wrong in substance.** SL1's claim is that nothing pinned moves. At f1c3d89e9 its bytes did not
move, but 165 pre-existing rules stopped replaying (4 + 9 + 10 + 14 + 128 across those five modules). The 0 / 0 / 0 above is a correct byte count that does not answer the
prediction.

**The repair** (c80941362, one commit on f1c3d89e9): every L2 `argl{` in those six modules is written `Virl2_typing!argl{`.
The arm reports 19/19 L2 modules GROUNDED, 1,362 rules, PRIM 0, and the SLang stages fresh (47/47 · 28/28 · 34/34).

**The re-score**, same command as above, count.py from vir 803a9ef, at c80941362:

| row | at f1c3d89e9 | at c80941362 |
|---|---|---|
| SLM.SL1.rulesEdited | 0 | **33** |
| SLM.SL1.defsEdited | 0 | **6** |
| SLM.SL1.prlaChanged | 0 | **4** (sem, semr, sems, semt) |
| every other slangm row (32 of 35) | — | byte-identical to the f1c3d89e9 output |

⇒ **SL1 FALSIFIED**: pre-existing definitions, rules and stored proofs change. All 10 changed files (6 `.ml`, 4 `.prla`) differ
from f1c3d89e9 ONLY by that qualification. Checked mechanically: each file compared with `Virl2_typing!argl{` rewritten to `argl{`
on both sides, 10/10 equal; a one-character mutant of one file is caught. So no statement's meaning changed. The addendum still
had to edit pinned modules, and the falsifier counts edits, not meaning.

**What it costs and what it does not touch.** One declaration in the SLang work broke the L2 chain silently. Repairing it took
43 qualified items in 10 pre-existing files. SL2–SL8 read the three SLang stages, which are unchanged, so D1, D2 and D3 stand as
scored. The cause is one name declared in two theories that a third module extends together.

