# RESULTS-11 (DRAFT): the SLang scoreboard, amend-20 SL1–SL8 and amend-22 D1–D4, MetaPRL arm

**DRAFT. This frame was written 2026-11-07 by the 33rd vir head, after the MetaPRL arm's SLang act 1 (mojave/slang 41de5e05d:
`vir_slang`, definitions and well-formedness only) and BEFORE any L1-stage file (`vir_l1slang`), the generic induction rule, or
the L1 rule exist.** Every L1 figure below is OWED. The frame fixes how each row is read, so that the reading cannot be shaped by
the L1 figures. One reading rule (SL3 on bound names, below) was written AFTER act 1's read, which is what raised it. That is
declared, and it is the only rule here written after any SLang figure existed.

The Lean arm takes no act (amend-20). Its comparator is amend-19 I3's 509 tokens (RESULTS-9).

## The run
`VIR_SLANG_ROOT=<the arm's L1 rule> count.py --arm slangm --base 73bd3ac0d --ext <the arm's named sha> <clone>`, with count.py
from vir ccc4fdd or later (ARM46 + ARM47), and NO VIR_SLANG_FW/L1, so the stages are read MEASURED. If the measured stages are
not exactly {vir_slang} / {vir_l1slang}, that is a finding, posted before scoring. Every figure is read at a sha the arm named on
the bus. A figure from any other sha is void.

## Rows

| row | falsifier (amend-20 / amend-22, quoted in short) | harness row(s) | reading at 41de5e05d (act 1, framework only) | at the L1 sha |
|---|---|---|---|---|
| SL1 | ≥ 1 pre-existing definition, rule or `.prla` changes | SLM.SL1.rulesEdited / defsEdited / prlaChanged; otherChanged BESIDE | 0 / 0 / 0; MetaprlInfo (one line, module list) BESIDE | OWED |
| SL2 | a prim is added; grounded under REPLAY | SLM.SL2.newPrims; SL2.grounded is Q (the arm's status_all) | 0 new prims; the arm posted 24/24 FRESH, 24 GROUNDED | OWED |
| SL3 | the framework module(s) name an L1 operator or a `virl1_`/`virl2_` term | SLM.SL3.hits (scored); SLM.SL3.binderOnly BESIDE; hand read | hits 1 = `kids`, a bound name only (binderOnly 1); by hand: no L1 term applied, no nat sort literal ⇒ HOLDS at this sha | OWED (re-read any edit to vir_slang) |
| SL4 | the L1 rule's derivation goes through a recogniser (`wfs`, `is_tyterm`, `isNum`) | SLM.SL4.recogHits over the closure from ROOT; SL4.control beside | Q (no root yet); control 3 | OWED |
| SL5(a) | L1 stage C5 > 25,332 tok | SLM.SL5.L1.C5tok | 0 (no L1 stage) | OWED |
| SL5(b) | framework + L1 C5 > 69,794 tok | SLM.SL5.total.C5tok | framework 649 so far | OWED |
| SL6 | a direction (type · atom · expression × both) not proved | Q: the arm's six rule names, each read in its `.prla` | not reached | OWED |
| SL7 | reported only | Q | not stated | OWED |
| SL8 | reported | SLM.SL8.{fw,l1}.{rules,steps} | fw 24 rules / 24 steps | OWED |
| D1 | = SL5(a) | SL5.L1.C5tok | — | OWED |
| D2 | L1 stage ≤ 5,090 tok | SL5.L1.C5tok | — | OWED |
| D3 | attribution follows SL4 × D1 | — | — | OWED |
| D4 | the tactic line, BESIDE, never in C5 | Q: the arm's ledger line (l2/slang/TACTIC-LEDGER.md) | tooling T1 (vir_walk) is UNSTAGED: 3 rules, out of every stage | OWED |

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

## Departures (the arm's, declared before the proofs they touch)
D-S1 explicit variable sort `SLang{ssig; vs; s}` · D-S2 sorts are nat · D-S3 children as a sort-indexed tuple (SKids, kidl) ·
D-S4 a node carries its signature ENTRY, not an index (Img's map must be closed, itt_image img_type), so the L1 rule splits on
membership in ssig1.

## Limits
SL3's reader matches names and cannot tell a binder from a term, so `binderOnly` and the hand read carry that distinction.
SL5 is C5 over stored derivations, not effort. The tactic line is reported without direction. Every SLang figure is from a local
mojave branch until that branch is public. Until then these counts stay outside reproduce.sh, as the MetaPRL L1 files did.
