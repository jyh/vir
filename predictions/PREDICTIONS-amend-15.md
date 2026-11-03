# PREDICTIONS amendment 15 — W3 on layer L1: the central definitions' NAMES and the extension's TIMING, fixed before either arm extends

**Written 2026-11-02 ~18:2x PST by the 11th vir head, AFTER the Lean arm's L1 close (l1-lean, PR #21; adequacy c03cf34) and
BEFORE any W3 extension commit on either arm.** At this file's commit, `git log --all -- l1/` holds no commit adding `max` or a
product type, and the MetaPRL arm has posted no L1 extension. amend-13's W3 prediction and thresholds are UNTOUCHED. This file
fixes what W3's count reads, as amend-11's V3 fixed `Tm · Step · HasType · den` for the router.

## The four categories (OBJECT-L1's term syntax · step relation · typing relation · denotation)
| category | Lean names (l1/VIRL1, as built) | MetaPRL names |
|---|---|---|
| syntax | `Ty`, `Atom`, `Tm` | owed by the arm BEFORE its extension commit (its D3 files `virl1_syntax`, …) |
| step | `Atom.eval`, `Atom.evalL`, `Step` | owed (`virl1_eval`, `virl1_step`) |
| typing | `HasTypeA`, `HasTypeL`, `HasType` | owed (`virl1_typing`) |
| denotation | `head`, `Head.run`, `Φ`, `den` | owed (`virl1_den`) |

**The count is the number of CATEGORIES with at least one EDITED declaration (0–4)**: a declaration that exists at both shas
with different text, comments stripped. A new declaration is an ADDITION and is reported beside, never counted. An edit to the
Σ instance (`L1.lean`: `Prim`, `Prim.args`, …) is not a central definition. That is what the parameter is for. The extractor
is `count.py --arm v3l1 --base <pre> --ext <commit> --prefix l1/VIRL1` (selftest ARM25, mutant killed, with a NONCOMPUTABLE
`den` in the fixture, because the shared block splitter glued a modified declaration onto its predecessor. The fix is local
to this extractor, so no recorded router count moves).

## Timing and blindness
Each arm makes its two W3 commits ((i) the pure operator `max : (int, int) → int`, (ii) the product type former `τ₁ × τ₂`
with a pair and its two projections; where the pair and projections sit, atom or expression, is the arm's call, declared in
its commit message) only AFTER BOTH arms have posted "L1 closed", and neither reads the other's extension before making its
own. This is the router's V3 discipline. The Lean arm closed first, so it waits.

## What would show this unfair
a category list changed after an extension commit is counted · an extension commit on either arm before both closes are posted ·
an arm whose extension commit was made after reading the other's.
