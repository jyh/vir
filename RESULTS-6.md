# RESULTS-6 — layer L1, the typed pure core (O95; OBJECT-L1 at vir dc44f15; amend-13, amend-14)

Every figure here is a row of `l1/out/counts-l1.tsv` (`harness/count.py --arm l1 l1`, re-derived by `harness/reproduce.sh`,
rc 0) or is labelled as something else. The MetaPRL arm's figures are owed (it began building after the pin), so every
two-arm prediction is UNSCORED below, never assumed.

## The scoreboard (amend-13 W1–W8)
| prediction | Lean (l1/, this file's sha) | MetaPRL (mojave) | verdict |
|---|---|---|---|
| W1 C4vir = 0 | **0** (`L1.C4vir`) | owed (scored on `virl1_*` alone, amend-14) | Lean HOLDS · MetaPRL unscored |
| W1b framework MetaPRL > Lean | Lean: axioms beyond the standard three **0** (`L1.C4`); the standard three only (`L1.audit` 35 rows) | owed: pin figure + PARTIALITY THEORY `itt_bar` (NOT-AT-PIN, 24 prims / 4 derived as the arm reports) beside it | unscored |
| W2a Lean ≥ 6 binder lemmas | **3** (`L1.binder`), and **1 BESIDE** (`L1.binder.substLOnly`) | — | **FALSIFIED** (3; 4 with the one beside) |
| W2c MetaPRL < Lean | 3 | owed (Lang{sop} REVIVED, sub-column) | unscored |
| W3 (i) a new operator costs 0 edits, (ii) a type former costs Lean ≥ 3, MetaPRL 0 | — | — | after BOTH arms close (the extension commits) |
| W3b the parameter's own cost | the hypotheses about Σ: `Sig.Lawful` (2 fields) + `S.O → False` | owed | EXPLORATORY |
| W4 the backend | not in L1 | — | at L3 |
| W5 K1–K5 agree | 120 · ¬Dom · 42 · 7 · 55, each terminating program with a ⟶* trace (`Programs.lean`) | owed | Lean HOLDS · MetaPRL unscored |
| W6 the fixpoint is used, and leastness for K2 | `L1.fix` **1** · `L1.leastness` **2** | owed (itt_bar's fix rule) | Lean HOLDS · MetaPRL unscored |
| W6b the side condition | `L1.continuity` **1** (`Φ_cont`, 12 lines) | owed (adm) | EXPLORATORY |
| W7 the six steps close | all required theorems, no fuel, no primitive step rule (`l1/STAGE-L1-LEAN.md`) | owed | Lean HOLDS · MetaPRL unscored |
| W8 conservative extension | — | — | at L2 |

C6 for the Lean arm: 18 logged saltbuild runs (`L1.C6`; 12 builds, 2 scratch, 2 audit, 2 mutants).

## What the W2a falsification says
amend-13 predicted at least 6 Lean binder lemmas from two syntactic categories and three binder shapes. The arm needed 3 (4
counting `HasTypeL.subst`, which names the list half `substL` and is not on the frozen token list). The reason is structural,
not an accident of style: a call-by-value semantics of CLOSED programs substitutes only CLOSED values, so the arm defines no
shift, weakening is at the outer end of the context (no index arithmetic), and the substitution lemma is one mutual theorem.
The prediction was written from the router fragment's 6, where the store and runtime values made more binder work. **What it
does to W2c:** W2c (MetaPRL < Lean) now asks the MetaPRL arm to come in under 3, with Lang{sop}'s revived rules counted
VIR-side (amend-13's ruling).

## The MetaPRL arm's declarations (owed by amend-13 before its first L1 file; posted 17:50, 0 L1 files at the post)
D1 pin jyh/metaprl fb8e715d7 (libmojave 623f7ac), branch mojave/vir-l1 = the pin + itt_bar + L1 files only · D2 Σ as Lang{sop},
REVIVED from `theories/itt/reflection/obsolete/itt_hoas_lang.ml` (port status unmeasured at the post; the fallback is a BTerm
subset with its own wf predicate, to be announced before any count) · D3 files `theories/vir/virl1_{hoas_lang, sig, syntax,
eval, step, typing, safety, den, progs}` · D4 partial results `bar{Val}` from `theories/vir/itt_bar.ml`, ⟦·⟧ by itt_bar's fix
rule, K2's ¬halts by fixpoint induction. **The fork it named (itt_bar is not at the pin) is ruled in amend-14.**
