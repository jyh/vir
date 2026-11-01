# O95 — the first act, summarised (2026-11-01, the 2nd vir head)

**What was done:** appendix A.2–A.3 of the O94 bundle (frozen at vir `cd64c9fd`; `object/verify-freeze.sh` rc 0) was mechanised in BOTH logics on two programs:
- program 1: the router as A.3's F states it;
- program 2: B.1's dynamic payload (erratum E9).

All predictions were pinned before the proofs they predict. **Nothing here is new measurement.** Every figure is a harness row (H) or a quote (Q), and each points into RESULTS-1 / RESULTS-2.

**To reproduce the H figures:**
- `python3 harness/count.py --arm lean --program {1,2} lean`
- `python3 harness/count.py --arm metaprl --program {1,2} ~/projects/claude/seats/mojave`
- `harness/selftest.sh` must read rc 0.

The arms:
- **Lean:** builds only through `saltbuild.sh`. Every chain's axioms are within {propext, Classical.choice, Quot.sound}.
- **MetaPRL:** mojave's arm (theory b26a2bd84 and later; tools adef670).
- **The A.4 spike:** paris.

## The verdicts

| pred | what it claims | Lean | MetaPRL | verdict | read under | pinned |
|---|---|---|---|---|---|---|
| P1 | Lean pays casts at slice_fuse | C1heq **20** (H) | C1 **0** (H) | **HOLDS** | amend-5 class + the `≍` glyph (RESULTS-2 §0) | pre-proof; class amended post |
| P1b | the gap is a representation choice | L-FLAT: C1heqFlat **0** (H); C1flat 1 by the letter | — | **HOLDS on intent, FALSIFIED on the letter** (Nat.sub_sub is listed); both readings are kept | amend-5 | pre-proof (amend-2) |
| P2 | CTT pays in well-formedness | C2 **9** (H, `C2.p1files`) | C2gen **13** (H) | **HOLDS, provisionally** (both extractors post-date the proofs; margin 4) | amend-4 / amend-6 | post-proof conventions |
| P3 | the object under-states its rules | C3 3 · deep C3deep **5** | C3 3, strict **2** | **HOLDS** except MetaPRL-strict (FALSIFIED 2 ≤ 2) | amend-3 | ruling post-dates mojave's proof |
| P4 | the trusted base is equal | C4 0 | C4 0 | **HOLDS** | — | pre-proof |
| P5 | A.4 as written is not a refinement (E2, E3) | — | — | **HOLDS** (paris's kernel-checked witnesses, Q) | — | pre-proof |
| Q1 | Lean pays more HEq at a dynamic index | P2.C1heq **20** = program 1's 20 | C1 0 | **HOLDS on the letter (≥ 5); the premise is REFUTED** (the HEq cost is fixed, L-F5) | amend-5 + glyph | pre-proof |
| Q2 | both arms pay more side conditions | P2.C2cond **8** > 3 | C2genCond **9** ≤ 10 | **SPLIT:** Lean HOLDS, MetaPRL FALSIFIED (its cost moved to equality obligations, C2genEq 0 → 6) | path rule, now in the harness (addendum 3) | pre-proof |
| Q3 | a context-dependent rewrite is needed | P2.C3 **6** > 3 · P2.C3deep **7** ≥ 6 | C3 4 > 3, strict 2 = 2 | **Lean HOLDS (shallow and deep); MetaPRL holds only under amend-3** | amend-3 | pre-proof |
| Q4 | MetaPRL's F1 recurs | — | measured (Q) | **HOLDS** (the binder variable is `topic`, not `off`) | — | pre-proof |
| Q5 | exploratory: size | C5chain 196 (was 202, RESULTS-3 addendum 1) · deep 649 | 12 tactics / 1,236 tok (Q) | no direction | — | — |
| R1 (amend-7) | Int offsets: the rewrite stays but is context-free | P2Z.C3 **6** = 6; cleared-guard proof builds; Nat control RED | — | **HOLDS** | amend-7 | pre-build (vir 8c163d0) |
| S1 (amend-8) | the deep chain's 2nd context-dependent rule is a statement choice | P2S.C3deep **7** = 7; ctxHolds 2 → **1**; `i ≤ m` control RED | — | **HOLDS** | amend-8 | pre-build (vir 5c27056) |
| T1 (program 3) | Lean pays the ValidFrame boundary as coercions | C1coe **54** | C1 **0** | **HOLDS** (RESULTS-3 addendum 3) | pinned extractor | pre-proof (vir 98d9329) |
| T2 (program 3) | CTT pays it as well-formedness | C2cond **0** | C2genWf **7** (3 statement-wf · 4 proof-wf, H since row 31, exploratory rows) | **HOLDS** | pinned extractor | pre-proof |
| T3 / T4 (program 3) | no aux rule · no extra axiom | C3 0 · C4 0 | C3strict 0 · C4 0 | **HOLD on both arms** | — | pre-proof |
| F1/F2 (amend-9) | the 54 is the subtype; ValidFrame carries no load | C1coe 54 → **0**; builds with `hv` cleared | — | **HOLD** | amend-9 | pre-build (vir bbeac50) |

## What it says, in four lines (each line's limit is in the row it cites)
1. **Lean's indexed slices cost a FIXED HEq transport** (20 tokens) that does not grow with dynamic offsets (P1, Q1). A flat representation removes it (P1b on intent).
2. **MetaPRL pays in OBLIGATIONS rather than casts** (P2, provisional). On program 2 the cost moved from conditions to equality obligations (Q2 split), so what is predicted to be "well-formedness" needs naming more finely.
3. **The object under-states its rules on both arms** (P3, Q3). How many rules it under-states depends on the embedding (L-F3: shallow 3, deep 5), on the reading (C3 vs C3strict), and on the statement of the rules (RESULTS-2 addendum 4's second control).
4. **The context-dependent rewrite is about the NUMBER TYPE, not the logic** (R1). Nat makes the rewrite depend on an enclosing guard. Int keeps the rewrite and drops the dependence. On both embeddings, exactly ONE rewrite of program 2 genuinely needs an enclosing guard, `aux_advance_idx` (S1). The deep chain's second one was a choice of how the rule was stated.

5. **(program 3, both arms; MetaPRL in RESULTS-3 addendum 3) The boundary cost of A.1's safety theorem is the subtype, and the subtype carries no load** (T1, F1, F2). The router's own guards discharge it, so in K3 the ValidFrame refinement is decoration. CTT agrees: mojave's control proves K3 with the squashed predicate thinned, and the boundary costs one set elimination plus 3 statement-wf obligations, never a coercion. Program 3 is the first verdict with every extractor fixed before any proof. **Erratum E10:** A.1/A.2 as written quantify a free principal, and with that principal free the theorem is false.

## Limits that ride with every verdict
- **Only three programs, all over one router family** (program 3 is a safety theorem over program 2's router; this line read "two programs" until 2026-11-01). Every count is over one chain per arm per program.
- **Post-proof conventions:** P2's C2 conventions (amend-4, amend-6), P3's form-unfold reading (amend-3) and the C1 glyph correction (RESULTS-2 §0) were all written after a proof. Each file says so, and each verdict is reported under both readings where they differ.
- **Whole-tree rows are not program-scoped.** C2, C5, C5tok and C6 count all of `VIR/` and every log, so they move whenever a file is added. P2's figure is therefore read from the scoped row `C2.p1files`.
- **The fence:** vir owns both the harness and the Lean arm. Each Lean proof was committed before vir read the MetaPRL result posts (BANK-1 lessons). That the MetaPRL arm did not read the Lean arm is mojave's design, and vir has NOT measured it.
- **MetaPRL Q figures** (Q4, Q5's tactic count) are mojave's, not harness readings.
