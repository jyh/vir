# RESULTS 2 — PROGRAM 2 (the dynamic-payload router, E9), both arms (2026-11-01 02:4x)

Inputs `inputs/program2-inputs.md` and predictions `predictions/PREDICTIONS-program2.md`, both pinned at vir 5d6f739a before either arm's first proof. H = harness · Q = quoted.

## §0 A CORRECTION to RESULTS-1 and to vir's posts, and its copies
The C1 token class did not contain `≍`. Lean's printer writes `HEq a b` as `a ≍ b`, so the class missed most HEq uses. **Program 1's C1heq on the slice path is 20, not 5** (`Slice.congr_heq` 10 · `Slice.heq_of` 9 · `Slice.adv_adv_heq` 1). The preregistered total C1 reads 93 with the glyph (it was 31). Every verdict stands, and P1 holds with a larger margin. This is a needle defect in vir's own extractor. **Copies corrected:** RESULTS-1 addendum 3 is annotated in place. The 01:2x and 01:4x bus posts that said "C1heq = 5" are superseded by the post announcing this file. `count.py` now includes `≍` in both classes.

## Lean (L-IDX shallow; `router2_fusion`, saltbuild EXIT=0 on build 13, `[propext, Quot.sound]`)
| count | program 2 | program 1 |
|---|---|---|
| C1heq (path) | **20** (`Slice.congr_heq_dep` 10 · `heq_of` 9 · `adv_adv_heq` 1; `aux_advance_idx` 0, closed by `subst`) | 20 |
| C2cond (side proofs in the chain) | **8** | 3 |
| C3 aux used | **6** (program 1's 3, plus advance_idx · advance_past_dguard · guard_cond_eq) | 3 |
| C5chain | 202 | 84 |
H for every figure. The chain compiled at its FIRST full elaboration (build 13). Build 12 was red on `slice_fuse_dep`'s proof (a generalize motive), fixed by a dependent twin of `congr_heq`.

## MetaPRL (mojave @[bus]; model B)
| count | Q (mojave) | H (harness) |
|---|---|---|
| C1 | 0 | 0 |
| C2gen wf / eq / cond | 3 / **6** / 9 = 18 | 4 / 6 / 15 = 25 ⚠️ |
| C3 / strict | 4 / 2 | 4 / 2 (aux declared in vir.ml, used in c2-router2.mp: sink_guard, guard_swap + the advance and read_u32 unfolds) |
| C4 | 0 | 0 |
⚠️ **C2gen differs: H 25 against Q 18, OPEN.** The program-2 replay has 21 CHILDREN lines in one session, and vir has not found which of them mojave excludes. It is QUOTED for scoring until the difference is named (STATUS row 14).

## Verdicts
- **Q1 HOLDS on the letter** (L-IDX 20 ≥ 5; MetaPRL 0). ⚠️ **But the premise is refuted:** the dynamic index cost NOTHING extra in HEq. The new arithmetic (`12 + (off − 12) = off` under `12 ≤ off`) became an `Eq` proof, closed by `subst` in `aux_advance_idx`, and the HEq count is identical to program 1's. What Lean pays at slice_fuse is a fixed cost of the indexed representation, and it does not grow with dynamic offsets.
- **Q2: Lean HOLDS (8 > 3). MetaPRL FALSIFIED on generated-cond (9 ≤ 10)**, by mojave's own scoring and convention. It holds on the displayed reading and on vir's harness reading (15). ⇒ **SPLIT.** MetaPRL's cost moved from CONDITIONS to EQUALITY obligations (C2eq 0 → 6, the two arithmetic bridges), which Q2 did not name.
- **Q3: Lean HOLDS (6 > 3, three new aux rules, one of them context-dependent: advance_idx). MetaPRL holds only under amend-3 (4 > 3); on C3strict it is FALSIFIED (2 = 2).** mojave measured that NO context-dependent rewrite was needed in model (B), because offsets are unbounded ints and `24 ≤ off` never enters the equation (M-F3 again). ⇒ **The context-dependent rewrite is an artefact of Nat subtraction in the Lean model, not of the VIR.** L-DEEP for program 2 was not built, so C3deep ≥ 6 is UNSCORED.
- **Q4 HOLDS** (mojave, measured: `Rewrite condition has free variable … 'topic`). The variable is topic, not off as Q4 guessed.
- **Q5:** Lean C5chain 202; MetaPRL 12 tactics / 1,236 tokens (Q).

## Findings
- **L-F4** Nat truncated subtraction manufactures a context-dependent rewrite (`12 + (off − 12) = off` needs `12 ≤ off`), and Int offsets (model B) do not. Some of Lean's cost is the CHOICE OF NUMBER TYPE, not the logic.
- **L-F5** the HEq cost is FIXED per representation and does not scale with dynamic indices here (Q1's premise).
- mojave's D1–D3 (MetaPRL defects: archive id ≥ 2^30 fails to load, a ~1,024-char line limit, an export after a failed step overwrote program 1's .prla and was restored from git) are mojave's, recorded in FINDINGS.md.

## ADDENDUM 1 (03:1x): row 14, the MetaPRL program-2 C2gen difference narrowed from 7 to 3, named, not closed
mojave @[bus]: its 18 EXCLUDES the two `omegaT` closer steps (CHILDREN 36, 42: wf 2 + assertion 3 each = 10 closer residuals) and ADDS the 3 lemma wf from runs-c2-lemmas.txt.
The harness now skips the CHILDREN of any step whose command runs `omegaT`, for both programs (program 1 still reads 13 = Q), and reads the lemma replay for program 2. **H = 21 (wf 3 · eq 6 · cond 12) against Q = 18 (3 · 6 · 9).** The remaining 3 are the lemma replay's `slice_fuse_c` assertions. mojave says neither slice_fuse form is on program 2's path, so by the path rule they should NOT count. The harness does not yet scope the lemma replay to the program's path, which is a harness defect.
⚠️ **This difference DECIDES Q2 for MetaPRL:** cond 9 (path-scoped, Q) gives FALSIFIED, and cond 12 (unscoped, H) would give HOLDS. **Scored on the path rule: Q2 FALSIFIED for MetaPRL stands.** The harness figure is the defective one until it scopes lemmas by path (STATUS row 14 stays open for that one change).
