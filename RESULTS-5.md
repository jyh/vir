# RESULTS-5 — the VIR program (PREDICTIONS-amend-11 / amend-12), the scores so far (10th vir head, 2026-11-02)

amend-11 was pinned at d558682 and merged at 622c6d4. That was before either arm's first file of the VIR program. amend-12
(where a binder lemma counts) was ruled before either arm counted. **H** marks a figure read by the harness from an artifact
in this tree (`count.py --arm leanp`, `virp/out/counts-p.tsv`, gated by `reproduce.sh`). **Q** marks a quote from the
MetaPRL arm's posts that this harness has not yet extracted. A prediction is SCORED only when both arms have a figure.

## The predictions, one row each
| id | prediction | Lean (virp) | MetaPRL (mojave) | state |
|---|---|---|---|---|
| V1 | VIR-specific prims 8 → 0 | **0** (H, P.C4vir) | not yet built | Lean HOLDS; MetaPRL open |
| V1b | framework column: MetaPRL > Lean | ≤ 3 kernel axioms; P.C4 = 0 beyond them (H) | reflection: 23 prims (14 operator axioms + 9 context unfolds), bar types 24 (Q) | to score at the MetaPRL fragment |
| V2a | Lean binder lemmas ≥ 3 | **6** (H, P.binder); 4 `ins` lemmas BESIDE (H) | — | HOLDS |
| V2b/c | MetaPRL 0 in the VIR files; MetaPRL < Lean | — | (b) driven: a toy's `bterm_induction` lacks a language-shaped induction, which under amend-12 is VIR-side (Q) | open |
| V3 | adding `let_atom`: MetaPRL 0 central edits, Lean ≥ 3 | after both fragments close | — | not started |
| V4 | backend theorem: 0 per-program hypotheses | — | — | paris building (layout relation DERIVES hdisj/hacw; ruling R) |
| V5 | five exits agree | **abstract side: 5/5** (VIRP/Exits.lean; build-013, audit-003; mutant-004 red) | — | Lean abstract HOLDS; the R-reading waits on V4 |
| V6 | fragment uses no fixpoint | **0** (H, P.fix) | — | Lean HOLDS |
| V7 | progress, preservation, soundness close | **yes** (Safety.lean; audit-001..003) | — | Lean HOLDS |

## Rows with no direction, recorded beside (written before the figure they record)
- **VALUE ENCODING** (ruled 2026-11-02 at mojave's fork (A), before its numeral file): the lemmas an arm writes so a runtime
  integer can be a term. Lean: **0**, because `Atom.lit (i : Int)` carries the logic's own Int. MetaPRL: the numeral file
  (num_nil · bit0 · bit1 · neg as DEFINED operators, 0 prims) and its decode lemmas. mojave's reason: *"the reflection
  theories quote OPERATORS … there is no way to put an ITT int inside a BTerm."* This is a framework difference, so it is
  reported, never folded into V1 or V2.
- **S-counts** (inputs/vir-program-inputs.md S5, exploratory): the separation algebra's lemmas, the store↔fragment bridge,
  and the frame theorem's size. Neither arm has built the model yet.

## Decisions taken on the way (each with its check)
- **(R), 2026-11-02, at paris's finding:** F gets no topic guard, and the layout relation carries the ACL aliasing. *Wrong
  if* V4's theorem needs a topic premise. paris's `repaired_refines_all` (paris/o95-layout f10e0bc) needs none, and its
  `t < 64` mutant reds the ACL step.
- **mathlib pinned (D2's first arm):** virp/ is a separate project, so lean/'s reproduction needs no mathlib.
- **V5's code map:** 0x1040 ↦ truncated, 0x1041 and 0x1042 ↦ unauthOrRate. The machine is finer than A.2's one drop code.

## ADDENDUM 1 (2026-11-02, the 10th vir head, after PR #15 and paris's sim_label)
- **Stage 2, the separation model (Lean, H):** `virp/VIRP/Sep.lean` to the shared input S1–S5 (merged 5591d8b BEFORE it);
  build-014 + audit-004 EXIT=0; S5 counts `P.sep.theorems` 8 · `P.sep.laws` 5 (EXPLORATORY); mutant-005 (frame without
  disjointness) RED. ⚠️ FINDINGS **L-F6**: in this fragment the frame holds without the type system, so stage 2 is not
  evidence for linearity.
- **MetaPRL steps 1–2 (Q, mojave @[bus] 12:48):** 43 rules grounded, **0 prims** (V1's MetaPRL side so far: holds at steps
  1–2); the binder well-formedness cost a 19-rule VIR-side variable family (V2b reads against it when the fragment closes).
- **V4, the label half (Q until composed here):** paris's `sim_label` (paris/o95-layout 97ec297): for EVERY store and every
  R-related machine state, the repaired router stops at the exit `F_closed` names. Its ONLY premise is R. `Fc` restates
  F_closed's right-hand side and cites vir 120c906. V4 is SCORED only when vir composes it with `F_closed` and reads the
  premise list at the object (STATUS-vir row 82). The post-state half (`sim_one`) is paris's next act.
- FINDINGS **X-F2**: the ACL aliasing and the (R) ruling.
