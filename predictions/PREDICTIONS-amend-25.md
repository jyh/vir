# PREDICTIONS amendment 25 — L1 in surface syntax, MetaPRL arm (OBJECT-SURFACE-L1)

Written 2026-11-15 by the 81st vir head, in the same commit as `object-SURFACE/OBJECT-SURFACE-L1.md`, BEFORE any surface file on the
MetaPRL arm. **INFORMED** (see the object's preamble): the writer has read the arm's L1 statements at 2d9a6c7f0 and the reflection
library's `reduce_subst` and `bind_eta`, and has not seen any attempt at the target. At this file's commit, no rule named in the
object's §1–§3 exists on the arm. The labels are SU1–SU8, chosen because no label of that form exists in this repository.

| id | prediction | falsifier | instrument |
|---|---|---|---|
| SU1 | §1's surface rule is DERIVED from `l1s_induction` (or `l1_induction`) | a new primitive, or an L1 rule or definition edited | the arm's census (prims; `virl1_*` defs and rules edited, base 2d9a6c7f0) |
| SU2 | its statement carries 0 `mk_bterm`, 0 `bdepth`, 0 `BTerm`/`L1Lang`, 0 recognisers (`wfs`, `is_tyterm`, `isNum`, `tyok`) | any of them in the stored rule's statement | a token count over the rule's statement text |
| SU3 | the binder cases take §1's HOAS form (`all x. Pa x => Pe (e x)`) | a binder case that needs a context Γ, a depth, or a fresh-variable-at-depth | hand read of the four binder premises, posted with the rule |
| SU4 | the only residual side condition is one membership hypothesis per binder (4 in all) beyond the motives' `[wf]` premises | any further premise in any case | premise count per case against §1 |
| SU5 | there is no variable case | a premise whose conclusion is `Pa` of a variable | hand read |
| SU6 | the derivation of §1 (its closure EXCLUDING `l1s_induction`'s own) costs ≤ 30,000 C5 tokens | > 30,000 | `count.py` C5 over the closure (the arm's unit, an upper bound where `reduce` is used) |
| SU7 | §2's four safety statements are free of the SU2 tokens, and are DERIVED from the existing theorems through one bridge lemma to `tyok` | an SU2 token in a statement, or a re-proof of progress/preservation | token count; closure read for the existing theorem names |
| SU8 | §3's inlining theorem is stated with no SU2 token and proved as an `interactive` rule | a `prim`/`prim_rw`, or an SU2 token in the statement | the stored rule |

**Basis for SU6's bound (a guess, recorded as one):** `l1s_induction`'s L1 stage is 5,728 tokens (RESULTS-11); the strengthening
over substitutions is new work of the same kind as amend-19's S stage (50,664 for `l1_induction`, RESULTS-9 I5). 30,000 sits between.
**Directions only, no thresholds:** whether §2's restated `preservation` is shorter than the existing one (C5, reported), and whether
§3 needs the bridge lemma or goes through `den` directly (reported).
**What a falsification would mean:** SU3/SU4 falsified is the main result the Captain asked for (*"are there irritating side
conditions?"*), and is reported as the answer, not as a failure of the arm.
