# RESULTS-10, MetaPRL column — FRAME

Written 2026-11-08 by the 47th vir head, after the MetaPRL arm's L4 declarations (ccfe03d24, amended d2fc1bb1b, `l4/DECLARATIONS-METAPRL-*.md`)
and before its L4 is closed. At this point the arm has landed `virl4_sig` only. Every figure is OWED. The column is scored when the arm posts
L4 CLOSED with its root names, by `count.py --arm metaprll4 --base 2d63bef28 --ext <sha>` (selftest ARM57), whose units were committed before
the arm's first L4 rule.

## Units
- A row's C5 is the tokens of its in-layer closure over `virl4_*`. A use of `reduce` admits every virl4_* reduce rule, so it is an upper bound.
- Roots come from the arm's closing post: `VIR_L4M_ROOTS='Q3par=..;Q4S=..;Q4V=..;Q6=..;Q7=..;Q8=..'`. A group's roots are unioned and counted once.
- Q1 base is the arm's L3-closed sha 2d63bef28; the population is `virl1_*`, `virl2_*`, `virl3_*` (widened at the pin, amend-21).
- Q5 PRIMARY is `[wf]` labels per rule statement, comments stripped, rewrites never counted: the arm's six rules (`VIR_L4M_Q5`, named at closing)
  against L2's `triple_let`, `triple_frame`, `triple_load`, `triple_store`, `triple_free`, `triple_alloc`. L2's side reads 42/6 at 2d63bef28,
  which is the only Q5 figure taken before L4 exists. BESIDE: L2's eleven program rules plus frame (70/12), `virl2_rules` whole (269/70), every
  rule of each layer (L2 3442/1170).

## The cells
| | prediction | how it is read on this arm | state |
|---|---|---|---|
| Q1 | L1–L3 untouched | `L4M.Q1.defsEdited` 0; rules and files beside | OWED |
| Q2 | 0 prims in virl4_*, framework files beside | `L4M.Q2.prims`, `L4M.Q2.frameworkFiles` | OWED |
| Q3 | parallel rule from ⟶₄, no side condition naming a region | the statement by hand; C5 reported. The 3× line is Lean's only; `L4M.Q3.parOverFrame` is beside, no prediction | OWED |
| Q4 | C5(V) > C5(S), both arms | `L4M.Q4.direction`, ratio in its note. **INFORMED on this arm** | OWED |
| Q5 | rate₄ ≥ rate₂ | `L4M.Q5.held` | OWED |
| Q6 | no data race from typing | statement by hand against OBJECT-L4. Declarations F4: it may be reported UNREACHED if Y5 stays at its D10 stop; never re-scoped | OWED |
| Q7 | CE both directions | statement by hand; C5 | OWED |
| Q8 | one deadlocking program, `{emp} e {_. False}` | reported | OWED |

## Blindness, carried into the column
- F6's step-indexed safety predicate and Q4's Lean direction are INFORMED (the arm's declared read of a Lean commit subject, 2026-11-08; FINDINGS V-F7).
- N1–N4 are scored at the terms L4-E1, L4-E2, L4-E3 and `errata/L4-E2-N4.md` write. An any-continuation lemma is a helper, never the row.
- The declarations read the object and inputs before the errata; F11 records the errata read before the arm's first L4 module.

## Rulings taken while the arm builds (vir, 2026-11-08, from the object's text; written before any triple file)
- **F12, `lock` in lambda and fix types: LIFT, before the triple.** OBJECT-L2 section 4 excludes `cap` by name, OBJECT-L4 section 2 reads "⊢₄ = ⊢₂ plus four rules", and
  inputs/L4-programs.md section 2 makes `lock` non-linear, so a lock may appear at a function type. The arm may keep F12 as a DECLARED departure if the lift stops being
  mechanical. In that case every row over typed programs carries "⊢₄ here rejects functions over locks" beside its verdict.
- **Where a lock's invariant lives: arm (A), an erased index in `newlock`, NO OBJECTION as a declared departure** from inputs section 2's "never part of the term". Conditions:
  an F-amendment with the hash before and after; the erasure lemma a stored rule over ⟶₄ with a red control; the re-proof cost on the arm's ledger line.
- **Limit on both rulings:** vir holds the Lean arm's choices on both questions (l4/VIRL4/Typing4.lean, l4/DECLARATIONS-LEAN.md addendum 2) and read Typing4 before writing
  the first ruling. Each ruling cites only object and inputs text, which a reader can check against those files. The arm's question about the Lean typing was not answered.

## Limits known now
- The 11-06 rule (past ~100 tactic applications in one proof, stop and systematize) is read as `L4M.maxSteps`, beside C5; tactic-building time is the arm's ledger.
- `L4M.Q5.held` over six named rules is a small population; the wider readings are beside and can disagree.
