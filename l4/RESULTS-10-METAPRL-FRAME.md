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
- **Read back at the arm's F-amendment (F13, mojave 8d298a808; a DRY read, not a score):** the F-amendment's hash is re-derived from the committed file, `d26b29b255f82882` at ed7f131fd to
  `03a3e425da9881a6` at 8d298a808, and it names the departure from inputs section 2. F12 went the LIFT way. At the re-proved modules (beb365b8c) the reader gives 180 stored derivations, equal to the arm's
  posted 13 + 52 + 41 + 74, 0 prims, Q1 0/0/0, and no L4 root yet. By hand, the third lock-table column in `virl4_step.ml` is only extended (newlock) and carried (acquire, release) on the lines that
  name it; that is a text read of those lines, and the erasure rule, read next, is the check. The re-proof cost is the arm's ledger line (about 15 minutes, Q).
- **The erasure rules (F13's filled bullets, mojave 12b54061d, hash `03a3e425da9881a6` to `4108175ff4678538` at 5b54d139b; DRY):** `l4succ_erase` and `fault4_erase` say two tables that differ only in the index column give the same successors (column dropped) and the same fault verdict, over `e` in BTerm{0}, by way of `effstep4_erase`. `lockop_index_erase` says two newlocks differing only in the index argument give the same result. Roots read with `erase=l4succ_erase,fault4_erase,effstep4_erase,lockop_index_erase` in `VIR_L4M_ROOTS`: rooted, closure 69,832 tok over 162 rules (an upper bound), roots 520 tok in 4 steps. Red control at the arm's tools f0bdad6: acquire reading the column leaves `effstep4_erase` INCOMPLETE and exactly its four dependents ungrounded.
  **Limits, to print beside the row:** `lockop_index_erase` is over argument VALUES. `argev4` evaluates the index atom before `lockop`, as it does every argument, so an index atom whose `aeval4` is `inr` leaves no step; F13's "read by no step" is a claim about the value and the column, not the atom. The N programs write the literal 0, so no row pays. The red control mutates the column only; the argument half has none.
  **Moved at b5c9a03d5 (DRY):** the arm narrowed F13's sentence to this limit (the column and the value, not the atom), hash `4108175ff4678538` to `9989461e732fee2a`; no rule changed. The erase row's closure reads 84,409 tok over 193 rules there, against 69,832 over 162 at 5b54d139b, with the erasure rules and everything they cite unedited. The growth is the reader's stated upper bound: a `reduce` use admits every `virl4_*` reduce rule, fired or not, so the new `virl4_prog` occ rules enter a closure they cannot have been used in. At scoring, this row's closure is quoted with that limit, and the 5b54d139b figure beside it.
- **N1-T and N3-T (mojave c9a991e45, DRY; `N1T=n1_ty;N3T=n3_ty` in `VIR_L4M_ROOTS`):** `tc4{0; nil; l4_N1} <--> inl{ty_int}` and `tc4{0; nil; l4_N3} <--> inl{ty_unit}`. Both terms read by hand against `inputs/L4-programs.md` §3 and L4-E1/E2 (N1's par binders, written `_`, are named q1 q2; `newlock(c1) [inv]` is written `newlock(c1, 0)`, F13's form). The source hashes the generator's comment names re-derive from vir 61ca190. Each row's closure reads 65,602 tok over 151 rules, an upper bound, and the two are the same figure because both proofs use the same script (root 979 tok, 1 step each); neither says how much of the closure either proof used. The red control (`release` keeps its capability) is as posted, not re-driven here.

## Limits known now
- The 11-06 rule (past ~100 tactic applications in one proof, stop and systematize) is read as `L4M.maxSteps`, beside C5; tactic-building time is the arm's ledger.
- `L4M.Q5.held` over six named rules is a small population; the wider readings are beside and can disagree.
