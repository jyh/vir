# RESULTS-9: amend-19, the three-sorted L1 induction rule (both arms)

**Status: DRAFT on local `ind-score`, 2026-11-04.** Predictions: `predictions/PREDICTIONS-amend-19.md` at d6cb991, pinned before
either arm stated the rule. Every figure below is a row of a counts file, produced by the harness and never typed:

- **Lean**: `l1/out/counts-ind.tsv` (`count.py --arm ind l1`), rule in `l1/VIRL1/Induction.lean` at 93efc67.
- **MetaPRL**: `l1/out/counts-indm.tsv` (`count.py --arm indm --base ec912bd80 --ext 3772fdf7e <clone>`). Base is the arm's
  L1-closed sha; ext is the sha the arm named for its rule (its post, 2026-11-03 21:29).

⚠️ **LIMIT, beside every MetaPRL figure:** ec912bd80 and 3772fdf7e are in the MetaPRL arm's LOCAL tree and are on no public
remote at this commit. The MetaPRL rows are reproducible from the artifacts only once that arm publishes them. Until then a
stranger cannot rebuild them, and `harness/reproduce.sh` does not check them.

| row | prediction | Lean | MetaPRL | verdict |
|---|---|---|---|---|
| I1 | no L1 definition, rule or stored proof edited | 0 edited · 1 new file | rules 0 · defs 0 · archives 0 · 3 new files (`virl1_induct.ml/.mli/.prla`) | **HOLDS** both |
| I2 | derived: 0 prims, 0 framework files; Lean axioms ⊆ the standard three | 5 audited, 0 non-standard (`[propext]` only; the "none at all" parenthesis was wrong, the bound holds) | 0 new prims · 0 framework files · grounded 37/37 under REPLAY (Q: the arm's fresh `status_all` + `classify.py`, posts 21:29 and 21:51) | **HOLDS** both (MetaPRL's grounded figure at Q) |
| I3 | Lean ≤ 40 proof lines, 0 aux lemmas | 25 lines · 0 aux · 509 proof tokens | — | **HOLDS** |
| I4(a) | unpacking lemmas = distinct arity shapes in L1's operator list, ± 0 | — | 28 operators · **8 shapes** · **9 unpacking lemmas** (8 in stage U, one per shape; plus `compat_nil_st` in stage S) | **FALSIFIED by one** |
| I4(b) | MetaPRL C5 ≥ 10 × Lean C5 tokens | 509 | **69,794** tokens, 37 rules, 40 steps | **HOLDS: 137.1×** |
| I5 | two stages, reported | — | U: 17 rules, 19,130 tok (`l1_op_induction` alone 10,689) · S: 20 rules, 50,664 tok (`l1_induction` alone 38,702) · 0 rules in neither | reported |
| I6 | W3 premises, reported | 8 (X1–X8) | 0: the rule is over L1-closed, which carries no W3 form | reported, no direction |
| I7 | one L1 property re-proved by the rule (exploratory) | EMPTY: no L1 theorem quantifies over wf terms | owed (the arm's next item) | — |

## Readings that ride with the figures

- **I4(a) as written.** The prediction says "one unpacking lemma per arity SHAPE". The extractor counts every new rule that
  concludes a subterm list from a literal `compatible_shapes` premise, and finds 9. Eight sit in stage U, exactly one per shape
  (`unpack_s` … `unpack_s0001`). The ninth, `compat_nil_st`, unpacks the empty shape a second time, over `list{BTerm}` instead
  of the language, and serves stage S. The shape prediction holds within U, but the count prediction as worded is off by one,
  so it is scored FALSIFIED. The 8 the arm declared (its post (5)) is the U column.
- **C5 is the stored derivation, never its leftovers.** A MetaPRL archive stores a proof step as `ext_rule[text]{status; goal;
  subgoals; extras}` (`tactics/proof/proof_term_boot.ml`). The extras are subtrees kept from earlier refinements that no
  longer match a subgoal. `l1_induction`'s archive keeps 38 such steps (39,002 tokens) from the arm's earlier piecewise
  refinement, which its own post (7) says it re-did as one tactic. They are printed beside (`INDM.extras.*`) and are not the
  proof. A walk that does not split the slots reads 108,796 tokens instead.
- **Two methods agree.** The arm's own script count is 69,834 tokens (U 19,148 · S 50,686), against this extractor's 69,794
  (U 19,130 · S 50,664), within 0.06 %. The arm partitioned the rules by hand. Here the partition is the closure, by name, of
  each top rule's derivation, and it reproduces the arm's 17/20 split exactly.
- **I1, after the rule's sha.** The arm's later e0cf88ed2 drops a comment in pre-existing `virl1_hoas_lang.ml`. It moves no
  rule, definition or stored proof (comments are stripped before comparison) and lies after the scored ext sha, so it is
  recorded here and not scored.
- **Numerals.** The arm declares its binary literal set as a REPRESENTATION DEVIATION (its DECLARATIONS-L1-METAPRL N1). A2
  counts one premise per literal FORM of each arm's syntax: 6 for MetaPRL (its N2), 1 for Lean.

## Harness

`count.py --arm indm` and selftest ARM40. The arm went red first, with no such arm in count.py. Its fixture builds a git pair
whose counts derive from the fixture's own strings (an extra subtree, a comment-only edit, a decoy `Perv!rule`, an operator
outside the list). The mutant that counts extras as proof is KILLED.
