# PREDICTIONS amendment 20: a SORTED language type, and L1's three-sorted rule from it (an L1 addendum, MetaPRL arm)

**Written 2026-11-05 ~16:0x PST by the 19th vir head, AFTER amend-19's proofs exist on both arms (RESULTS-9) and BEFORE either
arm states a sorted language type.** At this file's commit, `git log --all -S SLang` reads 0 commits in this repository and 0 in
the MetaPRL arm's tree. **This amendment is INFORMED, and says so:** its design was worked out in the helm's window with the
Captain on 2026-11-05, starting from vir's reading of amend-19's cost, and vir's sketch (the "Design" block below) is shared
text. Its predictions are therefore guesses by a party who has seen the existing MetaPRL derivation, and are scored as such.

## Why it exists (the Captain's ruling, in the helm's window, 2026-11-05 ~16:00)
Reading `l1_op_induction` and `l1_induction` (virl1_induct, amend-19 stages U and S), he asked whether S is needed because
`L1Lang{sig1}` contains terms the grammar forbids. It does: `Lang{sop}` (virl1_hoas_lang) constrains a node's operator and its
children's binding depths, never their SORTS, so `app(let(…), arrow(…))` is in L1Lang. Stage S pays for a sort discipline the
representation lacks (U 19,130 tokens, S 50,664: RESULTS-9 I5). A set type over L1Lang would restate S without making it
cheaper. A SORTED language type, whose operators declare their own sort and each child's sort, would make the generic
rule three-sorted by construction. His words: *"Yes, it seems we should try it."* On the naming question (one generic type, or
an L1 one): vir recommended both, a generic `SLang` and an L1 instance `L1SLang`, and he answered *"yes, ratified, thank you"*.

## Design (shared text; the arm may represent it differently and DECLARES any departure)
- A **sort signature** `ssig` is a list of entries (operator, result sort, sorted shape), the sorted shape a list of
  (binding depth, child sort). Sorts are a parameter of the signature, not fixed by the framework (L2 and L3 add sorts).
- `SLang{ssig; s}` is the terms of sort `s`. Variables are in the sort the signature names as the variable sort (L1: atoms). A node
  `mk_bterm{d; op; st}` is in sort `s` iff `ssig` gives `op` result sort `s` and each child is at its binding depth, in its sort.
  It is built as `Lang{sop}` is (a union over finite approximations), with each approximation a family indexed by sort.
- A signature is **well formed** when every entry's depths equal the operator's built-in `shape{op}`, so the sorts cannot claim a
  node that `mk_bterm` builds differently.
- `SLang`'s generic induction rule: one motive `P[s; t]`, a variable premise, and one node premise whose IH is `P[s_i; y_i]` at
  each child's own sort.
- `L1SLang{sig1; s} = SLang{ssig1; s}`, with `ssig1` L1's sort table over OBJECT-L1's operator list (sorts at least: type ·
  numeral · pure operator · atom · argument list · expression).

## Predictions (each scored from the artifacts; each extractor added red first, before scoring)
- **SL1 (an ADDENDUM: nothing pinned moves).** Every pre-existing `virl1_*` / `virl2_*` / framework module's rules and `.prla`
  are unchanged; the new work is in NEW modules only. **FALSIFIED if** ≥ 1 pre-existing definition, rule or stored proof changes.
- **SL2 (DERIVED).** `SLang`, its well-formedness and its induction rule are definitions plus DERIVED rules: 0 new prims, grounded
  under REPLAY (`status_all`). **FALSIFIED if** a prim is added.
- **SL3 (GENERIC).** The module(s) defining `SLang` and its rule name no L1 operator and no `virl1_` / `virl2_` term (the content
  test of the L2 Y1 ruling: a module's own text, `.ml` and `.mli`, comments stripped). **FALSIFIED if** one does.
- **SL4 (the L1 rule falls out).** amend-19's three-sorted rule, in this arm's representation (one premise per form, the IH of
  each child at its own sort), is derived from `SLang`'s rule instantiated at `ssig1` and the operator split, with NO sort
  recogniser (`wfs`, `is_tyterm`) in its premises or its proof. **FALSIFIED if** the derivation goes through a recogniser.
- **SL5 (it is cheaper).** (a) C5 of the L1 stage (`ssig1`, `L1SLang`, the per-form rule and everything L1-specific under it)
  ≤ 25,332 tokens, half of amend-19's S. (b) C5 of the framework stage (`SLang`, its well-formedness, its rule) plus the L1 stage
  ≤ 69,794 tokens, amend-19's U + S: the sorted route costs no more in total than the route it replaces. **FALSIFIED if** (a) or
  (b) exceeds its bound. Both figures and their ratios to Lean's 509 tokens (RESULTS-9 I3) are reported.
- **SL6 (the sorts agree with the recognisers).** For each of type · atom · expression, both directions: `t ∈ L1SLang{sig1; s}`
  ⇒ `t ∈ L1Lang{sig1}` with its recogniser `btrue` at depth `bdepth{t}`, and conversely. **FALSIFIED if** a direction is not
  proved; a direction shown FALSE is a finding about `ssig1` or the recognisers, recorded before any repair.
- **SL7 (a set-type statement layer, reported).** If the arm states the rule over set types (`{t: L1SLang{…} | …}` or
  `{t: L1Lang{sig1} | wfs{…}}`), its C5, no direction.
- **SL8 (reported).** Proof steps and rules per stage; the framework stage's C5 apart from L1's, so a later layer that reuses
  `SLang` is charged only its own instance.
- **Lean arm: NO ACT.** Lean's mutual inductive types are already sorted; amend-19 I3's 509-token proof is the comparator.
- C1 to C6 keep their amend-1..19 definitions on this addendum's files and are reported without direction.

## Numbering
This takes the number 20. vir's L4 predictions draft (§4 of its L4 programs draft, UNPINNED, in the private record) called itself
amend-20; it becomes amend-21 when it is pinned.

## What would show this amendment unfair
a sorted language type stated on the MetaPRL arm in a commit before this file's sha · SL5's bounds re-read after the arm's first
SLang proof · a count taken from a sha the arm did not name · an SL6 direction scored on a recogniser edited after this sha.
