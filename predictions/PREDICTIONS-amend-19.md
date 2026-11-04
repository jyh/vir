# PREDICTIONS amendment 19 — the THREE-SORTED STRUCTURAL INDUCTION rule for L1 (an L1 ADDENDUM, both arms)

**Written 2026-11-03 ~18:4x PST by the 17th vir head, BEFORE either arm states the rule.** At this file's commit no commit on
any branch of this repository states a structural induction rule over L1 terms (read by `git log --all -S` on `three-sorted`
and `Atom.induct`: 0 commits each), and the MetaPRL arm has posted no such rule (its posts to this hour name `lang_elim` /
`lang_induction` only, the general rule its L1 already has).

## Why it exists (the Captain's ruling, council 2026-11-03 afternoon, minute §E ①)
From his reading of `virl1_hoas_lang` at the table: `lang_elim` / `lang_induction` give bterm-shaped subgoals (the variable, and
one `mk_bterm` with an ARBITRARY operator), not a case per form of the grammar. His words: *"induction is *the* primary/only
technique by which we prove anything over all programs. If we were to write a paper, this would be the key rule and we would want
to show that we can capture the induction principle well."* · *"I think we have to do it, and update L1 with the "nice" induction
rule. And in fact, that's the 3-sorted rule. If we can't do it, that's a flaw. If we can, then we need to."* · *"yes, let's do
it; it will pay off handsomly"*. ⇒ vir writes this prediction first; the MetaPRL arm DERIVES the rule from `lang_induction` as an
L1 ADDENDUM (an addition, no definition edited); the Lean arm STATES it as a theorem; vir scores both; the paper reports the cost
of the HOAS route against the free one.

## The rule (the statement both arms prove, in each arm's own representation)
Over OBJECT-L1 §2's grammar as PINNED (types · atoms · expressions). Let a scope be a depth n (the number of binders in scope:
de Bruijn depth, or a bterm's binding depth). Given three predicates

- `Pτ(τ)` on types, `Pa(n, a)` on atoms at depth n, `Pe(n, e)` on expressions at depth n,

and ONE premise per form of the grammar, each with the induction hypotheses of exactly its immediate subterms:
```
  T1  Pτ(β)                                     T2  Pτ(τ₁) ∧ Pτ(τ₂) ⇒ Pτ(τ₁ → τ₂)
  A1  x in scope at n ⇒ Pa(n, x)                A2  Pa(n, k) for every literal k (n ∈ ℤ, true, false; one premise per
                                                    literal FORM of the arm's syntax)
  A3  Pa(n, a₁) ∧ … ∧ Pa(n, aₖ) ⇒ Pa(n, p(a₁, …, aₖ))          (k = |ar(p)|)
  A4  Pτ(τ) ∧ Pe(n+1, e) ⇒ Pa(n, λ(x:τ). e)
  A5  Pτ(τ₁) ∧ Pτ(τ₂) ∧ Pe(n+2, e) ⇒ Pa(n, fix f(x:τ₁):τ₂. e)
  E1  Pa(n, a) ⇒ Pe(n, ret a)                   E2  Pτ(τ) ∧ Pe(n, e₁) ∧ Pe(n+1, e₂) ⇒ Pe(n, let x:τ = e₁ in e₂)
  E3  Pa(n, a₁) ∧ … ∧ Pa(n, aₖ) ∧ Pτ(τ) ∧ Pe(n+1, e) ⇒ Pe(n, let x:τ ← o(a₁, …, aₖ) in e)
  E4  Pa(n, a₁) ∧ Pa(n, a₂) ⇒ Pe(n, a₁ a₂)      E5  Pa(n, a) ∧ Pe(n, e₁) ∧ Pe(n, e₂) ⇒ Pe(n, if a then e₁ else e₂)
```
conclude: **∀τ. Pτ(τ)**, **∀n a. wf(n, a) ⇒ Pa(n, a)**, and **∀n e. wf(n, e) ⇒ Pe(n, e)**, where wf is OBJECT-L1 §3's
well-formedness (free variables in scope, operators at their arity) read at depth n. **Binder bodies are one depth deeper and
carry the IH there** (A4, A5, E2, E3); the conclusion holds at EVERY depth, and the object's theorems use it at depth 0.
- **E3 is in the rule although O = ∅ in L1** (the form is in the grammar; its premise is vacuous on L1's programs). An arm whose
  L1 syntax has no such form DECLARES that, and the premise is then absent, not scored as missing.
- **Extensions.** An arm whose L1 tree carries the W3 constructs (products, sums: amend-15/17) proves the rule for its tree, with
  one premise per added form; those premises are counted SEPARATELY (row I6) so that the pinned grammar's cost is comparable.
- **A3's "one premise for all of P"** is the rule as stated. An arm may instead give one premise per operator of P; it declares
  which, and I2/I3 are scored on what it built.

## Predictions (each scored from the artifacts; each extractor added red first, before scoring)
- **I1 (an ADDENDUM: nothing in L1 moves).** No L1 definition or stored proof is edited: Lean, `l1/VIRL1/*.lean` at the L1 tree
  before the rule against after, every pre-existing file byte-identical (the rule in NEW file(s)); MetaPRL, every pre-existing
  `virl1_*` module's rules and `.prla` unchanged, the rule in a new module or appended rules only. 0 on both.
  **FALSIFIED for an arm if** ≥ 1 pre-existing definition, rule or stored proof changes.
- **I2 (DERIVED, never assumed).** MetaPRL: the rule and every lemma under it are DERIVED rules (0 new prims, 0 new framework
  files), grounded under REPLAY (`status_all`). Lean: a theorem whose `#print axioms` is within propext · Classical.choice ·
  Quot.sound (predicted: none at all). **FALSIFIED for an arm if** a prim or a non-standard axiom is added.
- **I3 (Lean is cheap).** The Lean proof of the three conclusions is the recursor / a structural mutual recursion: proof text
  ≤ 40 lines (C5, the proof bodies; the STATEMENT's lines reported separately, no direction) and NO auxiliary lemma.
  **FALSIFIED if** > 40 lines or ≥ 1 auxiliary lemma. (The helm expected "one line"; the nested `List (Atom S)` of A3 and the
  depth-indexed wf are why this predicts a small block rather than one line.)
- **I4 (MetaPRL pays, in a predicted SHAPE).** The derivation has the helm's shape: a case split on the finite operator list,
  one unpacking lemma per arity SHAPE (binding depths of the operator's slots), and a slot-sort table taking the one-sorted rule
  to three sorts. Predicted: (a) the number of unpacking lemmas = the number of distinct arity shapes in L1's operator list,
  ± 0; (b) MetaPRL C5 (whitespace tokens of the rule's whole derivation, every new rule) ≥ 10 × the Lean proof's C5 tokens.
  **FALSIFIED if** (a) the count differs, or (b) the ratio is < 10. The ratio itself is the paper's figure and is reported.
- **I5 (two stages, reported).** MetaPRL's cost is reported in two stages, as the minute's honesty records: U, the per-form rule
  over ONE sort (from `lang_induction` and the operator split), and S, the three-sorted rule from U. C5 per stage, no direction.
- **I6 (extensions, reported).** The W3 premises (products, sums) and their C5, per arm, no direction.
- **I7 (it is USED — exploratory).** Each arm re-proves ONE existing L1 property by the new rule, its choice, beside the original
  proof, and both C5s are reported. No direction; not required for I1–I4.
- C1–C6 keep their amend-1..18 definitions on the addendum's files and are reported without direction.

## What would show this amendment unfair
a rule stated on either arm in a commit before this file's sha · an arm that reads the other's statement or proof before its own
lands (the statement above is the only shared text) · a count taken from a sha the arm did not name · I4(a)'s arity-shape count
taken from anything but L1's operator list at the arm's L1-closed tree.
