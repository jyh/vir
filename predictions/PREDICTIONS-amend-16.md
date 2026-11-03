# PREDICTIONS amendment 16 — layer L2, the imperative layer (OBJECT-L2)

Drafted 2026-11-02 ~19:3x PST by the 12th vir head, beside `2026-11-02-vir-OBJECT-L2-DRAFT.md` and
`2026-11-02-vir-L2-PROGRAMS-DRAFT.md`. It becomes `predictions/PREDICTIONS-amend-16.md` at the OBJECT-L2 pin (STATUS-vir
row 100), in the same commit, BEFORE either arm's first L2 file. Clauses that depend on the helm's F3/F8 word are marked [F8].

**What was known when this was drafted**, so that no prediction can claim to be blind to it: the L1 Lean arm is complete
(RESULTS-6: W1 0, W2a 3 FALSIFIED against ≥ 6, W6 fix 1 / leastness 2, adequacy built). The MetaPRL L1 arm is mid-build at
e0f16ac71 (206 grounded, 0 prims in virl1_*, PARTIALITY 27 with the M-F5 fix). FINDINGS L-F6 (router fragment): a frame rule
held there as a property of the SEMANTICS, without the type system. amend-13's W8 (conservative extension, scored AT L2)
stands unchanged and is not restated here except for its scoring.

**What was known AT THE PIN (2026-11-03, the 15th vir head), added beside the draft's paragraph above, which is kept as the
draft's own record:** the MetaPRL L1 arm is CLOSED for every required item under REPLAY (672/672 at ec912bd80 = be5312958's
theories; RESULTS-6 addendum 1: W1 0 · W2b 216 rules · W2c FALSIFIED · W5–W7 HOLD on both). W3 on L1: Lean (i) 0 · (ii) 3
(informed, FINDINGS V-F5) · (iii) 4 (blind, amend-17); MetaPRL (i) 0 / alt 2, (ii)/(iii) in progress. No L2 file exists on
either arm. The predictions below are the draft's, unchanged; **[F8] is ruled (ii) / bounds-by-logic** (council 11-03 ask 1),
so every [F8] clause is scored under (ii) and its (iii) branch is moot.

## Declarations owed by each arm before its first L2 file (posted on the bus, quoted into RESULTS-7)
the store's representation (H, R), the form of Δ and of its split, where ⊢₂ / ⟶₂ / ⟦·⟧₂ / the assertion logic live (files,
sha), and whether the triple is defined from ⟶₂ (semantic) or as an inductive proof system with a soundness theorem.

## Predictions (scored by the harness from the artifacts; each extractor added red first, before scoring)
- **Y1 (VIR-specific primitives = 0, W1 at L2).** No `prim` in a VIR L2 theory (MetaPRL), and no `axiom` / `opaque` /
  structure field standing for an L2 construct (Lean): stores, the four operations, ⟶₂, ⊢₂, the assertions and the triple are
  all DEFINED. **FALSIFIED for an arm if** ≥ 1.
- **Y2 (W8, its scoring fixed here).** The edit count is the number of L1 DEFINITIONS (Lean: declarations in `l1/VIRL1/*`;
  MetaPRL: `virl1_*` theories at the L1-closed sha) whose text differs at the arm's L2-closed sha, read by a `count.py` arm
  added red first. amend-13's prediction stands: 0 on both arms, clause 2 paid by a lemma in Lean. **[F8]: if F8 is ruled (iii)
  (an indexed `cap(n)`), Lean's `Ty` is edited by design, W8 is FALSIFIED on Lean BY THE RULING, and RESULTS-7 prints that
  cause beside the count.**
- **Y3 (the frame rule does not use the type system, L-F6 restated as a prediction).** The proof of OBJECT-L2 §5's frame rule
  mentions no ⊢₂ judgement (Lean: no `HasType₂`-family constant in the transitive proof term of the frame theorem, by `#print`
  closure; MetaPRL: no ⊢₂ rule in the frame theorem's proof tree). Linearity is used only by SEMANTIC TYPING.
  **FALSIFIED for an arm if** its frame proof uses ⊢₂.
- **Y4 (the frame rule has no side condition).** It is stated for every L2 program with no hypothesis naming a region the
  program does not touch, and is proved from ⟶₂ with ONE locality lemma per O₂ operation (4) plus L1's steps leaving σ alone.
  **FALSIFIED for an arm if** the statement carries such a hypothesis (the retired hdisj form).
- **Y5 (semantic typing holds as OBJECT-L2 §5 states it).** `Γ ; Δ ⊢₂ e : τ` implies the triple with `region(c)` per c ∈ Δ, so
  a well-typed program does not fault except out of bounds and does not leak. **[F8]: under (ii), bounds stay out of ⊢₂ and M3
  is well-typed; under (iii), M3 is ill-typed.** **FALSIFIED for an arm if** the theorem needs a bounds premise inside ⊢₂ under
  (ii), or cannot be stated without fuel.
- **Y6 (the acceptance programs agree).** On M1–M5 both arms give 7 · 5 · ⊥ (M3 faults) · ILL-TYPED (M4) · 55 with the store
  untouched (M5), with the triples the programs file names, and M2's middle store step is DERIVED by the frame rule.
  **FALSIFIED if** any value, typing verdict or triple disagrees between the arms or with the file.
- **Y7 (linear-context structure, EXPLORATORY, no direction).** Per arm: the lemmas about Δ alone (split existence, split
  commutativity/associativity, exchange, the empty context), and the C5 size of semantic typing's proof. The router fragment
  never measured a linear context, so no prior favours either arm.
- **Y8 (partiality carries over).** ⟦·⟧₂ is ONE least fixed point Φ₂ by the same logic fixpoint L1 used (Lean `Part.fix`;
  MetaPRL the bar type's fix rule at e0f16ac71 or later, M-F5), and its continuity/admissibility side condition is reported
  beside L1's W6b figure. **FALSIFIED for an arm if** ⟦·⟧₂ uses fuel or a second fixpoint mechanism.
- C1–C6 keep their amend-1..15 definitions on the L2 files and are reported without direction.

## What would show this amendment unfair
an L2 proof file on either arm with a commit time before this file's sha · OBJECT-L2 or `inputs/L2-programs.md` edited after
the pin · an arm that reads the other's L2 files · a count taken from files or a sha the arm did not name first · the two arms
given different goal-state affordances · a [F8] clause scored under a ruling other than the one the pin records.
