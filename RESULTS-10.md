# RESULTS-10 — layer L4, concurrency with locks (O95; OBJECT-L4 at vir e80bd25; amend-21; errata L4-E1, L4-E2, L4-E3)

**DRAFT, the Lean column only, written on the SEALED branch `l4-lean` (2026-11-06, the 27th vir head).** Nothing here is public
until the MetaPRL arm posts its L4 declarations (the pace rule (C), as at L3). The C5/W8 counts that Q1, Q3, Q4 and Q5 read are NOT
in this draft: they are row 166's harness arm (`count.py --arm l4`), built red first at the unseal. Every figure below is a theorem
name, a commit, or an `EXIT=` line in `l4/logs/`.

## The declarations, written before the files they govern
| file | content | commit |
|---|---|---|
| `l4/DECLARATIONS-LEAN.md` | the arm's L4 plan (fresh Tm₄; ⟶₄ a relation; the triple as Vafeiadis safety; the rows and their files) | bddbd40 |
| addendum 1 | erratum L4-E1: `par` binds its two results | (before Typing4) |
| addendum 2 | `I` keyed by region BASE; Shared / Ext / Assn₄ / safe₄ named | 5cba66f |
| addendum 3 | Q6's typed configuration; scope = typed configurations; preservation OWED | e32b22e |
| addendum 4 | N4 in Router4.lean; N4-S with ∃ t and I_b | 015171e |
| addendum 5 | N4-V at the join configuration; EmitsT; the closing compile NT₄.cc | c74651c |
| addendum 6 | Q6 preservation: the typed configuration and the moves of Ω | dc8c45c |
The file at dc8c45c reads sha256/16 `29428abea87a9007`.

## The rows (inputs/L4-programs.md §3), Lean
| row | theorem(s) | file |
|---|---|---|
| N1-T | `N1_typed` | Programs.lean |
| N1-V | `N1_V` — every terminating run of N1 returns 2 (invariant `R1` over ⟶₄*) | Values.lean |
| N1-S | `N1_S` — `{emp} N1 {v. v ∈ ℤ}` under I₁ | Programs.lean |
| N2 | `N2_untyped` — no ⊢₄ typing (Δ cannot give one capability to both `par` sides) | Programs.lean |
| N3 | `N3_typed` · `N3_no_triple` (via `triple₄_invariant`; the release's precondition is the counterexample) | Programs.lean |
| N4-T | `F₄_typed` · `N4_typed` | Router4.lean |
| N4-S | `F₄_S` — each side keeps ℓb's invariant (every bucket ≥ 0) and returns its world as `postF₄ f p t` for the token t it read | Router4.lean |
| N4-V | `N4_V` — at every ⟶₄*-reachable configuration whose two `par` sides are `ret`, each world holds `postF₄` for its thread's token and, for every sender s, the emits naming s across both threads are ≤ g₀(q + s) | RouterV.lean |
| CE | `ce_fwd` · `ce_bwd` (both directions on ⟶ through ι) · `ce_pure` | CE.lean |

## The predictions (amend-21 Q1–Q8), Lean
| | prediction | Lean | verdict |
|---|---|---|---|
| Q1 | L1–L3 untouched (W8) | owed to row 166 | — |
| Q2 | no new axiom | `audit-018`: 157 theorems, every one within propext · Classical.choice · Quot.sound; 3 depend on none | HOLDS |
| Q3 | `par₄_rule` C5 ≤ 3 × L2 `frame` C5 | `par₄_rule` is proved from ⟶₄ (Rules4.lean, via `safe₄_par`), no side condition naming a region; C5 owed to row 166 | — |
| Q4 | C5(N1-V + N4-V) > C5(N1-S + N4-S) | owed to row 166 (Values.lean + RouterV.lean against the N1-S and F₄_S proofs) | — |
| Q5 | MetaPRL wf rate | Lean: no analogue (0) | — |
| Q6 | a typed configuration has no race, nothing assumed beyond ⊢₄ | `Q6_no_race` (typed configurations, 17ea0e6) and, stronger, `Q6_typed_program`: a closed ⊢₄-typed program, from the empty store and lock table, has no race at ANY ⟶₄*-reachable configuration (`pres₄`, Preserve4.lean); control `N1_no_race` | HOLDS |
| Q7 | CE both directions | `ce_fwd` · `ce_bwd` | HOLDS; C5 owed to row 166 |
| Q8 | one deadlocking program with `{emp} e {_. False}` | `D_triple_false` · `D_blocks` (it reaches `Blocked₄`, never a fault) | reported |

## Red backwards (a mutant that restores the defect, the arm firing where it should)
| mutant | what it restores | where it is red |
|---|---|---|
| 001–005 | (the 26th head's; listed in their commits) | each at its intended obligation |
| 006 | VOID: no decrement, but it stopped at `F₄_S` and never reached N4-V; declared in its commit, not counted | — |
| 007 | the bucket store writes t, not t − 1 (F₄_S stubbed so the build reaches N4-V) | `th_step`'s decrement clause, nowhere else |
| 008 | RT₄'s acquire gives the continuation its capability WITHOUT ownership | `pres₄`'s acquire case and `rt_of`'s acquire case, nowhere else |

## What the Lean arm found, for the paper
- **The value claims need the thread's PROGRESS, not only the shared state.** N4-V's invariant names each thread's stage (a suffix of
  F₄ under the values its lets have bound), whether it has decremented, and the token it read; region invariants alone (N4-S) cannot
  say how many emits there were, which is H5's own finding, now proved on both programs.
- **Naming a thread's stages cost a compiler, not a list.** The stages are `NT₄.cc ρ [] S` for a suffix S of F₄ and ONE expected
  environment ρ per thread: a step binds the value ρ already holds, so the stage's term never changes shape. The substitution lemma
  (`NT₄.cc_subst`) is the one place de Bruijn indices are touched.
- **Preservation at L4 is L2's frame-form preservation with the lock table as part of the frame.** The free locks' regions are a
  shared part (`Shared` with the trivial invariant); acquire moves a region from it into the thread's Ω, release and newlock move
  one back. The same `Shared` serves the triple (Safe.lean) and preservation.

## Limits
- N4-V is stated at the configuration the join steps from (both sides `ret`): the last at which both worlds are allocated. Every
  terminating run passes through one; a run that never reaches it is not described by N4-V (whether one exists is a liveness
  question, outside partial correctness, Q8's point).
- Q6's "no race" is by region BASE (two threads' enabled accesses through one ⟨p⟩); a cell-level race across two bases is excluded by
  the store's well-formedness and is not restated (addendum 3).
- The adequacy of the triple (`triple₄_adequate`) is the object's reading of a triple; the triple itself is the thread-local
  safety predicate (addendum 2's reason).
- Mutant 007 stubbed `F₄_S` to reach N4-V; mutant 008 adjusted the two structural lemmas' acquire lines to the mutated rule. Both
  are declared in their commits; neither edit survives (files restored by copy, the next build EXIT=0).
