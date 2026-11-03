# RESULTS-7 — layer L2, the imperative core (O95; OBJECT-L2 at vir dec0cdd; amend-16; errata L2-E1, L2-E2)

**DRAFT on the local branch l2-lean; the Lean column only.** Every Lean figure is a row of `l2/out/counts-l2.tsv`
(`harness/count.py --arm l2 l2`, re-derived by `harness/reproduce.sh` at that file's own commit, rc 0) or of
`l2/out/counts-w8.tsv`, or is labelled as something else. The two arms' declarations (amend-16) are quoted here when the
branch is unsealed (STATUS-vir 121); the MetaPRL column is scored when that arm posts L2 closed (STATUS-vir 122).
The Lean L2-closed sha is **dc95b53** (l2-lean).

## The scoreboard (amend-16 Y1–Y8)
| prediction | Lean (l2/) | MetaPRL (mojave) | verdict |
|---|---|---|---|
| Y1 C4vir = 0 | **0** (`L2.C4vir`); axioms beyond the standard three **0** (`L2.C4`, `L2.audit` 205 rows, control 1) | owed | Lean HOLDS |
| Y2 W8 = 0 | **0** (`W8.defsEdited`, base 37c209e, ext dc95b53; `W8.thmEdited` 0, `W8.newFiles` 0 beside) | owed | Lean HOLDS |
| Y3 the frame proof uses no ⊢₂ | `L2.Y3.frame` **0**, `L2.Y3.op_frame` **0**, with the proof control live (`L2.Y3.control` 1: closure-004, typing2 9) | owed | Lean HOLDS |
| Y4 no side condition | **2** explicit binder groups (`L2.Y4.frameExplicitBinders`: R and the triple). Locality is in the four small axioms, one per operation, not in the frame theorem (STAGE limit) | owed | Lean HOLDS |
| Y5 semantic typing as §5 states it, read with L2-E1 + L2-E2 | `L2.Y5.closed` **1** · `L2.Y5.open` **1** · fuel in their statements **0** · bound premises in ⊢₂ **0** (3 inductives); M3 stays TYPED. Red backwards: `mutant-002` (no-fault triple) EXIT=1, one error, at the IndexFault branch | owed | Lean HOLDS |
| Y6 M1–M5 agree | **16 of 16** acceptance theorems (`L2.Y6.theorems`): 7 · 5 · ⊥ · ILL-TYPED · 55 | owed | agreement owed |
| Y7 linear-context structure (EXPLORATORY) | mask lemmas **21** (`L2.Y7.maskLemmas`); semantic typing's C5 **1092** lines / **13155** tokens over its 9 route files | owed | reported |
| Y8 one least fixed point | `L2.fix` **1**, `L2.continuity` **1**; no fuel | owed | Lean HOLDS |

C6 for the Lean arm: **79** logged saltbuild runs (`L2.C6`; one log each: 67 builds · 4 audits · 1 audit control · 4 closures · 2 mutants · 1 scratch).
Binder lemmas (`L2.binder`, the leanp binder row on VIRL2/): **13**.

## The literal §5 formula
OBJECT-L2 §5's semantic-typing statement, read with §5's NO-FAULT triple, is false, twice, in Lean:
`semantic_typing_literal_false` (M3, an out-of-bounds load that is typed) and `A0_typed` + `A0_faults` (alloc(0)). Errata
L2-E1 and L2-E2 permit exactly the INDEX faults, and Y5 is scored against that reading on both arms.

## Limits
- Y4's binder count reads the frame theorem's explicit `( … : … )` groups; its implicit `{P} {e} {Q}` are metavariables.
- The frame rule is cheap by construction of the semantic triple (it quantifies over every frame); a reader comparing arms
  compares the frame theorem AND the four small axioms.
- Y5's open form closes Γ ; Δ by substitution (`Binds`): each available capability is bound to some ⟨p⟩ owning region(p).
  The `fuel` and `bounds` rows are token counts over two statements and three inductive blocks; they can miss a premise
  spelled otherwise, and they say nothing about a premise hidden in a definition the statement names.
- Y7's C5 counts whole files, lemmas used elsewhere included.
