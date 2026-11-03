# L2, the Lean arm: where it stands (OBJECT-L2 at vir dec0cdd; amend-16; erratum L2-E1)

Every build went through the fleet's `saltbuild` via `l2/logged-build.sh`, one log per run in `l2/logs/`, and is judged only by
its `saltbuild EXIT=N` line. The declarations (`DECLARATIONS-LEAN.md`) were committed at 161a6fc, before any `.lean` file here.
L1 is imported by path and never edited: `count.py --arm w8 --base 37c209e --ext <tip> --prefix l1/VIRL1` reads W8.defsEdited 0.
Figures below are rows of `count.py --arm l2 l2` at this file's commit, or are labelled otherwise.

## Built (each item names its file; all in `VIRL2/`)
| OBJECT-L2 | what | where |
|---|---|---|
| §1 Σ₂ | an INSTANCE of L1's `Sig`/`ESig`; P₂ = P₁ through L1's own `Prim.interp`; `lawful` | `Sig2` |
| §2 stores, faults | σ = (H, R) as two `Finmap`s; alloc/load/store/free as partial functions (`none` = fault); `Store.WF` | `Store` |
| §3 ⟶₂ | L1's `Step` lifted VERBATIM (`pure`), a configuration context rule, one `op` rule; `stepFn₂` sound | `Step2` |
| §4 ⊢₂ | a usage mask Δ over Γ, a pointwise split; λ/fix bodies under ⊢₂ with Δ = ∅; capability-free atoms | `Typing2` |
| §5 logic | fragments, ∗, the SEMANTIC triple (no fault + post + the store stays well-formed); **the frame rule for every L2 program, 2 explicit binders (R, the triple), no side condition**; consequence | `Logic` |
| §5 small axioms | alloc, load, store, free (op triples by Finmap locality); the `let x ← o(a⃗)` rule | `Axioms` |
| §5 structural | `ret`, `let`, a deterministic pure head step | `Rules` |
| §5 for programs | region-level load/store/free with contents; the frame rule for ONE operation (`op_frame`); ∃/pure preconditions | `Regions` |
| §6 meaning | ⟦·⟧₂ = `Part.fix Φ₂` (L1.fix's form with a store), continuity, unfolding, soundness of ⟶₂, a fault is ⊥ | `Denot2` |
| §6 adequacy | (v, σ′) ∈ ⟦e⟧₂ σ iff ⟨e, σ⟩ ⟶₂* ⟨ret a, σ′⟩ with ⟨a⟩ = v (L1's `head_go_step` reused) | `Adequacy2` |
| §7 = OBJECT-L1 §8 | ι : Σ₁ → Σ₂; clause 1 (typing), clause 2 (steps ⟺, store untouched), clause 3 (⟦ι e⟧₂ σ = ⟦e⟧₁ ≫= (c ↦ (ι c, σ))) | `Conservative` |
| §8 M1–M4 | runs, typings (M4 REFUTED), triples (M2's `store(b,0,9)` by `op_frame`), M3 has NO triple, M4's leak, meanings | `Programs`, `Triples`, `Meanings` |
| §8 M5 | ι K5: typed, ⟦K5⟧₂ σ = (55, σ) for EVERY σ, `{P} K5 {v. v = 55 ∗ P}` for EVERY P | `M5` |
| §5 erratum | the semantic-typing FORMULA read with §5's no-fault triple is false (`semantic_typing_literal_false`, from M3) | `Triples`, errata/ERRATA-L2.md |

## The amend-16 rows, as the harness reads them now (PROVISIONAL: the L2-closed sha is not yet named)
Y1 `L2.C4vir` 0 · Y2/W8 `W8.defsEdited` 0 · Y3 `L2.Y3.frame` 0 and `L2.Y3.op_frame` 0 with `L2.Y3.control` 1 (closure-003) ·
Y4 `L2.Y4.frameExplicitBinders` 2 · Y6 `L2.Y6.theorems` 16 of 16 · Y7 `L2.Y7.maskLemmas` 4 (EXPLORATORY) · Y8 `L2.fix` 1,
`L2.continuity` 1 · audit `L2.audit` 126 rows, `L2.C4` 0, control 1 (audit-003, audit-control-001) · C6 `L2.C6` 54.
**Y5 (semantic typing) is NOT BUILT.** It is scored against L2-E1's bounds-tolerant triple.

## Limits, riding with the rows
- **Y3 measured a closure, and the closure's first form was blind to proofs.** `ConstantInfo.value?` skips theorems, so
  `closure-001` followed statements only (its M1_typed control read 1). Caught by that control; the fixed form follows theorem
  values, and a control whose STATEMENT is `True` while its PROOF uses ⊢₂ reads 9 (the old form, `mutants/ClosureValueQ.lean`,
  reads it 0: mutant-001). The harness refuses a Y3 row unless that proof control reads > 0 in the same log (ARM35).
- **Y4's binder count reads the statement's explicit `( … : … )` groups**; implicit `{P} {e} {Q}` are the rule's metavariables.
- **The frame rule is cheap here BY CONSTRUCTION of the triple**: the triple quantifies over every disjoint frame, so the frame
  rule is a re-association. The locality work sits in the four small axioms (Y4's "one locality lemma per operation" lives
  there, not in the frame theorem). A reader comparing arms should compare the frame theorem AND the axioms.
- **`stepFn_complete` (any Σ) is proved in L2**, not in L1, so W8 stays 0; it is L1-shaped and counted as an L2 theorem.
- The region-level `load_at`/`store_at` are specifications on a WHOLE-region fragment; the cell-level small axioms
  (`load_axiom`, `store_axiom`) are proved beside them, and the programs use the region-level ones.
