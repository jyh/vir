# Preregistered predictions (O95, STATUS-vir row 2)

Pinned BEFORE either arm's first proof. At the commit that adds this file, no `lean/` or `metaprl/` proof exists in any tree: vir's Lean arm is not started, and mojave posted "waiting on vir's freeze" (@[bus]).
After this sha is posted, this file is never edited. A change is a new file `PREDICTIONS-amend-<n>.md`, dated, and it says that it was written after which proofs.

Object: `object/` @ vir cd64c9fd. Inputs: `inputs/router-inputs.md` (same commit as this file). Goal: I4 (`U ≡ F`).

## Conflict of interest, declared
vir writes these predictions AND builds the Lean arm. To bound that, the Lean arm's REPRESENTATION is fixed here, before the first proof:
- **L-IDX (the arm the paper's claim is about, §5.2):** slices are length-indexed, `Slice (n : Nat)`, and `advance` has type `Slice n → (i : Nat) → i ≤ n → Slice (n - i)`. `ValidFrame` is the Prop-carrying subtype of §5.1 Exhibit A.1.
- **L-FLAT (control, built second):** slices are an unindexed structure `{buf : ByteArray, off len : Nat}` with the bound as a separate hypothesis.
Both are counted. The headline Lean figure is L-IDX. If only one gets built, the file says which, and P1 is scored on L-IDX only.

## The counts (each is defined by the harness from the artifacts alone, row 3; the definitions are fixed here)
| id | count | Lean extractor | MetaPRL extractor |
|---|---|---|---|
| C1 | TRANSPORT CASTS in proofs | occurrences of `HEq` · `cast` · `▸` · `Eq.mpr` · `Eq.rec` · `heq_of_eq` · `eq_rec` · `Nat.sub_sub` used for index realignment, in the proof terms of the theorems on the path to I4. Measured on the elaborated term (`#print` output), not on the source, so tactics that hide a cast still count | the same token class in the replayed proof (expected structurally 0, because CTT has no casts) |
| C2 | WELL-FORMEDNESS OBLIGATIONS | goals whose target is a typing or membership side condition the elaborator did NOT discharge (`_ ∈ _`, `_ < _` index bounds, `Decidable`, coercion side goals), counted as tactic-closed side goals | proof-tree nodes labelled `wf` (or MetaPRL's equivalent typing-subgoal label, matched as mojave's census prints it) |
| C3 | AUX RULES | stated lemmas outside the 7 GIVEN rules (I5) that the path to I4 uses | the same, as declared rewrites/rules in the theory module |
| C4 | AXIOMS beyond the logic | `#print axioms` beyond propext · Classical.choice · Quot.sound (expected 0 by build law), plus VIR rules taken as axioms | rules declared without a proof (`prim` / unproven) |
| C5 | SIZE | proof-script lines and tokens on the path to I4 (exploratory: no direction predicted) | the same |
| C6 | AGENT ITERATIONS | build/check invocations until the first green on I4 (`saltbuild` runs) | `mp -batch` replays plus driver `refine` steps |

## The predictions (directional, with the threshold that scores them)
- **P1, Lean pays at slice_fuse.** C1 on the L-IDX proof of `slice_fuse` (as used in I4) is ≥ 1. C1 for MetaPRL is 0. **FALSIFIED if** L-IDX proves slice_fuse and I4 with C1 = 0.
- **P1b, the gap is a representation choice.** C1 on L-FLAT is 0. **FALSIFIED if** L-FLAT needs a cast (C1 ≥ 1).
- **P2, CTT pays in well-formedness.** MetaPRL C2 over the I4 path is ≥ the number of guard/advance rule applications in that path (at least one wf goal per subset-typed rewrite). Lean C2 (L-IDX) is strictly lower. **FALSIFIED if** MetaPRL C2 ≤ Lean C2.
- **P3, the object under-states its rules.** Both arms have C3 ≥ 3 (E8: commutation of advance/read_u32/guard/let_lin, and the ACL-before-rate-limit reorder). **FALSIFIED for an arm if** its C3 ≤ 2.
- **P4, the trusted base is equal.** C4 = 0 on the Lean arm, and every MetaPRL VIR rule is derived or counted. Exploratory on the MetaPRL side.
- **P5 (paris's spike, A.4).** If E2 and E3 are kept as written, the refinement check FAILS on them: the signed test for len ≥ 2^63, and the rate-limited exit with the state changed. **FALSIFIED if** a refinement proof goes through with E2 or E3 as written.
- C5, C6: no direction. Reported as measured.

## What would show the comparison unfair (scored before any verdict)
an arm that read the other's proofs · an input given to one arm only · a prediction amended after a first proof without saying so · a count the harness cannot reproduce from the artifacts.
