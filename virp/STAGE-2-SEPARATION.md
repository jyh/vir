# VIR program, Lean arm — stage 2: the semantic reading of linearity (the separation model)

O95, council 2026-11-02 §C point 4: *"linear types denote resource predicates over owned store fragments under a separation
algebra … soundness = the frame rule; this retires the hdisj trap."* The carrier and the theorem were fixed FIRST as a shared
input for both arms, `inputs/vir-program-inputs.md` S1–S5, merged at vir 5591d8b before this file existed. The MetaPRL arm
builds the same statement and neither arm reads the other's model.

## The file: `virp/VIRP/Sep.lean`, rule by rule
| input | Lean | what it says |
|---|---|---|
| S1 | `Loc` (wire i · bucket p, `DecidableEq`), `Frag := Loc → Option Int`, `emp`, `Disj`, `union` | locations, partial fragments, # and ⊎ |
| S2 | `union_emp` · `emp_union` · `union_comm` (under #) · `union_assoc` · `disj_union` | the algebra's laws, each a THEOREM |
| S3 | `Store.read`, `ownsTok p`, `ownsSlice o n`, `own σ`, `own_split` | a token at sender p owns {bucket p}; a slice owns wire(o..n); F's footprint is exactly their union |
| S4 | `F_effect`, **`frame_F`** | ⟦F⟧ leaves the store alone or decrements the sender's one cell. **Any fragment disjoint from F's footprint keeps every value.** |

**Why this retires the hdisj trap at the abstract side.** At the machine, the old premise excluded the whole bucket array
from the buffer. paris narrowed it at spike d7e992c to the current sender's cell, and has now DERIVED it from one placement
(paris/o95-layout). `frame_F` is the abstract statement of the narrowed form: its only premise is disjointness from what F
actually touches, and that is a property of the meaning, not a hypothesis on the program.

## What was checked
- `virp/logs/build-014.log`: `saltbuild EXIT=0`. `audit-004`: 28 theorems, each a subset of {propext, Classical.choice,
  Quot.sound}, with no `sorryAx`.
- **Mutant `mutant-005-framenodisj` is RED:** the same theorem WITHOUT the disjointness premise ("every location unchanged")
  stops at the bucket case, where the emit path decrements the sender's cell. So the premise is load-bearing.
- S5 counts (EXPLORATORY, harness `count.py --arm leanp`, ARM22 fixture): `P.sep.theorems` 8 · `P.sep.laws` 5. The maps
  are hand-built, not taken from a mathlib structure, so all 8 are VIR-side under amend-12.

## Limits
- S4 is proved for the router's F, as the input states it. A frame rule for EVERY well-typed program (from `HasType`) is the
  general form, and it is not built here.
- The ACL is shared and unowned (S1). An arm that owns it states something else.
