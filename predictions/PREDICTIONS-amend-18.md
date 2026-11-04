# PREDICTIONS amendment 18 — layer L3, the router as an L2 program (OBJECT-L3)

Drafted 2026-11-03 by the 16th vir head beside the OBJECT-L3 and L3-programs drafts; PINNED 2026-11-03 by the 17th as this file,
in the same commit as `object-L3/OBJECT-L3.md` and `inputs/L3-programs.md`, BEFORE either arm's first L3 file.
Every clause assumes G1–G4 at their recommendations; a different ruling re-drafts the clause it touches, at the pin, and says so.

**What was known when this was drafted**, so that no prediction can claim to be blind to it: the Lean L2 arm is BUILT on a
local sealed branch (counts only: 205 theorems within the standard three; Y5 closed and open, no fuel, no bounds in ⊢₂).
The MetaPRL L2 arm has not posted its declarations. No L3 file exists on either arm. virp's program-1 router (the special
language) is complete on both arms, and its `U_eq_F` holds with aborting drops (OBJECT-L3 draft G4).

**What was known AT THE PIN (2026-11-03 ~18:3x PST, the 17th vir head), added beside the draft's paragraph above, which is kept as
the draft's own record:** G1–G4 were ruled at their recommendations, so no clause below is re-drafted. The MetaPRL L2 arm posted its
declarations (d3a3f91a7, 10:53) and builds L2 on a local branch: chain 351/351 grounded at d34f8b8ce, with den2's 37 rules UNCOUNTED
until pass 5 (landed 18:02: its two prims SOUND, text amendments owed), adequacy an open design question, Y5 not begun. The Lean L2 arm
is still sealed (L2-closed sha dc95b53, 205 theorems). No L3 file exists on either arm: read by `git log --all -S'U_tx'` and
`-S'RD32'` in this repository (0 commits each; control `-S'y5_closed'` 4) and by mojave's posts (no L3 file named). Neither arm's L2 is
PUBLISHED-CLOSED; each arm's L2-closed sha is its own declaration, owed before its first L3 file.

## Declarations owed by each arm before its first L3 file
where the L3 terms live (files, sha), how the macros RD32 / EXIT / EMIT are expanded (by hand, or by a definition the arm
states), and which L2 rules each arm's L3 proofs are allowed to cite (the L2-closed sha).

## Predictions (scored by the harness from the artifacts; each extractor added red first, before scoring)
- **Z1 (L3 adds no language: W8 at L3).** No L2 definition is edited: Lean `l2/VIRL2/*`, MetaPRL `virl2_*`, diffed from the
  arm's L2-closed sha to its L3-closed sha. 0 on both. **FALSIFIED for an arm if** ≥ 1.
- **Z2 (the transport prediction does NOT recur).** The O94 paper's Lean-pays prediction was transport casts at slice_fuse.
  In L3 a slice is an int offset, with no type indexed by it, so Lean's C2 (amend-1's transport-cast count) on the L3 proof
  files is 0. **FALSIFIED if** ≥ 1. MetaPRL's C2 is reported beside it, with no direction.
- **Z3 (R2 by evaluation).** Both arms prove ⟦U⟧₂ ≠ ⟦F⟧₂ by running both terms on ONE concrete store (Lean: kernel
  evaluation of the step function; MetaPRL: reduction), citing no L2 lemma beyond the step function's soundness/adequacy.
  **FALSIFIED for an arm if** the witness proof cites a triple.
- **Z4 (R3 is the cost centre).** ⟦U_tx⟧₂ σ = ⟦F⟧₂ σ for EVERY σ is the largest single L3 proof on each arm by C5 (a case
  split on every load's fault, for an unknown store). **FALSIFIED for an arm if** another L3 theorem's C5 exceeds it.
- **Z5 (R4 from the rules, never from ⟶₂).** The router triple's proof sequences OBJECT-L2 §5's rules (the let/op rules and
  the load/store specifications) and does not unfold ⟶₂: Lean, `Step₂`/`Steps₂` tokens in the R4 proof text = 0; MetaPRL, no
  step rule in its proof tree. **FALSIFIED for an arm if** ≥ 1.
- **Z6 (R5 cites the frame rule; it is not re-proved).** The caller-frame half of R5 is one application of L2's frame rule:
  no locality lemma of an operation is cited in the R5 proof. **FALSIFIED for an arm if** one is.
- **Z7 (R6 lives in the logic).** run_tokens is an induction over the list of frames using R4, and no L3 program contains
  a `fix` (R-b). Its C5 is reported beside virp's `run_tokens` (EXPLORATORY: no direction).
- **Z8 (the refusals are cheap).** R7 is refuted by inverting ⊢₂ once; R8 is a run to the stuck configuration plus the
  IndexFault. Each ≤ 15 lines of proof on each arm. **FALSIFIED for an arm if** either exceeds it.
- **Z9 (the headline, a direction only).** Each arm's L3 proof C5 exceeds its own virp program-1 router C5: the general
  language costs more than the special one, on the same router. No ratio is predicted. **FALSIFIED for an arm if** ≤.
- C1–C6 keep their amend-1..17 definitions on the L3 files and are reported without direction.

## What would show this amendment unfair
an L3 proof file on either arm with a commit time before this file's sha · OBJECT-L3 or the L3 programs file edited after
the pin · an arm that reads the other's L3 files · a count taken from files or a sha the arm did not name first · a G-fork
clause scored under a ruling other than the one the pin records.
