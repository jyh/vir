# The driver theorem's L2 half (OBJECT-COMPILER C0 (a); STATUS-vir 304), the declarations, written BEFORE any file

Written 2026-11-12 by the 70th vir head. OBJECT-COMPILER C0 (a): *"one machine-level theorem, independent of the program and proved once,
says: if the compiled step refines the L2 step relation, then a fixed driver loop (call the step, test its exit code, jump back)
refines the iterate"*, with *"vir proving the L2 half"* (§3, paris owes (4)). This file declares the L2 half at the WORD machine (S2's
target), so it composes with paris's machine half at S3.

## DR-0, a FINDING, recorded before the route: compile_refines cannot be chained as stated
`s2_refines`/`compile_refines` clause (1) gives, at a finished run, words related to the result (`VRel`) and NOTHING about the final
memory: Sim2's `SRel.done` carries `VRel` only, while `SRel.run` carries `Layout σ lay ∧ MemRel lay σ m`. A second call of the
step needs `MemRel lay σ₁ m₁` at the first call's end, so the iterate cannot be read off the compiler as built. This is not a
defect in what is proved. The end-state clause was never stated, and the driver is the first use that needs it.

## DR-1, the end-state clause (generic; in k7/K7/Driver.lean, so compiler/ and its counts are NOT edited)
`s2_refines_mem`: under s2_refines' hypotheses, an IR run that FINISHES with v at σ' is matched by a word run that finishes with words
ws at memory m' such that `VRel T lay σ' τ v ws ∧ Layout σ' lay ∧ MemRel lay σ' m'`, or reaches OVERFLOW. Route: the IR run's last
step is a `ret` with an empty frame stack from a run state (n − 1 steps). There, s2_run gives `SRel.run`, which carries Layout and MemRel.
That `ret` leaves the store unchanged on the IR side and the memory unchanged on the word side. Then `compile_refines_mem` at the
source, as compile_refines is built from s2_refines (Compose.lean's route).

## DR-2, the L2 half of the driver (generic over step-shaped programs; names no program, K3; k7/K7/Driver.lean)
A step-shaped program is `e` with `HasType₂ [tcap] [true] e tcap` and compile_refines' side conditions. `IterRel e p k σ σ'`: k ⟶₂ runs
of `instL 0 [cap p] e`, each from the previous one's store, each returning `cap p`. `WIter`: k word runs of `lower2T [tcap] e []`,
each from the previous one's final memory, each FINISHING with the cap's two words. **`driver_l2`:** IterRel k σ σ', Layout σ lay,
MemRel lay σ m, and `σ.R.lookup p = some n` ⇒ the word machine's k chained runs from m either all finish (WIter k m m', with
`MemRel lay σ' m'`) or one of them reaches OVERFLOW. By induction on k, with DR-1 per call, and with `R` carried
(compile_refines' VRel at `cap p` returns the same two words, `lay p` and n, so the next call starts from the same ρw₀).
- **What stays a premise:** the regions do not change across calls (`σ.R` is preserved, which L-2's `run_shape` gives for no-alloc
  programs). Stated as a hypothesis on IterRel if it is not derivable generically.
- **What would show it wrong:** DR-1 needing an edit of Sim2 (a run state that reaches done other than by a frame-less `ret`, a
  finding about Sim2's semantics); the next call's ρw₀ differing from the cap's words returned (then the driver loop must re-pack the
  capability, and the machine half must say so); a premise naming a program.

## Addendum 1 (same head, after DR-1 and DR-2 PROVED in k7/K7/Driver.lean): the K3 homing owed
DR-2 needs no "regions preserved" premise: the returned capability's `VRel.cap` gives the next call's EnvRel. Under K3's whitelist
(DECLARATIONS-S1.md l.46–50), read by the derived-namespace k3_check, `driver_l2` names `K7.IterRel`/`K7.WDone`. These are generic
definitions, but they sit in a namespace the whitelist does not admit. At S3 the driver theorem is assembled from them, so they
(and `compile_refines_mem`) move to compiler/ under VIRC, declared first in DECLARATIONS-S2's "Added" list. Until then, K3 is not
scored on them.

## Addendum 2 (same head, BEFORE its file): DR-3, DEFLATE's iteration through the driver's L2 half (STATUS-vir 305)
- **Statement.** `deflate_driver` (k7/K7/DeflateDriver.lean): for bytes < 256, n and OUTMAX < 2³², either reading, the region placed
  at 0 ≤ p with p + L0 ≤ 2⁶⁰, and every k and σ with `iterS p k (initStore b om lit p) = some σ`: the compiled step, run k times
  from the scaled loader's image of the initial store (`scaleMem (initStore …)`, argument words `capWords scaleLay p L0`), each run
  fed the previous run's returned words, FINISHES all k times (`WDone`), and the final memory is related to σ (`MemRel scaleLay σ m'`).
  No overflow branch, and the hypotheses are those of `deflate_noovf_loaded`.
- **Route.** Induction on k through `iterS_succ'`, carrying `WDone`, `MemRel` and the EnvRel of the next argument words. Per step:
  `compile_refines_mem` at the reached σ_k (from the source run that `stepS` packs, returning `cap p`). Its overflow branch is
  excluded by `deflate_noovf` at σ_k, whose argument words are `capWords scaleLay p L0` because the returned cap's VRel gives
  σ_k's region length and `reach_shape` gives `σ_k.R = {p ↦ L0}`. A `WDone.snoc` lemma appends the new call.
- **What would show it wrong:** a reached σ_k whose returned words are not `capWords scaleLay p L0` (the region changed: a finding
  against reach_shape); an overflow branch that deflate_noovf does not exclude (a gap between K5's statement and the driver).

## Addendum 3 (same head): the homing of Addendum 1 DONE
Moved to compiler/VIRC/Driver.lean (DECLARATIONS-S2 "Added", 81bd82c), statements unchanged; under the derived-namespace k3_check, `VIRC.driver_l2` and `VIRC.compile_refines_mem` read OK (k7/logs/k7-probe-K3-002.log).
