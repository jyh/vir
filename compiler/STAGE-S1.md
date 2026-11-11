# Compiler S1: L2 → block IR, PROVED (2026-11-11, 61st vir head)

**Theorem `VIRC.s1_refines`** (`VIRC/S1.lean`). `#print axioms` gives propext · Classical.choice · Quot.sound
(`logs/s1-audit-002.log`, `saltbuild EXIT=0`). The `sorryAx` control is red (`logs/s1-audit-control-001.log`).

For every term e with `Fragment.ok e = true` (C2's checked predicate) and every store σ:
- `compileS1 e = some (lowerT e)`;
- a ⟶₂ run from (e, σ) to (`ret a`, σ′) with ⟨a⟩ = w is matched by an IR run to `done (valOf w)` with the **same** store σ′;
- a ⟶₂ run to a configuration that FAULTS is matched by an IR run to a `run` state with no step, which is the IR's one fault
  state;
- an n-step ⟶₂ run is matched by an IR run of ≥ n steps, so divergence is preserved.

`c2_rejects_open_lam` and `c2_accepts_closed_lam` show the predicate deciding by evaluation (`decide`). A λ that captures a
variable is rejected.

## How it is proved (one paragraph)
`TRel n vs c e` relates IR code to an L2 term. The term carries the environment's values `vs` substituted in, and its n
innermost binders are still variables. `TRel.subst` is the one fact ⟶₂'s substitution needs: substituting the outermost local
moves it into the environment. A call to `fix` uses it twice, through a commutation lemma (`Tm.subst_comm`). `Match` adds the
frame stack: the IR's frames are ⟶₂'s `let` contexts (`plug`). `normalize` pushes frames, and these pushes are steps that
⟶₂ does not take (stutters). `sim_step` matches each ⟶₂ step with ≥ 1 IR step. `match_fault` shows that a stuck IR state
would otherwise contradict the fault. C2 is used in exactly one place: a closed function atom is unchanged by substitution
(`Tm.subst_wfB`), so its code is its whole value.

## The predictions it scores (amend-23 §K)
- **K1, FALSIFIED (low).** The prediction was 40 < S1 ≤ 80. By the declared rule (`DECLARATIONS-S1.md`: every `s1-*` log from
  the first S1 file to the first `EXIT=0` audit printing `s1_refines`), S1 is **9**: `s1-001` … `s1-008` and `s1-audit-001`.
  All `s1-*` logs together are **13**. That adds the control, one mutant, one rebuild for the C2 witnesses and their audit.
  Both figures are under the plan's 40-build guess. The plan's §4 checkpoint therefore does not trigger, and C1's fallback is
  not considered for S2/S3.
- **K2, HOLDS for S1.** S1 is one ∀-program theorem, not per-output.

## A mutant, red (the theorem is load-bearing)
`mutants/Lower-ite-swap.lean` lowers `ite` with its branches swapped. Built in place of `VIRC/Lower.lean`, it gives
`logs/s1-mutant-ite-swap.log` `saltbuild EXIT=1`, at `lowerT_rel` (VIRC/Sim.lean). The original was restored, and `s1-009`
rebuilt it green.

## Limits (they ride with the verdict)
- **The converse is PROVED (`VIRC.s1_converse`, `VIRC/Converse.lean`, `logs/s1c-audit-001.log`, standard axioms).** Every IR run
  of `lowerT e` that FINISHES at `done v` with store σ′ is matched by a ⟶₂ run to `ret a` with ⟨a⟩ = w, `valOf w = v` and the same
  σ′. It rests on `step₂_det` (⟶₂ is deterministic, proved here from L1's `stepFn_complete`; L2 is not edited) and on the IR being
  a function. Its builds are `s1c-*`: 2 builds and 1 audit, reported BESIDE K1 and never folded into it.
- **A finding against this arm's own declaration.** `DECLARATIONS-S1.md` says that logs after `s1-audit-001` are named `s2-*`.
  Four were named `s1-*` instead: the control, the mutant, `s1-009` (the C2 witnesses) and `s1-audit-002`. That is why K1 is
  reported as 9 (the declared window) with 13 beside it, and not as one figure.
- IR values are still L2 values (`valOf`), not words. The 64-bit gap and fork C4 belong to S2.
- Typing plays no part. The theorem holds for every closed C2 term, typed or not. A "finished" run is one ending in
  `ret a`, and the clause asks that a evaluate. For ⊢₂-typed programs that is L2's safety theorem, not S1's.
- The fault clause says the IR reaches a stuck `run` state. It does not say WHICH fault. S2 maps every stuck state to the one
  fault exit.
