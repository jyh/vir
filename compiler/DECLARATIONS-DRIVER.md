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

## Addendum 4 (2026-11-15, the 79th head, BEFORE its file): the driver at the x86 machine (C0 (a) whole; K3 scored on it)
- **The loop (machine code, fixed, generic in the step):** at H: `call rel (base − …)` (5 bytes; it pushes ret0 = H + 5 at rsp0,
  which is DriverCall's `ret`); at ret0: `mov rax, [rbx+0]` (STATUS), `test rax, rax`, `jne X` (any status but DONE leaves the loop),
  then `mov r12, env0` (an immediate: the loop is generated for the layout) and the returned capability's two words are copied
  BUF → ENV (`mov rcx, [r14+0]; mov [r12+0], rcx; mov rcx, [r14+8]; mov [r12+8], rcx`), then `jmp H`. Its instructions are ⊆ K4's
  emitted set. *(Amended by its author before the file: the first text relied on the stub's `pop r12`, but R3's `Returned` does not
  carry r12, so the loop sets it.)*
- **Statement `driver_x86`** (s3/S3/Driver3.lean, namespace S3): for a step-shaped e (`[tcap] ⊢ e : tcap` + the compiler's side
  conditions, as `driver_l2`), k chained ⟶₂ runs `IterRel e p k σ σ'` from a store related to the start memory, S3's premises for
  `lower3` of e at base, the loop at H in the same program, and a machine state at H whose post-call state is `DriverCall`: either
  the machine reaches H again after the k-th iteration with the next DriverCall (memory related to σ'), or some iteration i ≤ k
  leaves the loop at X with STATUS ∈ {FAULT, OVF, RES} (OVF from S2's int range, RES with `ResWhy`). Names no program.
- **Route.** One iteration = the call's effect (one `stepP`) → `compile_x86` clause (1) at the reached store (it ends `Returned`
  at ret0) → the check block → the copy block → `jmp`. paris's `driver_iteration` / `call_ret` (X86/Effects.lean at 4f08f91) are
  used if their shape fits S3's `Returned`; if the direct composition is shorter, the record says which was used and why.
  Induction on k as in `driver_l2`.
- **Premises that are new here, all about the driver's own code and layout:** the loop's bytes at H (CodeAt), canonical H and X,
  `L.ret0 = H + 5`, ENV ≥ 2 words at env0, BUF ≥ 2 words, and the loop's memory writes (ENV words 0–1) lying outside L.live.
- **K3** is read on `driver_x86`'s statement by `k5/tools/k3_check.py` (derived whitelist), with router_refines as the positive
  control. **What would show it wrong:** a premise that names e's structure; an iteration whose returned words are not the next
  call's DriverCall words (the copy block misread); a write of the loop that lands in L.live.

## Addendum 5 (2026-11-15, the 79th head, WRITTEN AFTER driver_x86 was proved; it records one premise Addendum 4 did not list)
- `driver_x86` takes **L.live ⊇ Live σ'' lay for every store σ'' an `IterRel` prefix reaches from σ** (stated over `VIRC.IterRel`,
  generic). Addendum 4 listed only the driver's own code/layout premises. The premise is there because S3's run theorem takes
  L.live ⊇ the START store's live cells at each call, and no source-level lemma here shows a ⟶₂ run of an accepted program keeps
  σ.R (the IR has it, `stepIR_R`; the source does not yet). Removing it needs that lemma; it is not claimed.
- The loop's ENV demand is stated as `env0 + 16 ≤ envTop` and its BUF demand as `2 ≤ |BUF|` (the capability's two words), as
  Addendum 4 said.

## Addendum 6 (2026-11-15, the 79th head, BEFORE its code): removing Addendum 5's premise (STATUS-vir 354)
- **`s2_run_R`** (s3/S3/SrcR.lean): `VIRC.s2_run` with `I'.2.R = I.2.R` added to its SRel branch (each IR step keeps σ.R by
  `stepIR_R`, its NoAF from the SRel at that step, `noAF_of_srel`). **`compile_refines_mem_R`**: `compile_refines_mem` with
  `σ'.R = σ.R` added to its FINISH branch (the IR's final store is the source's, `stepIR_done_store`).
- **`driver_x86_R`** (same file): `driver_x86` with the premise replaced by L.live ⊇ Live σ lay at the START store only; the
  iteration carries it by `live_of_R`. `driver_x86` stays as proved; nothing proved is edited.
- **What would show it wrong:** an IR step of an accepted program that changes σ.R (stepIR_R's NoAF not available from SRel at
  some step); the finish branch's final store not being the IR's.

## Addendum 7 (2026-11-15, the 80th head, BEFORE k7/K7/DeflateX86.lean): DEFLATE at the x86 machine (STATUS-vir 369)
- **`iterS_iterRel`:** `iterS p k σ = some σ'` ⇒ `IterRel stepT p k σ σ'` (both recurse at the front; each step by `stepS_steps_p`).
- **`deflate_x86`:** `driver_x86_R` instantiated at e = stepT, lay = scaleLay, from the loader's image of `initStore b om lit p`
  (Layout and MemRel by `deflate_noovf_loaded` at k = 0; EnvRel by `K5.envRel_cap`), under DEFLATE's own premises (bytes < 256,
  n, OUTMAX < 2³², 0 ≤ p, p + L0 ≤ 2⁶⁰) and the driver's S3 premises on `lower3` of stepT, which stay PREMISES here (needW, code
  size, table length, layout, loop code at H), with L.live covering the START store's live cells. Conclusion, for every k with
  `iterS p k (initStore …) = some σ`: the machine reaches the loop head again with memory related to σ, OR some iteration leaves the
  loop at X with a non-DONE status.
- **Declared limit:** the second disjunct is NOT excluded here. `driver_x86_R` does not say WHICH non-DONE status, so DEFLATE's
  no-OVF (`deflate_noovf`, at S2) cannot be applied through it; RES is not excluded generically either (stepT's table is not empty,
  so `resWhy_false` does not apply). Excluding OVF at the machine needs a driver variant carrying a per-iteration no-OVF premise:
  queued as its own item, not claimed here.
- **Going red:** start the iteration from a store the loader did not produce (drop `initStore`'s EnvRel), and the instantiation must
  fail to close.

## Addendum 8 (2026-11-15, the 80th head, BEFORE s3/S3/DriverN.lean and k7/K7/DeflateX86N.lean): OVF excluded at the machine (STATUS-vir 371)
- **`S3.drv_iter_N` (new file s3/S3/DriverN.lean; no existing s3 file edited):** `drv_iter_R` with one more premise, SrcInRange of
  the iteration's source run, and a narrower exit: the machine reaches the head again (EnvRel, Layout, MemRel at σ₁, σ₁.R = σ.R), or
  it leaves the loop at X with the cb word EXACTLY `stRes`. The OVF branch is closed by `compile_noovf`. It names no program.
- **`deflate_x86_N` (k7/K7/DeflateX86N.lean):** induction on k through `iterS_succ'`, `drv_iter_N` at each step with SrcInRange from
  K5's `deflate_inrange` and L.live carried by σ.R = σ₀.R. Conclusion, for every k with `iterS p k (initStore …) = some σ`: the
  machine reaches the head with memory related to σ, OR it has left the loop at X with cb = stRes. **OVF is excluded at the machine
  for DEFLATE; RES (ENV or STACK outgrown) is the one remaining non-DONE exit, and is NOT excluded** (stepT's table is not empty).
- **Going red:** drop the SrcInRange premise from drv_iter_N, and the OVF branch must fail to close.

## Addendum 9 (2026-11-15, the 80th head): RES for DEFLATE at the machine, MEASURED; UNREACHED by a static measure (STATUS-vir 373)
- **Measured** (k7/probes/ResNeed2.lean, k7-probe-res-002 EXIT=0; res-001 printed the first four lines, then went red on a missing
  import): stepT's lowered table has **4** functions. **All 4, and main, make NON-tail calls** (an `app` inside a `letE`'s first arm,
  so the continuation is a pushed frame). Static measures: main envM(·, 2) = **41** words, frD = **1**. Per function (from 3 words):
  envM 10 · 8 · 8 · 8, frD 1 each.
- **Verdict: a `resWhy_false` analogue by STATIC measure is UNREACHED for DEFLATE.** res_free bounds frames by frD along a run of
  main only because an empty table makes every call terminal. With non-tail recursive calls, the frames pushed grow with the
  recursion DEPTH, which is a property of the inputs, not of the code.
- **What would reach it (queued, not claimed):** (1) a generic depth-indexed res_free: frames ≤ frD(main) + Σ over the live call
  chain of frD(fᵢ), ENV ≤ the chain's sum of envM; (2) DEFLATE's per-function depth bound, taken from its termination measures
  (D3's: OUTMAX − m or the pending count, and the bit count per read); (3) ENV/STACK premises sized from (1)+(2). Until then
  `deflate_x86_N`'s RES disjunct stands, and it is stated as a limit wherever DEFLATE at the machine is cited.
