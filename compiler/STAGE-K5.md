# K5, the stage record (STATUS-vir 295; DECLARATIONS-K5.md and its addendum 1 were written first)

## K5-1a: PROVED (68th head, 2026-11-12), VIRC/NoOvf.lean, Sim2.lean not edited
- `s2_noovf`: under `s2_refines`'s hypotheses and `InRangeRun (.run (lowerT e) ρ₀ [], σ)`, every word run from W₀ has
  `W'.1 ≠ .ovf`. `s2_refines_noovf`: s2_refines (1) without its `∨ .ovf`. No hypothesis beyond InRangeRun and s2_refines's own.
- Route as declared: (i) `stepW_noovf`, a pure word-machine fact (every `.ovf` step is a head operand's `.ovf`; Word.lean has
  no other ovf path); (ii) `opd_noovf`/`opdL_noovf`, the opd_sim induction; (iii) `heads_*` per construct + `step_noovf`;
  (iv) `s2_run_noovf`, by induction on the WORD run, with `stepW` deterministic and `fault` final (`WN.from_fault`).
- Builds: k5-001 (bad saltbuild argument, no Lean run), k5-002/003 red (tactics), k5-004 EXIT=0, k5-005 root EXIT=0,
  k5-006 EXIT=0 (rebuild after the mutants).
- Audit k5-audit-001: 19 rows within propext · Classical.choice · Quot.sound (axiom_gate --no-control OK; `stepW_noovf` uses
  propext · Quot.sound only). Control k5-audit-control-001 shows sorryAx (axiom_gate OK).
- Mutants: k5-mutant-002 (`Val.inR`'s int case → True) is RED at exactly add · sub · mul (NoOvf l. 92/98/104) and nowhere
  else: the range premise is what closes the three `chk` sites. k5-mutant-001 (prim's result clause dropped) is red too, but at
  a structural `rw`, so it is recorded and NOT counted as evidence.
- Scope, stated beside the verdict: InRangeRun is a predicate on the IR run (S1's image). The ⟶₂ form is K5-1b, OWED.

## K5-1b: PROVED (68th head, 2026-11-12), VIRC/NoOvfSrc.lean (declared first: DECLARATIONS-K5 addendum 2, vir 72b9c8f)
- `compile_noovf`: under `compile_refines`'s hypotheses and `SrcInRange (instL 0 vs e, σ)` (every configuration the ⟶₂ run
  reaches evaluates in-range atoms next), NO word run of the compiled program reaches `.ovf`. `compile_refines_noovf`:
  compile_refines (1) without its `∨ .ovf`. No hypothesis beyond SrcInRange and compile_refines's own. **K5-0 is closed at
  the source**, for every L2 program the compiler accepts.
- Route as declared: `ir_step_match` (letE push: same source configuration; a final `ret`: done; otherwise `src_steps` forces
  a ⟶₂ step and `step_notlet`, sim_step's body copied for a NotLet code, matches it), `ir_reach`, `ARel.inR` + `valOf_inR`,
  `match_stepInR`, `inRangeRun_of_src`, then K5-1a's `s2_noovf`. ir_reach answers declared falsifier 1: every IR state reachable
  from a matched start IS finished or matched (S1 has no uncharacterised states).
- Builds: k5-007/008 red (names, a `stepFn₂_sound` unification, a wildcard `cases` arm), k5-009 EXIT=0, k5-010 root EXIT=0,
  k5-011 EXIT=0 (rebuild after the mutant).
- Audit k5-audit-002: 29 rows (the 19 of audit-001 + 10) within the three; control k5-audit-control-001 (sorryAx) stands.
- Mutant k5-mutant-003 (`Atom.inR₂`'s int case → True): RED at exactly one site, `valOf_inR` (NoOvfSrc l. 53), the point
  where a source result's range becomes the IR value's range.
- **Duplication declared:** `step_notlet` is a verbatim copy of sim_step's body (S1.lean l. 98–181) so S1.lean stays unedited;
  it counts in this file's C5 and is named here so a count can subtract it.
- NEXT: K5-2 `deflate_inrange` (SrcInRange for DEFLATE's step term from Safety's Inv, bounds in n and OUTMAX only), K5-3.

## K5-2: IN PROGRESS (68th head, 2026-11-12), project k5/ (DECLARATIONS-K5 addendum 3, route A)
- **Generic half DONE** (k5/K5/Checked.lean): `headB` (a Bool check, `headB_sound` → `Tm.HeadInR`), the checked runner
  `stepFn₂C`/`run₂C`, `srcInRange_runC` (by `step₂_det`), `srcInRange_ret`, `srcInRange_step` (one checked step), `inRange_eq`.
- **The kernel's limit, measured:** a trace written as ONE nested `run₂C 40` term passes elaboration and is refused by the
  kernel, "deep recursion detected" (k5p-004/005; probes 001–003 localise it to the nesting, not the range proofs). The fix is
  the walk `repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [...])`: a chain term.
  An `omega` discharger for the range facts timed out (probe-004) and is not used.
- **The porter** (scratch `port.py` + `fix.py`, the method recorded here): each Step.lean trace is copied with its conclusion
  swapped to `SrcInRange (closeAt p T, σ)` and its trace `simp` wrapped in the walk. A build's leftover goals are EXACTLY the
  arithmetic sites' range facts, which `fix.py` turns into named hypotheses `rrN : inRange (e) = true` (or a `norm_num` fact
  for a literal) round by round until the build is clean. The hypotheses are the record of every arithmetic site a mode's
  run passes through.
- Done so far: HDR (Checked), READ's bit step (Read, r7–r10), Modes1 (12 traces: hdrb hdrd shdr slen snlen fixlens_step
  fixlens_end dhdr dh2 dh3 dh4 clput; k5p-015 EXIT=0). Modes2 (21 traces) in rounds from k5p-020.
- **OWED for K5-2, in order:** the BUILD family (11 traces), TABLE (its BITc call: POW/STRIP's arithmetic under the fix),
  the dispatch prefix (stepT → mode term), then **K5-2b: discharge every rrN at the Safety level** (the mode's own facts +
  `Mag`, finding K5-2-0), then `deflate_inrange` over the 28 modes, then K5-3.
- **Update, end of the 68th head:** Modes2 20/21 (k5p-028), Modes3 10/11 BUILD (k5p-049), Modes4 DECODE (k5p-050: its `tauto`
  hit the recursion limit over the added facts → `not_and_or.mp hh`), Dispatch `step_inR` (k5p-032: the dispatch adds no range
  fact). **Traces done: HDR, READ bit, 12 + 20 + 10 + 1 = 45 mode traces + the dispatch.** OPEN: `build_left_end` (whnf
  heartbeat timeout over the whole declaration even at 16M and de-duplicated, k5p-probe-006/008 and BuildLeftEndWIP rounds;
  next: split its walk at a `by_cases` or state it in two halves), TABLE (BITc), `readbit_trunc`'s twin is done in Modes2.
  **The K5-2b work list is k5/RANGE-SITES.md: 202 distinct (trace, expression) range obligations**, each to be discharged
  from Safety's facts or `Mag`.
- **K5-2b PILOT DONE: `read_inR` (k5/K5/SafeRead.lean, k5p-052):** READ in range on every world satisfying Safety's `Inv`, n < 2³²,
  from Inv ALONE (InvM.read: `wt·2^k ≤ kcap ≤ 65536` bounds wt and k ≤ 16; t ∈ {0,1}; acc < wt). Safety's `safeI_read`'s own
  derivation is the template for every other mode. Audit k5-audit-001: 12 rows within the three; control sorryAx.
- build_left_end with `maxHeartbeats 0` ran 11.5 min holding the fleet lock and was stopped by its owner (k5p-probe-009):
  the unbounded form is impractical; split its 64-way case analysis into separate theorems.
- **build_left_end DONE (69th head): `build_left_end_inR` (k5/K5/BuildLeftEnd.lean, GENERATED by k5/tools/gen_ble.py), k5p-054 EXIT=0.**
  Cause of the timeout: `maxHeartbeats` is a PER-DECLARATION budget, and the 64-way `by_cases` walked every branch inside one
  declaration. Fix: one theorem per real source path, 3 (e1: c1/rest) × 4 (ex: var/tot) × 2 (0 < left) = 24 (`ble_p00..23`, 4M each;
  the module built in 121 s), and `build_left_end_inR` is the case tree that dispatches to them. Timing probe k5p-probe-010
  (2 leaves, EXIT=0). Audit k5-audit-003: build_left_end_inR, ble_p00, ble_p23 within the three. **K5-2 traces: 46 + the dispatch;
  open: TABLE (BITc).**
- **TABLE DONE (69th head): `table_inR` (k5/K5/Table.lean), k5p-058 EXIT=0.** The BITc call is carried by a CHECKED-RUN relation
  `Reach` (k5/K5/Bit.lean: trans, the `let` frame `Reach.letE`, `Reach.srcInRange`) and three inductions mirroring Step.lean:
  `pow2_reach` (k ≤ 7), `strip_reach` (i + n ≤ 7, 0 ≤ v < 256, with `stripTop_rng`), `bit_reach` (0 ≤ b < 256, i ≤ 7). TABLE's own
  hypotheses are Safety's `tb_rng` (tb < 256, ti ≤ 7); no rrN is left open in it.
  Lessons (each cost a probe, k5p-probe-011..025): the walk's evaluator must NOT unfold `inRange` (kernel deep recursion): use
  `inRange_eq` as a conditional rewrite with `(disch := omega)`; and a lemma whose conclusion carries `2 ^ k` symbolically hits
  kernel deep recursion at defeq: state it over a plain `v : Int` with bounds and rewrite `2^(k+1) = 2 * 2^k` at the call.
  Audit k5-audit-004: 17 rows (Audit.lean + build_left_end_inR, pow2_reach, strip_reach, bit_reach, table_inR), all within the three.
  **K5-2 trace coverage: HDR, READ, 12 + 20 + 11 + 1 mode traces, TABLE, the dispatch. NEXT: K5-2b (RANGE-SITES, 27 modes after
  READ), then deflate_inrange, then K5-3.**
- **K5-2b, 69th head: 22 of 28 modes in range from `Inv` alone** (Safe1–4 + SafeRead, vir 88f332e · eeb50c7 · b63fa35 · f3d47b6;
  k5p-060/063/064/065 EXIT=0). **Finding K5-2-1 + `Mag` re-declared: DECLARATIONS-K5.md Addendum 4 (vir 1871722)**, before any Mag file.
  Its required census, run after it, over Step.lean (178 stores, `store \[` = `tcap .store`, two needles agree): cPEND 10 stores
  (l.650 SLEN, 683 SCOPY, 1738 SYMD, 1745 LENX, 1775 COPY, 2259/2262/2264 LSYM, 2273 LREP → REP, 2285 REP) — the two not named in
  the addendum land in REP, which `facts_rep` bounds (fl + pd ≤ hl + hd), so no clause is owed; cDIST 2 (1753 DSTD, 1763 DSTX);
  cCODE/cLEFT/cREST/cTOTAL 2 each (BUILD); X and X+1: l.1509/1510 (DECODE) and l.1698/1699 (reqDecN) — the reqDecN X store has a
  PARAMETER target `.v w0` that a `.v "…"` needle misses (found by the second needle shape the addendum names). Consistent with
  the addendum: no unlisted write to a `Mag` cell.
- **ALL 28 MODES IN RANGE AT THE SAFETY LEVEL (69th head).** 22 from `Inv` alone (Safe1–4, SafeRead, TABLE); 6 from `Inv ∧ Mag`
  (k5/K5/Mag.lean: SNLEN LENX DSTX LREP DECODE; k5/K5/SafeBuild.lean: BUILD, one theorem per phase), n, OUTMAX < 2³². Two BUILD paths
  had NO trace and are now traced (k5/K5/BuildZero.lean): phase 0's cell path (`build_zero_cell_inR`, k5p-069) and phase 4 with a
  source length of 0 (`build_syms_skip_inR`, k5p-073: `build_syms_cell_inR` takes slot[0]'s range unconditionally, and slot[0] is
  bounded by nothing). **⇒ the 11:0x claim "every mode has its trace" was FALSE; it is corrected on the bus.** The wrappers are the
  coverage check that caught both: a mode's wrapper compiles only if every path of the mode reaches a trace.
  Audit k5-audit-005: 39 rows, all within propext / Classical.choice / Quot.sound, 0 sorryAx.
  **OWED, in order:** `Mag_step` (preservation over the 28 modes, Addenda 4–5's clauses), then `deflate_inrange` (Dispatch's
  `step_inR` + the 28 wrappers, over Safety's reachable worlds), then K5-3.
- **`step_inrange` PROVED (69th head, vir 14e1a31, k5p-078; k5/K5/InRange.lean):** DEFLATE's step term is in range on every world
  with `Inv ∧ Mag`, n, OUTMAX < 2³², bytes < 256 (Dispatch's `step_inR` + the 28 wrappers; mode lookup by `rfl` per key — `simp`
  cannot reduce `List.lookup` on Int keys past the head). Audit k5-audit-006 40 rows within the three.
  **⇒ K5-2's ONLY open premise is now `Mag_step`.**
- **`Mag_step` begun (k5/K5/MagStep.lean, k5p-080):** `world_uniq` (one store ⇒ one cell function on the region), `Mag_congr`,
  `Mag_of_explicit` (the per-mode form: the mode's explicit step pins `stepS`'s store), and the first mode, **SLEN** (the step
  that MAKES P1). **Route for the other 27:** per mode, the explicit store from Safety's `safe_*` (5 exist) or from Step.lean's
  `<mode>_step` via `stepS_of_mode` exactly as the mode's `safeI_*` builds it, then the 9 clauses of the explicit cell function
  (most are vacuous by the new mode; the frame is `Function.update_apply` away from the written cells).
- **K5-2 CLOSED (69th head): `deflate_inrange` PROVED (k5/K5/DeflateInRange.lean, vir 12a5a95, k5p-116).** For every byte string
  (bytes < 256), n, OUTMAX < 2³², either reading, and every world the iteration reaches from `initStore`, the step term is in range
  at every configuration of its run. Route: `reach_inv` (induction over `iterS`: Safety's `stepSafe_of safeI_build` keeps `Inv`,
  `Mag_step` keeps `Mag`, DONE/REJECT fixed by `stepS_fixed`), then `step_inrange`. `Mag_step` (MagAll.lean, k5p-114) dispatches the
  28 mode cases of MagStep.lean (23) and MagBuild.lean (BUILD, 5 phases); each pins the step's store from Safety's/Step.lean's
  explicit step and reads the new cells off it. **Audit k5-audit-007: 46 rows, all within propext / Classical.choice / Quot.sound,
  0 sorryAx** (deflate_inrange, reach_inv, Mag_step, Mag_step_build, Mag_step_decode, Mag_step_build2 among them).
  The premise beyond Addendum 3's statement is `Mag`, PROVED preserved, so the theorem's hypotheses are only bytes < 256 and
  n, OUTMAX < 2³² (no premise on the bytes' content: K5's falsifier is not met). **NEXT: K5-3 `deflate_noovf`.**
- **K5-3 `deflate_noovf` PROVED (70th head, k5/K5/DeflateNoOvf.lean, k5p-118 EXIT=0; root K5 k5p-119 EXIT=0), with
  `deflate_refines_noovf` (row 296: compile_refines (1) at DEFLATE's step term, without its overflow disjunct).** Declared first as
  DECLARATIONS-K5.md Addendum 6 (vir 6752570). Instance: Γ₀ = [tcap], Δ₀ = [true], vs = [cap p], ρw₀ = `capWords lay p (L0 n om)`.
  The four per-program facts (`Tm.wfB 1`, `fnOk`, `ok2` of stepT; lowered table length < 2⁶⁴) close by `decide` (probe
  k5p-probe-stepT-1 EXIT=0); `instL 0 [cap p] stepT = closeAt p stepT` is `rfl`. EnvRel comes from `World.reg` at the reached σ
  (`envRel_cap`, the cap parameter's two words; not a statement about `Layout`). **Hypotheses of deflate_noovf: bytes < 256,
  n, OUTMAX < 2³², σ reached by `iterS`, and the loader premise `Layout σ lay`, `MemRel lay σ m`, which every program carries.**
  No premise on the bytes' content. **Audit k5-audit-009: 55 rows (48 within the three, 7 [propext]), 0 sorryAx** (k5-audit-008
  EXIT=1 audited a stale root olean: the 9 new names unknown, so it was re-run after k5p-119). Going red: k5p-probe-mut-stepT-1
  states `Tm.ok2 stepT = false` and table length < 2; `decide` REFUSES both (2 errors at lines 5 and 8, EXIT=1), so the facts
  are evaluated rather than vacuous. **K5 (amend-23) reads HOLDS at this sha: the overflow exit is unreachable for DEFLATE's step
  under n, OUTMAX < 2³² with no per-input premise.** Row 296's K3/K6 reading at this sha is still owed (its own row).
