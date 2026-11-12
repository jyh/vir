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
