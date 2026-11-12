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
