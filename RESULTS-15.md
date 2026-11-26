# RESULTS-15 — proved programs compile with NO index checks (OBJECT-NOCHECK, PREDICTIONS-amend-26 NC1–NC9)

Scored 2026-11-25 by the 90th vir head, the same day as the object's pin (5a0d823) and its erratum E1 (58791ef). The writer is also the
builder (amend-26's preamble). Every figure below is read from a committed artifact named in its row. **A non-author read of
`compile_x86_proved`'s statement is OWED** (asked for on the bus with this file); until it lands, this page reports what was built and
measured, not a read.

## What was built (option (iv), his 11-25 word)
- **`S3.compile_x86_proved`** (`s3/S3/Proved.lean`): for a program the compiler accepts and that is PROVED in the sense of NC-P′
  (`NoFaultP`: no reachable source configuration faults, and every reached `ret` atom evaluates; every L2 `Triple` supplies both),
  the UNCHECKED lowering `lower3u` matches every finishing ⟶₂ run (DONE with a related result, or OVF, or RES) and every n-step prefix.
  It has **no fault clause**: under NC-P′ there is no faulting run to carry.
- **`S3.lower3u`** (`s3/S3/Lower3.lean`): `lower3` with the four instructions `test`, `js`, `cmp`, `jge` of every `load`/`store` omitted.
  Overflow checks (`jo`) stay. `lower3` and `compile_x86` are unchanged (NC5).
- **`S3.word_no_fault`** (`s3/S3/NoFault.lean`, NC-W): under compile_refines' premises and NC-P′, no word run reaches FAULT. Derived
  from compile_refines' clauses (1) and (3), `src_classify` and `stepW`'s determinism. Nothing under `compiler/VIRC` changed.
- **`K7.router_triple_x86_proved_p`** (`k7/K7/RouterProved.lean`, NC-R): L3's router triple R4 carried to the machine through
  `lower3u`. R4 supplies NC-P′.

## Scores
| id | prediction | measured | verdict |
|---|---|---|---|
| NC1 | 0 lines changed under `compiler/VIRC/` | `git diff --numstat e3a8181..39ee4fd -- compiler/VIRC`: **0 files** | **HELD** |
| NC2 | exactly 4 instructions removed per load/store site, no other change; on F, 4 × sites | `k7/probes/NcCount.lean` (log `k7/logs/nc-r-003.log`): F has **20** sites; `allCode` checked **731**, unchecked **651**, difference **80 = 4 × 20**; `test` 20→0, `js` 20→0, `cmp` 57→37, `jge` 20→0. The four class drops sum to the total drop. The `gen` cases at 39ee4fd emit `ldChk`/`stChk`, whose two branches differ by exactly those four. | **HELD** (instrument: counts by class and in total, not a sequence diff) |
| NC3 | premises = compile_x86's + NC-P′ (one hypothesis) | `s3/probes/nc-compile_x86-print-after.txt` vs `nc-compile_x86_proved-print.txt`, split on top-level `→`: the diffs are `ctxOf`→`ctxOfU`, `lower3`→`lower3u` (the object's substitution), **+`S3.NoFaultP vs e σ`**, and clause (2) removed. One display difference (`∃ ws m', ⋯` vs `∃ ws, ⋯`) is pretty-printer elision; with `pp.deepTerms` both read `∃ ws m',` (`s3/logs/nc-016.log`) | **HELD** (scored with NC-P′, per E1) |
| NC4 | 0 `.fault` in the statement; two clauses | the statement text: **0** `.fault`, **0** `Faults`; the one case-insensitive `fault` is the premise name `NoFaultP`. Two conjuncts. | **HELD** |
| NC5 | `compile_x86`'s statement byte-identical | `#print S3.compile_x86` at e3a8181's sources (`nc-002`, sha256/16 ed66240bc6e27fa6) vs after (`nc-015`): statement 5,674 = 5,674 bytes, **identical**; the whole print (proof term included) is identical too | **HELD** |
| NC6 | router carried with 0 new router-specific lemmas | `k7/K7/RouterProved.lean` declares one theorem and no lemma; it uses `R4`, `loader_ok`, `F_typed`, `F_wfB`, `F_fnOk`, `F_ok2`, `F_table`, `F_need`, `F_tbl_nil`, `good_cap`, `envRel_cap1`, `regionAt_lookup_p`, all already used by `router_triple_x86_p`/`router_x86` | **HELD** |
| NC7 | 40 < builds ≤ 80, first route file → compile_x86_proved EXIT=0 | `s3/logs/nc-001` … `nc-012`: **12** saltbuild runs (6 EXIT=0, 6 EXIT=1); `nc-012` is the first with `S3.Proved` at EXIT=0 | **FALSIFIED (low)**: 12 ≤ 40 |
| NC8 | one ∀-program theorem, no translation validation | the statement: no per-program premise beyond NC-P′ | **HELD** |
| NC9 | axioms ⊆ {propext, Classical.choice, Quot.sound} | `s3/logs/nc-013.log`: `compile_x86_proved`, `word_no_fault`, `s3_refines_from_s2B`, `lift3u` each **[propext, Classical.choice, Quot.sound]**; `k7/logs/nc-r-004.log`: `router_triple_x86_proved_p` the same; controls `nc-014`, `nc-r-005` print `[sorryAx]` and `[Lean.trustCompiler]` | **HELD** |

**All route builds:** 25 logged runs (16 EXIT=0, 9 EXIT=1) across `s3/logs/nc-*` (19) and `k7/logs/nc-r-*` (6), counted by
`cat s3/logs/nc-*.log k7/logs/nc-r-*.log | grep -h 'saltbuild EXIT=' | sort | uniq -c`.

## Why NC7 fell low, read from the logs (a finding, not an excuse)
The REVIEW's price (40–80) was an estimate by analogy with S2/S3's own builds. What made it cheap:
- **NC-W needed no simulation work.** The three clauses of `compile_refines`, already proved, pin the word run against the source run;
  the whole-run argument (fork N1 (a)) built first time (`nc-001`).
- **The unchecked proofs are the checked proofs with steps deleted.** `sim_load`/`sim_store` were split on the flag mechanically: the
  `true` branch is the old proof unchanged, and the `false` branch is its in-bounds path with the four check steps removed and the
  step counts lowered (9→5 and 10→6). The failures were a stale literal (`nc-004`), the per-declaration heartbeat limit on the now
  twice-as-long `sim_store` (`nc-005`; raised to 600000 for that declaration only, `nc-006`/`nc-007`), a name shadowed by `intro`
  (`nc-009`/`nc-010`), and a downstream premise (`nc-008`).
- **Directions (amend-26, no thresholds):** fork N1 (a) needed no new determinism lemma (`WN.det_stuck` and `WN.from_stopped` exist in
  `compiler/VIRC/S2.lean`). The flag reached **2** simulation lemmas directly (`sim_load`, `sim_store`), was threaded as a premise through
  **4** (`sim_step`, `s3_run`, `s3_refines`, `s3_refines_lower3`), generalised **1** placement lemma (`lower3_placed`), and added one
  equality hypothesis to **2** size lemmas (`gen_er`, `gsz_congr`), with **2** new erasure lemmas (`ldChk_er`, `stChk_er`).

## ERRATA-NOCHECK E1 in the result
The pinned NC-P (no reachable configuration faults) does not exclude a run that stops at a `ret` whose atom does not evaluate,
because every `ret` is terminal. The route takes NC-P′. **Red backwards:** `s3/probes/MutNoFaultPinned.lean` (NC-P as pinned) fails
with ONE error, at the `ret` case that uses the second conjunct (`s3/logs/nc-019.log`; `nc-018` was a defective mutant, an `open` of
an unimported namespace, and is not counted). **Limit:** this shows that THIS proof needs the conjunct, not that no proof could do
without it. A typed closed program probably never reaches such a `ret`, but proving that would need L2's runtime typing at the start
state, which compile_x86's premises do not carry. Every L2 `Triple` supplies the conjunct, so NC6 is unaffected.

## What this does NOT claim
no speed figure (the 80 fewer instructions on F are a count, not a measurement of time) · overflow checks unchanged · no external-caller
entry check (fork N3 (a): its object comes next, with its own predictions) · no claim beyond `compile_x86`'s trust (XED decode, the
S4 differential run) · NC2 is measured on F only, and its "no other change" is a count argument over four classes plus the `gen` read.
