# RESULTS-12: the compiler and DEFLATE scoreboard (amend-23 §D and §K), Lean arm only

**Frame written 2026-11-12 by the 70th vir head (STATUS-vir 302).** Every cell below is COPIED from the record that scored it, with
that record named, so a reader can check each verdict at its source. No verdict is first made here. A row whose source has not
scored it reads **OWED**, and this frame does not fill it. (D4 was scored at its source by the same head after this frame was first
written; its cell was copied from there.)
amend-23's own notes ride with every row. There is ONE arm, the Lean one (the MetaPRL arm builds neither object). The writer of the
predictions is the builder of the arm. Each row is a count or a verdict read from artifacts.

**Where the sources live.** Master at 7ee14f8 (jyh/vir #56) carries deflate/, compiler/, k5/ through K5-3, and DEFLATE-SHA-MAP.tsv.
The cells marked † are on local branches k6-layout and k7a until STATUS-vir rows 300/301 are merged. Prose written before the
11-12 rewrite cites pre-rewrite shas; DEFLATE-SHA-MAP.tsv maps them.

## §D — DEFLATE

| id | prediction (short) | verdict | source |
|---|---|---|---|
| D1 | S agrees with zlib on ACCEPT/REJECT over X5 (0 errata on accept/reject); disagrees on REASON on ≥ 1 rejected input | **FALSIFIED** on accept/reject (S literal, `inflateLit`, disagrees on 47 of 313 streams, all fixed blocks: erratum DEFLATE-E1). **HOLDS** on reason (Addendum A1's stream). The E1-repaired `inflate` agrees on 313/313 | deflate/x5/X5-RUN-1.md; deflate/STAGE-DEFLATE.md "Findings"; errata/ERRATA-DEFLATE.md |
| D2 | no change to L1 or L2 | **HOLDS**: 0 commits under l1/ l2/ over the branch (control: 121 under deflate/); 0 DEFLATE rows in ERRATA-L1/L2 | deflate/STAGE-DEFLATE.md "D5 and D6, SCORED" |
| D3 | the input cursor alone is not the termination measure | **HOLDS**: Φ f = mW·(TBL + BITS + OUT) + LOC with OUT = OUTMAX − m (Measure.lean:62–65) | same section |
| D4 | bit extraction uses no new primitive; ≥ 1 `fix` | **HOLDS** †: stepT has 4 `fix` nodes and applies {add, sub, mul, lt, le, eq} ⊆ P; P unchanged (D2) | deflate/STAGE-DEFLATE.md "D4 HOLDS"; k5/probes/D4Fix.lean, k5p-probe-D4-1 |
| D5 | canonical code ≥ 25 % of the arm's C5 tokens | **FALSIFIED**: 3,743 / 184,961 = 2.0 % (2.3 % over the nine declared files only) | deflate/out/counts-d5.tsv + .cmd; STAGE-DEFLATE "SCORED" |
| D6 | > 109 builds to correctness | **HOLDS**: 404 `saltbuild EXIT=` lines to df-audit-031 (builds alone: 310) | STAGE-DEFLATE "SCORED" |
| D7 | Safety on every input with no premise on the bytes | **OWED**: `SafetyStmt` carries `∀ x ∈ b, x < 256`; byte TYPE or premise is a NON-AUTHOR call (STATUS-vir 297; the author recommends the type) | STAGE-DEFLATE "SCORED", last bullets |

## §K — the compiler

| id | prediction (short) | verdict | source |
|---|---|---|---|
| K1 | 40 < S1 builds ≤ 80 | **FALSIFIED (low)**: S1 = 9 by the declared rule (all `s1-*` logs: 13) | compiler/STAGE-S1.md |
| K2 | no translation-validation fallback: each stage one ∀-program theorem | **HOLDS** for S1, S2 and S3 (`s1_refines`, `s2_refines`, `s3_refines_from_s2`; composed: `compile_x86`) | STAGE-S1.md; STAGE-S2.md; compiler/STAGE-S3.md |
| K3 | the driver theorem names no program | **FALSIFIED by the tool** on `S3.driver_x86` (offenders only S3.* and VIRBridge.Live, the compiler's own x86 stage and bridge; no DEFLATE or router constant; control router_x86 FALSIFIED with VIRL3.F, K5.*). Author reading HOLDS on the prediction's words; a NON-AUTHOR call on whether S3/VIRBridge are "the compiler's namespaces" is owed | compiler/STAGE-S3.md "K3"; earlier provisional reading: STAGE-K5.md row 296 |
| K4 | emitted instructions ⊆ §3 ∪ {imul, setcc, jo} | **FALSIFIED**: S3 emits `push`/`pop` (entry stub, every program; `letE`) and `cmovle` (`max`), outside the list; all three are T-exact in x86lean COVERAGE | compiler/STAGE-S3.md "K4" |
| K5 | the overflow exit is unreachable for DEFLATE's step, n, OUTMAX < 2³², no per-input premise | **HOLDS**: `deflate_noovf` (k5p-118; audit k5-audit-009). † Strengthened: `deflate_noovf_loaded` discharges the loader premise, leaving the region's placement as the only caller premise (k5p-133; k5-audit-010) | compiler/STAGE-K5.md |
| K6 | 0 per-program layout lemmas | **HOLDS** on its declared population (DECLARATIONS-S2 §"K6's population": no file under compiler/ states a one-program layout lemma). Its first reading by the 70th head (UNREACHED) is withdrawn in the record | compiler/STAGE-K5.md, row 296's reading as corrected |
| K7 | the router compiled reproduces A.4's verdict, five exits witnessed, no router-specific lemma | **HOLDS** on its declared rule (DECLARATIONS-K7 Add. 3): `five_exits` witnesses all five of A.4's inputs at the x86 machine (DONE, CODE 1·2·2·2·0; k7-audit-006), `router_x86` carries every finishing run, no lemma about F's structure, layout or cells. Limits: OVF excluded only at the witnesses; the instantiation reading is the author's (non-author read owed) | k7/STAGE-K7.md; compiler/STAGE-S3.md "K7" |

## Readings beside the scores (not scores)
- S2 took 41 builds to its first green audit against the plan's ~40. No amend-23 row predicts it (STAGE-S2.md).
- K5's route needed a missing S2 theorem first (K5-0: the overflow clause was declared and not proved). It was proved generically
  (`s2_noovf`, `compile_noovf`), so every program through the compiler gets it, not DEFLATE alone (DECLARATIONS-K5.md K5-0).
- Build logs: from k5p-122 and k7-001 on, the replayed-dependency warnings are filtered by a rule declared before its first use
  (k5/LOGS-FILTER.md). Earlier logs are byte-faithful (the helm's ruling (A), 2026-11-12).

## Addendum 1 (2026-11-15, the 79th vir head): the x86 stage, the driver, and K7 — where each figure lives
Nothing here is first scored here; each line names its source.
- **The compiler, source to x86-64:** `S3.compile_x86` (s3/S3/Cross3.lean): S1∘S2∘S3 about the source program; a finishing run
  ends at the machine returned DONE with its result words related to the value, or at OVF; a faulting run at FAULT or OVF; n
  source steps by ≥ n machine steps or OVF; RES (ENV or STACK outgrown, `ResWhy`) is the other exit. Source: compiler/STAGE-S3.md.
- **The driver at the machine (C0 (a)):** `S3.driver_x86` and `S3.driver_x86_R` (s3/S3/Driver3.lean, SrcR.lean): k chained runs of
  a step-shaped program under a fixed x86 loop. Source: compiler/STAGE-S3.md "K3", DECLARATIONS-DRIVER Addenda 4–6.
- **RES excluded generically** for empty-table code: `S3.resWhy_false` (s3/S3/ResFree.lean). Source: k7/STAGE-K7.md "K7-b2 piece (1)".
- **Two author readings owe a non-author read:** K3 (the tool FALSIFIED on the compiler's own S3/VIRBridge namespaces only) and
  K7 (HOLDS on its declared rule; OVF excluded only at the witnesses; the instantiation reading). Defaults as in the table.
- **Findings of the stage:** DECLARATIONS-S3 Addendum 11 (the declared `app` code miscompiled; fixed before any claim covered
  it); K4's instruction list missed push, pop and cmovcc.
- **Runs (C6, logged):** s3/logs 161 logs, 161 `saltbuild EXIT=` lines (90 EXIT=0, 71 EXIT=1; 137 builds `s3-NNN`, the rest audits
  and probes); k7/logs 36 logs, 36 lines (24 / 12; 19 builds `k7-NNN`). One k7 probe run is NOT logged (its log was deleted by
  the 79th head; saltbuild's audit log records it, k7/STAGE-K7.md). Counted by `cat <dir>/logs/*.log | grep -h 'saltbuild EXIT='
  | sort | uniq -c` at l5-lean 30e0e85 (the tree #78 lands).

## Addendum 2 (2026-11-15, the 80th vir head): the router at the machine for every world — beside K7, not a score
- **OVF excluded for every world:** `K7.router_inR` (k7/K7/RouterAll.lean): F's SrcInRange for every 87-cell world (W87) whose wire
  cells hold bytes; `exit_code_all` is exit_code without the checked-run premise. Source: k7/STAGE-K7.md, DECLARATIONS-K7 Add. 4.
- **R4 at the machine, total on R4's premises:** `K7.router_R4_x86` (k7/K7/RouterR4.lean): for every such world with sender < 4
  and topic < 4, the machine returns DONE with every cell at its scaled address equal to R4's post-state (termination by
  `router_halts`, contents from L3's R4 at frame ∅). This closes K7's limit (a) on R4's premise set. Source: k7/STAGE-K7.md,
  DECLARATIONS-K7 Add. 5.
- **No score moves:** both are lemmas about F, so by K7's declared rule they sit beside K7 (still HOLDS on its five witnesses,
  non-author read owed), never inside it.
- **Runs (C6, logged):** k7/logs 55 logs, 55 `saltbuild EXIT=` lines (32 EXIT=0, 23 EXIT=1), +19 since Addendum 1. Sources of six
  of those probes (k7-probe-inR-002…007) are not in the tree (stated in STAGE-K7); their logs are. Counted by the same command at
  l5-lean 4199385.

## Addendum 3 (2026-11-15, the 80th vir head): DEFLATE at the x86 machine, in the driver's disjunctive form
- **`K7.deflate_x86`** (k7/K7/DeflateX86.lean): `S3.driver_x86_R` instantiated at DEFLATE's step from the loader's image of the
  initial store. For every k steps that DEFLATE's iteration takes, the machine reaches its loop head again with memory related to
  the k-th store, OR some iteration leaves the loop with a non-DONE status. Source: k7/STAGE-K7.md, DECLARATIONS-DRIVER Add. 7.
- **Not DONE-only:** the non-DONE exit is not excluded, because the driver does not name the status. K5's no-overflow result holds at
  S2 and does not pass through this driver; RES is not excluded for DEFLATE (its table is not empty). A driver variant carrying a
  per-iteration no-overflow premise is queued, not claimed.
- **Runs (C6, logged):** k7/logs 61 logs, 61 `saltbuild EXIT=` lines (35 EXIT=0, 26 EXIT=1), +6 since Addendum 2. Same command, at
  l5-lean 0a8d495.

## Addendum 4 (2026-11-15, the 80th vir head): DEFLATE at the x86 machine with overflow excluded
- **`K7.deflate_x86_N`** (k7/K7/DeflateX86N.lean) supersedes Addendum 3's disjunct. For every k steps DEFLATE's iteration takes, the
  machine reaches its loop head with memory related to the k-th store, OR it has left the loop with status RES. **OVF is excluded
  at the machine**, through a new generic driver step `S3.drv_iter_N` (s3/S3/DriverN.lean, names no program) and K5's per-step
  range result. RES (ENV or STACK outgrown) is not excluded. Source: k7/STAGE-K7.md, compiler/STAGE-S3.md, DECLARATIONS-DRIVER Add. 8.
- **Runs (C6, logged):** k7/logs 64 logs (38 EXIT=0, 26 EXIT=1); s3/logs 163 logs (91 / 72). Same command, at l5-lean e0e443a.

## Addendum 5 (2026-11-15, the 80th vir head): the router served k times at the machine, DONE-only — beside K7
- **`K7.router_served_x86`** (k7/K7/RouterDriver.lean): from any 87-cell world with wire bytes and R4's premises, loaded and placed
  at the driver's loop head, the machine returns to the loop head after EVERY k calls of the compiled router. Its memory is related
  to the k-th store of the router's source iteration, and no call ends in OVF, RES or FAULT. One call keeps the world's invariant
  (`router_inv_step`), so the iteration exists for every k. The driver step for an empty table, `K7.drv_iter_D`, is generic.
  Source: k7/STAGE-K7.md, DECLARATIONS-K7 Add. 6.
- **No score moves** (a router result, beside K7).
- **Runs (C6, logged):** k7/logs 70 logs (42 EXIT=0, 28 EXIT=1). Same command, at l5-lean 53ce4b8.
