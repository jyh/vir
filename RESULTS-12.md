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
| K2 | no translation-validation fallback: each stage one ∀-program theorem | **HOLDS for S1 and S2** (`s1_refines`, `s2_refines`); S3 **OWED** | STAGE-S1.md; STAGE-S2.md |
| K3 | the driver theorem names no program | **OWED as a score** (the driver is S3's). **Provisional HOLDS** at the S1∘S2 statements: compile_refines, compile_noovf, compile_refines_noovf, s2_refines, through `k5/tools/k3_check.py`; positive control deflate_noovf reads FALSIFIED | compiler/STAGE-K5.md, row 296's reading |
| K4 | emitted instructions ⊆ §3 ∪ {imul, setcc, jo} | **OWED** (S3's code generator) | — |
| K5 | the overflow exit is unreachable for DEFLATE's step, n, OUTMAX < 2³², no per-input premise | **HOLDS**: `deflate_noovf` (k5p-118; audit k5-audit-009). † Strengthened: `deflate_noovf_loaded` discharges the loader premise, leaving the region's placement as the only caller premise (k5p-133; k5-audit-010) | compiler/STAGE-K5.md |
| K6 | 0 per-program layout lemmas | **HOLDS** on its declared population (DECLARATIONS-S2 §"K6's population": no file under compiler/ states a one-program layout lemma). Its first reading by the 70th head (UNREACHED) is withdrawn in the record | compiler/STAGE-K5.md, row 296's reading as corrected |
| K7 | the router compiled reproduces A.4's verdict, five exits witnessed, no router-specific lemma | **OWED** (needs S3). † K7-a, the S1∘S2 half: `router_refines` with no router-specific lemma (k7-001; k7-audit-001) | k7/STAGE-K7.md; compiler/DECLARATIONS-K7.md |

## Readings beside the scores (not scores)
- S2 took 41 builds to its first green audit against the plan's ~40. No amend-23 row predicts it (STAGE-S2.md).
- K5's route needed a missing S2 theorem first (K5-0: the overflow clause was declared and not proved). It was proved generically
  (`s2_noovf`, `compile_noovf`), so every program through the compiler gets it, not DEFLATE alone (DECLARATIONS-K5.md K5-0).
- Build logs: from k5p-122 and k7-001 on, the replayed-dependency warnings are filtered by a rule declared before its first use
  (k5/LOGS-FILTER.md). Earlier logs are byte-faithful (the helm's ruling (A), 2026-11-12).
