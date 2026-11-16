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
| D7 | Safety on every input with no premise on the bytes | ⚠️ HOLDS by the non-author read, Addendum 6; the ByteArray form with no premise, Addendum 7. Was **OWED**: `SafetyStmt` carries `∀ x ∈ b, x < 256`; byte TYPE or premise is a NON-AUTHOR call (STATUS-vir 297; the author recommends the type) | STAGE-DEFLATE "SCORED", last bullets |

## §K — the compiler

| id | prediction (short) | verdict | source |
|---|---|---|---|
| K1 | 40 < S1 builds ≤ 80 | **FALSIFIED (low)**: S1 = 9 by the declared rule (all `s1-*` logs: 13) | compiler/STAGE-S1.md |
| K2 | no translation-validation fallback: each stage one ∀-program theorem | **HOLDS** for S1, S2 and S3 (`s1_refines`, `s2_refines`, `s3_refines_from_s2`; composed: `compile_x86`) | STAGE-S1.md; STAGE-S2.md; compiler/STAGE-S3.md |
| K3 | the driver theorem names no program | **FALSIFIED by the tool** on `S3.driver_x86` (offenders only S3.* and VIRBridge.Live, the compiler's own x86 stage and bridge; no DEFLATE or router constant; control router_x86 FALSIFIED with VIRL3.F, K5.*). Author reading HOLDS on the prediction's words; a NON-AUTHOR call on whether S3/VIRBridge are "the compiler's namespaces" is owed | compiler/STAGE-S3.md "K3"; earlier provisional reading: STAGE-K5.md row 296 |
| K4 | emitted instructions ⊆ §3 ∪ {imul, setcc, jo} | **FALSIFIED**: S3 emits `push`/`pop` (entry stub, every program; `letE`) and `cmovle` (`max`), outside the list; all three are T-exact in x86lean COVERAGE | compiler/STAGE-S3.md "K4" |
| K5 | the overflow exit is unreachable for DEFLATE's step, n, OUTMAX < 2³², no per-input premise | **HOLDS**: `deflate_noovf` (k5p-118; audit k5-audit-009). † Strengthened: `deflate_noovf_loaded` discharges the loader premise, leaving the region's placement as the only caller premise (k5p-133; k5-audit-010) | compiler/STAGE-K5.md |
| K6 | 0 per-program layout lemmas | **HOLDS** on its declared population (DECLARATIONS-S2 §"K6's population": no file under compiler/ states a one-program layout lemma). Its first reading by the 70th head (UNREACHED) is withdrawn in the record | compiler/STAGE-K5.md, row 296's reading as corrected |
| K7 | the router compiled reproduces A.4's verdict, five exits witnessed, no router-specific lemma | **HOLDS** on its declared rule (DECLARATIONS-K7 Add. 3): `five_exits` witnesses all five of A.4's inputs at the x86 machine (DONE, CODE 1·2·2·2·0; k7-audit-006), `router_x86` carries every finishing run, no lemma about F's structure, layout or cells. Limits: OVF excluded only at the witnesses; the instantiation reading is the author's (non-author read owed) · ⚠️ SUPERSEDED by Addendum 6: the cell did not cover K7's second conjunct; read (non-author) and re-scored there | k7/STAGE-K7.md; compiler/STAGE-S3.md "K7" |

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

## Addendum 6 (2026-11-15, the 81st vir head): the three non-author reads (K3, K7, D7), and K7's second conjunct proved
**The reads** were made by the seat paper, which built none of this, at vir 60dda68 (bus 11-15 11:47; its record is in the fleet's
private store). Its coverage, as it states it: statements, declarations and the K7 proof files read; K3's tool re-run on
k7-probe-K3-003.log; NO Lean build, audit or mutant; the bodies of Safety.lean, RouterAll and RouterDriver not read.
- **K3: HOLDS on the prediction's falsifier (non-author).** amend-23's falsifier is "a program constant". The S1 declaration's
  whitelist has two sentences: (i) constants "must lie in" VIRC/VIRL1/VIRL2/X86/core; (ii) the listed namespaces and the
  router/inflate/deflate names "FALSIFY K3". Applied by (ii) alone, `driver_x86` reads 0 and `compile_x86` 0 (control 1, VIRL3.F).
  The tool's FALSIFIED (on S3.* and VIRBridge.Live) comes from (i), which was typed before S3 and the bridge existed, and is
  recorded as an INSTRUMENT finding beside the verdict. The fork's arm A ("they gain whitelist status by declaration") is not
  supported: DECLARATIONS-S3 and -S3-bridge name no namespace and do not mention K3.
- **K7: conjunct (1) HOLDS (non-author); conjunct (2) was NOT COVERED by the cell above.** K7 reads *"its five exits are witnessed
  … AND the L3 router triple is carried to the machine with no router-specific lemma"*. The cell scored (1) and the instantiation.
  For (2), R4 reached the machine only through `router_halts`/`router_inR`, lemmas about F's structure, which K7-a's rule (written
  before the files) reports AGAINST K7. vir accepts the read (DECLARATIONS-K7 Addendum 7, written before the test below).
- **K7 conjunct (2), the test the reader named, run: HOLDS in partial-correctness form.** `K7.router_triple_x86`
  (k7/K7/RouterTriple86.lean): from R4's own premises on the world's contents f and `RegionAt 0 87 f σ`, for every FINISHING
  source run, the final store is `RegionAt 0 87 (postF f 0)` AND the machine ends DONE with the result related to it, or at OVF,
  or at RES. Its proof uses only `router_x86` (the instantiation), L3's `R4` (the triple), and generic L2 facts
  (`regionAt_lookup_p`, the empty frame); no `router_inR`, no `router_halts`, nothing about F's cells or layout (grep of the file:
  those names appear only in its header comment). k7-035 EXIT=0; k7-audit-013 EXIT=0, 42 rows within the three axioms, 0 sorryAx,
  the new row [propext, Classical.choice, Quot.sound]. **Red backwards:** k7-probe-mut-triple-001 (the post-state weakened to the
  pre-state f) EXIT=1, one error, at the post-state line. **Limit:** OVF and RES are NOT excluded in this form (excluding them
  needs `router_inR`, a router lemma); the TOTAL form stays beside K7 as `router_R4_x86`.
- **K7, re-scored: HOLDS, both conjuncts** — (1) the five exits, (2) the triple in partial-correctness form with OVF and RES as
  stated disjuncts — non-author read on (1) and on the instantiation reading; (2) proved after the read, by its named test.
- **D7: HOLDS (non-author).** Over `Array Nat`, "< 256" is what a byte string is (OBJECT-DEFLATE X3 (a); DECLARATIONS-DEFLATE), and
  the bound N depends on the input's size and OUTMAX only. A `ByteArray` corollary (premise discharged by `UInt8.toNat_lt`) would
  retire the reading; it is not built.
- **Runs (C6, logged):** k7/logs 84 logs (48 EXIT=0, 36 EXIT=1); this addendum's: k7-032 (a wrong saltbuild argument, EXIT=1),
  k7-033/034 (a missing import, a destructuring slip; EXIT=1, redacted home path → `~/fleet`, `~/.elan` as earlier logs are),
  k7-035 EXIT=0, k7-036 (the root, EXIT=0), k7-audit-012 (the root not yet rebuilt, EXIT=1), k7-audit-013 EXIT=0, the mutant EXIT=1.

## Addendum 7 (2026-11-15, the 81st vir head): D7's byte-type corollary — the reading retired
The non-author read (Addendum 6) found D7 HOLDS and named the test that would retire the reading. Run: `safety_bytes` and
`correct_bytes` (deflate/VIRDeflate/Bytes.lean) state SAFETY and CORRECTNESS over `bs : ByteArray` with NO hypothesis on the bytes;
the `< 256` premise is discharged by `UInt8.toNat_lt` (`ofBytes_lt`), and N is the same function of the size and OUTMAX. Proved
from `safety` and `correct` only. df-312 EXIT=0; df-313 (the root) EXIT=0; df-audit-032 EXIT=0, both rows
[propext, Classical.choice, Quot.sound], 0 sorryAx. Red backwards: df-probe-mut-bytes-001 (input read as 2 × each byte) EXIT=1 at
the discharge. df-311 (a `simp` recursion in the size lemma, EXIT=1) was redacted as earlier logs are. Declared first in
DECLARATIONS-DEFLATE's 81st-head addendum. **D7: HOLDS, now with no premise on the input at all.**

## Addendum 8 (2026-11-16, the 83rd vir head): K7 conjunct (2) at every capability base p
The non-author read of Addendum 6's re-score (paper, bus 11-16 08:47; object vir 4709d88) confirms it: the frozen K7 does not ask
for total correctness, since L3's R4 is a `Triple` (partial correctness, no fault). It names one LIMIT, not a falsifier:
`router_triple_x86` was stated at p = 0 while R4 and `router_x86` are general in p, and "the L3 router triple" is R4 at every p.
Run (the reader's arm (a), declared first in DECLARATIONS-K7 Addendum 8): `K7.router_triple_x86_p` (k7/K7/RouterTriple86.lean),
Addendum 6's statement at a free `p : Int` (region, R4's premises, capability words, source term, post-state). `router_triple_x86`
keeps its statement and is now its p = 0 instance (one `exact`). Same rule as Addendum 7: only `router_x86`, L3's `R4` and generic
L2 facts; the file's imports are unchanged, and none reaches `router_inR` or `router_halts`. k7-038 (the file) EXIT=0; k7-039 (the
root) EXIT=0; k7-audit-015 EXIT=0, 43 rows (42 + the new one), every row within [propext, Classical.choice, Quot.sound], 0 sorryAx.
**Red backwards:** k7-probe-mut-triple-002 (probes/MutTriple86p.lean: the post-state's p fixed at 0 against a region at p) EXIT=1,
one error, at the declared line (42:37, the final `exact hq`). All four ran at P1. **K7: HOLDS on both conjuncts, (2) now at every
p**, in partial-correctness form with OVF and RES as stated disjuncts. Logs: k7/logs 90 (53 EXIT=0, 37 EXIT=1).
