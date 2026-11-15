# STAGE-S3: the compiler's x86 stage (word code → x86lean `Program` over `stepP`), readings

**Written 2026-11-15 by the 79th vir head.** The source record for RESULTS-12's S3 cells (amend-23 §K). Every reading names the
artifact it was read from and how, so it can be re-read without asking. The declarations are compiler/DECLARATIONS-S3.md (main
text + Addenda 1–15, each written before its file); the project is s3/ (lib S3; x86lean by git at paris/c3-effects 4f08f91;
compiler and bridge by path).

## The theorems
- **`S3.s3_refines_from_s2`** (s3/S3/Sem3.lean): for `lower3 ilen tbl main base`, every word run of S2's machine from main's
  start is matched by an x86lean `stepP` run reaching R3 at its end in ≥ n + 3 steps, or returning RES at a reached word state
  whose `ResWhy` holds (ENV or STACK outgrown). Premises: the layout (`L.Ok`, canonical addresses, the stub's return point),
  `DriverCall`, Fragment3's static clauses (1 ≤ ilen; code < 2⁶⁴ bytes; table < 2⁶⁴ entries; `needW` of main and every body ≤
  |BUF|), S2's `SRel` at the start, L.live ⊇ the start store's live cells.
- **`S3.compile_x86`** (s3/S3/Cross3.lean, Addendum 15): S1 ∘ S2 ∘ S3 about the SOURCE program `instL 0 vs e`: (1) a run that
  finishes with `ret a` ends, after mm machine steps, R3-related to `done ws` with ws related to a's value (returned stDone, r13 =
  |ws|, the words at BUF) or to OVF; (2) a run that faults ends R3-related to FAULT or OVF; (3) n source steps are matched by mm ≥ n
  machine steps or a stop at OVF; in every clause RES (with `ResWhy`) is the other exit. No premise beyond the union of the stages'.

## Readings against amend-23 §K
- **K2 for S3: HOLDS.** `s3_refines_from_s2` and `compile_x86` quantify over `tbl`, `main` (resp. `e`); no statement is about one
  output. With S1 and S2 (STAGE-S1, STAGE-S2), each stage is one ∀-program theorem.
- **K4: FALSIFIED.** Population: the instruction constructors in S3's code generator, s3/S3/Lower3.lean (the only file defining
  `gen`, `arithCode`, `evalTo`, `envRoom`, `prependBuf`, `stackRoom`, `prependLoop`, `dispatch*`, `exitCode`, `entryStub`,
  `lower3`). Method: every constructor of x86lean's `Op` (X86/Syntax.lean:1526 at 4f08f91, 110 constructors, the list derived
  from the file) counted in Lower3.lean, then `.bin` kinds separately. Emitted: mov, lea, add, sub, and, or, cmp, test, jcc, jmp,
  call, ret (all §3), imul, setcc (declared at the pin), and **push, pop** (`entryStub` line 232 and `gen`'s `letE`, lines
  181/183: r12 saved across the call) and **cmovle** (`arithCode` line 93, `max`). The three were declared in DECLARATIONS-S3's
  main text (the `max` and `letE` bullets) before the code, and are outside §3 ∪ {imul, setcc, jo}. The entry stub is in every
  lowered program, so push/pop is emitted for every program, not only for max or letE. All three are x86lean `Op`s that `stepP`
  executes, and each has a T-exact row in x86lean's docs/COVERAGE.md at 4f08f91 (`push` r q, `pop` r q, `cmovcc`; read by
  the row text, not re-run), so the finding is about the prediction's list, not about an unvalidated instruction.
- **K3: the tool reads FALSIFIED; the author reads HOLDS on the prediction's words; a NON-AUTHOR call is owed.** The driver theorem
  is `S3.driver_x86` (s3/S3/Driver3.lean, DECLARATIONS-DRIVER Addenda 4–5; s3-130 EXIT=0; audit s3-audit-018 86/86 within the
  three). `k5/tools/k3_check.py` over k7/logs/k7-probe-K3-003.log (derived whitelist VIRC · VIRL1 · VIRL2 · X86): **FALSIFIED**,
  100 constants, offending only `S3.*` (21 names: AtHead, CodeAt, Ctx3, Lay3 and its fields, allCode, bytes, ctxOf, loopCode,
  lower3, needW, rd, stubHead) and `VIRBridge.Live`. `S3.compile_x86` reads the same way (S3.* and VIRBridge.Live). The positive
  control `K7.router_x86` reads FALSIFIED with `VIRL3.F` and `K5.*` among its offenders, so the check separates a statement about
  the router from one that is not. **No constant of DEFLATE or the router** (VIRL3 · K5 · K7 · VIRDeflate) is in driver_x86's
  statement. amend-23 K3 says the constants are drawn from "the compiler's, L2's and x86lean's namespaces"; S3 (the compiler's x86
  stage, DECLARATIONS-S3) and VIRBridge (its word↔byte bridge, DECLARATIONS-S3-bridge) are the compiler's own, born after the
  whitelist was typed. Whether they count is a reading the author does not make for himself after the result: the precedent
  (driver_l2, row 307) MOVED definitions into VIRC rather than widen the list. The tool's verdict stands as the score until a
  non-author rules.
- **K7: OWED.** K7-b1 `router_x86` (k7/STAGE-K7.md) carries compile_x86 to the router; the five exits witnessed is K7-b2.

## Runs
s3/logs through s3-118 and s3-audit-016: 136 logs (118 builds `s3-NNN`, 18 audits and controls), 136 `saltbuild EXIT=` lines
(73 EXIT=0, 63 EXIT=1), counted by `cat s3/logs/*.log | grep -h 'saltbuild EXIT=' | sort | uniq -c`. The plan's S3 guess was ~60
builds (OBJECT-COMPILER §4); no amend-23 row predicts S3's build count. `compile_x86`: s3-117 EXIT=0 (s3-116 red: `Op` ambiguous
between X86 and VIRL2); audit s3-audit-016 78/78 within propext · Classical.choice · Quot.sound (`axiom_gate.py --no-control`
rc 0; positive control s3-audit-control-002 sorryAx, rc 0; s3-audit-015 red: the root olean predated the import, rebuilt s3-118).
