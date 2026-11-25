# The axiom TRIPLE, driven on every project (2026-11-25)

**What this shows:** `harness/axiom_gate.py` (the TRIPLE form, since 54e650c) accepts a real receipt from every one of the 15
lake projects in this repo. 14 had a `logged-build.sh`; compose/ had none until this drive gave it one (row 428). Before this drive, only l1 had been driven for real
(row 419). **What it does not show:** that any recorded log in a `logs/` directory is a triple. Receipts taken before
2026-11-23 are the old PAIR and are read with `--legacy-pair` (RESULTS-3, row 46 annotation).

**How:** for each project, `logged-build.sh` ran a real saltbuild at PRIO=P1 with `LOGDIR` set to a scratch directory
outside the repo, so no counted `logs/` changed and C6 is unaffected. The order was build (the lib targets), then
`Audit.lean`, then `AuditControl.lean`, then `axiom_gate.py AUDIT --build BUILD --control CONTROL`. Every saltbuild
read `EXIT=0`. Library sources: `src=67ee7fc71a9d0121` (268 files, the repo-wide hash) in every header.

| project | lib target(s) | audit | rows | gate | note |
|---|---|---|---|---|---|
| l1 | VIRL1 | Audit.lean | 40 | OK rc 0 | row 419 (87th head) |
| l2 | VIRL2 | Audit.lean | 205 | OK rc 0 | reds rc 1 each: no `--build`; audit log as `--build`; src mutated |
| l3 | VIRL3 | Audit.lean | 14 | OK rc 0 | |
| l4 | VIRL4 | Audit.lean | 157 | OK rc 0 | |
| l5 | VIRL5 | Audit.lean | 243 | OK rc 0 | |
| virp | VIRP | Audit.lean | 32 | OK rc 0 | |
| bridge | VIRBridge | Audit.lean | 8 | OK rc 0 | |
| compiler | VIRC | Audit.lean | 29 | OK rc 0 | |
| deflate | VIRDeflate | Audit.lean | 635 | OK rc 0 | |
| k5 | K5 | Audit.lean | 78 | OK rc 0 | |
| k7 | K7 | Audit.lean | 43 | OK rc 0 | |
| s3 | S3 | Audit.lean | 94 | OK rc 0 | |
| lean (VIR, VIRB) | VIR VIRB | Audit.lean | 18 | OK rc 0 | built from `lean/` by `lean/VIRB/logged-build.sh` |
| lean (VIR, VIRB) | VIR VIRB | AuditBP.lean | 7 | **FAIL rc 1 → OK rc 0** | in-file control is `control_sorry_bp`; fixed by `--in-file-control` (e355221) |
| x86compose | X86Compose | Audit.lean | 4 | **FAIL rc 1 → OK rc 0** | IMPORTED CONTROL MISSING; fixed by `x86compose/AuditControl.lean` (49f6fbe) |
| compose | Compose | Audit.lean | 30 | **FAIL rc 1 → OK rc 0** | no wrapper, so no header and no imported control (red on its recorded audit-008 + build-024); fixed by `compose/logged-build.sh` + `compose/AuditControl.lean` (row 428); 30 rows = audit-008's |

The three refusals were defects in the receipt setup, not in any proof. Each fix went red first (x86compose and AuditBP in #96, merge 4765516; compose in row 428).
A receipt for `lean/AuditBP.lean` is
`axiom_gate.py AUDIT --build BUILD --control CONTROL --in-file-control control_sorry_bp`.

**Limits:** this is one drive at one source state (master 78a830d, plus the fixes above). The scratch logs are not in the
repo, so this table is the author's transcription of their `AXIOM-GATE` lines, not a count anyone can reproduce from
the artifacts. To re-check, re-run the drive. The gate reads logs and does not re-run Lean; it gates only the names
an audit file prints.
