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

⚠️ *Annotation (rows 430–433):* this table omits `l1/AuditInduction.lean`, and "to re-check, re-run the drive" is now one
command. See the addendum below, whose table is the script's output.

## Addendum 2026-11-25 (rows 430–433): the census as a command

The table above is a transcription. It is now reproducible by one command, `harness/triple_drive.py`, which derives the
population from the tracked tree (every `lakefile.toml`, every `Audit*.lean` beside it), drives build → `AuditControl.lean` →
each audit through the project's `logged-build.sh` into a scratch `LOGDIR`, gates each audit with `axiom_gate.py`, and prints
the table below. To re-check: `PRIO=P1 SEAT=<seat> python3 harness/triple_drive.py <scratch dir outside the repo>` (it builds);
`--dry-run` prints the population without building, and `harness/reproduce.sh` runs that dry run.

**What the first drive found (drive-430, 14/17 OK, every saltbuild EXIT=0):**
- `l1/AuditInduction.lean` (amend-19) was **not in the table above**: the hand census drove `Audit.lean` only. Its imports
  include `VIRL1.Induction`, which `lake build VIRL1` does not build, so its gate read `imports NOT BUILT` (rc 1). The drive
  now builds every in-repo module an audit imports.
- k5 and k7 logged **zero** `#print axioms` rows at EXIT=0: `k5/tools/replay_filter.py` folded the audit's rows into the last
  replayed-warning block, because saltbuild now builds an audit's imports first. `axiom_gate.py` read them EMPTY (rc 2), so
  nothing passed on them. Fixed in the filter (`k5/LOGS-FILTER.md`, addendum 2026-11-25; selftest ARM68).

**The drive after both fixes (drive-433), output verbatim except the scratch path:**

```
# population: 15 projects, 17 audits (from tracked lakefile.toml + Audit*.lean)
project	targets	audit	rows	verdict	gate_rc
bridge	VIRBridge	Audit.lean	8	OK	0
compiler	VIRC	Audit.lean	29	OK	0
compose	Compose	Audit.lean	30	OK	0
deflate	VIRDeflate	Audit.lean	635	OK	0
k5	K5	Audit.lean	78	OK	0
k7	K7	Audit.lean	43	OK	0
l1	VIRL1 VIRL1.Induction	Audit.lean	40	OK	0
l1	VIRL1 VIRL1.Induction	AuditInduction.lean	5	OK	0
l2	VIRL2	Audit.lean	205	OK	0
l3	VIRL3	Audit.lean	14	OK	0
l4	VIRL4	Audit.lean	157	OK	0
l5	VIRL5	Audit.lean	243	OK	0
lean	VIR VIRB	Audit.lean	18	OK	0
lean	VIR VIRB	AuditBP.lean	7	OK	0
s3	S3	Audit.lean	94	OK	0
virp	VIRP	Audit.lean	32	OK	0
x86compose	X86Compose	Audit.lean	4	OK	0
TRIPLE-DRIVE 17/17 OK  projects=15  logs=<scratch>  (limits: gates only the names each audit prints; src = this repo's library sources, not .lake/packages; one drive at one source state)
```

47 saltbuild runs, all `saltbuild EXIT=0`, every one on a P1 ticket. The row counts equal the table above for every audit it
lists; AuditInduction (5 rows) is new.

**Limits, revised:** the logs are still not in the repo (C6 counts logged runs, and a census drive is not one of them), so the
table is the script's output at one source state, not a count recomputed from committed artifacts. The difference from the
transcription above is that re-checking it is one command, run by anyone, and a malformed project is refused by name.
