# DECLARATIONS — OBJECT-NOCHECK-ENTRY's route (predictions amend-27)

Written 2026-11-25 by the 90th vir head, BEFORE the route's first build.
- **NE6's population:** every `saltbuild EXIT=` line in `s3/logs/ne-*.log`, from `ne-001` to the first log in which `compile_entry`
  builds at EXIT=0. The router side's logs are `k7/logs/ne-r-*.log` (not in NE6).
- **The route's files** are NEW files only (NE4): `s3/S3/Contain.lean` (the chain for a program that CONTAINS a lowering's code),
  `s3/S3/Entry.lean` (the entry stub and `compile_entry`), and `k7/K7/RouterEntry.lean` (dF and its soundness). The library roots
  (`s3/S3.lean`, `k7/K7.lean`) and the Audit files gain lines.
- **NE8's instrument:** `#print` of `S3.compile_x86` and `S3.compile_x86_proved` with `pp.deepTerms`, against
  `s3/probes/nc-compile_x86-check-deep.txt` and `nc-compile_x86_proved-check-deep.txt` (8fc40b8's).

## Addendum 1 (2026-11-25, the 91st vir head, BEFORE the first build on E3's statement)
- **compile_entry / compile_entry_run on E3's interface.** Changed from 55962a3: `hdty : HasType₂ [tcap] [true] d tcap`;
  `hsound`: every finishing run of d from σ has `σ' = σ ∧ valOf w = cap p₀ ∧ NoFaultP [cap p₀] e σ` (a decider rejects by faulting,
  so finishing is accepting); the code at H is `call base_d :: loopTail env0 XF H₂` (no bool test); `2 ≤ L.bufN`; the ACCEPT
  disjunct loses its `valOf w = (cap p₀, true)` conjunct. Everything else, including (F) and AtFaultX, is byte-identical.
- **Removed from Entry.lean:** `boolChk`, `gateTail`, `bool_check`, `gate_accept`, `gate_reject` (E2's bool test), and their two Audit
  rows. They were proved at 55962a3 (ne-005..ne-018) for an interface no L2 program instantiates; 55962a3 is their record.
  `k7/probes/RouterEntryCapBool.lean` cites `S3.gateTail` and no longer builds against the tip; it is E3's record at 55962a3.
- **NE6** continues from ne-019; every build counts.
