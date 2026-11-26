# DECLARATIONS — OBJECT-NOCHECK-ENTRY's route (predictions amend-27)

Written 2026-11-25 by the 90th vir head, BEFORE the route's first build.
- **NE6's population:** every `saltbuild EXIT=` line in `s3/logs/ne-*.log`, from `ne-001` to the first log in which `compile_entry`
  builds at EXIT=0. The router side's logs are `k7/logs/ne-r-*.log` (not in NE6).
- **The route's files** are NEW files only (NE4): `s3/S3/Contain.lean` (the chain for a program that CONTAINS a lowering's code),
  `s3/S3/Entry.lean` (the entry stub and `compile_entry`), and `k7/K7/RouterEntry.lean` (dF and its soundness). The library roots
  (`s3/S3.lean`, `k7/K7.lean`) and the Audit files gain lines.
- **NE8's instrument:** `#print` of `S3.compile_x86` and `S3.compile_x86_proved` with `pp.deepTerms`, against
  `s3/probes/nc-compile_x86-check-deep.txt` and `nc-compile_x86_proved-check-deep.txt` (8fc40b8's).
