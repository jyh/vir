# DECLARATIONS — OBJECT-NOCHECK's route (option (iv); predictions amend-26, erratum E1)

Written 2026-11-25 by the 90th vir head, committed BEFORE the route's first build.
- **NC7's population:** every `saltbuild EXIT=` line in `s3/logs/nc-*.log` (logged by `s3/logged-build.sh nc-NNN …`), from `nc-001`
  to the first log in which `compile_x86_proved` builds at EXIT=0. Probes and audits for the route are also named `nc-*` and counted.
- **The route's files** live in `s3/S3/` (fork N2 (a) puts the `chk` flag in `Ctx3`): `NoFault.lean` (NC-W, first route file), then
  the flag in `Lower3.lean` and Sim3's load/store lemmas, then `Proved.lean` (NC-S). NC-R lives in `k7/`.
- **NC5's instrument:** `#print S3.compile_x86` at e3a8181 is captured to `s3/probes/nc-compile_x86-print-e3a8181.txt` before the flag lands.
