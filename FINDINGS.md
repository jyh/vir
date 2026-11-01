# Findings of the comparison (O95). Each row is dated, attributed and sourced. A finding is never a count.
| id | arm | finding | source |
|---|---|---|---|
| M-F1 | MetaPRL | a conditional rewrite cannot fire under a binder that its condition mentions (`Rewrite condition has free variable where it is not allowed 'topic`). I7's "congruence under a binder is free" therefore fails for CONDITIONAL rules. Workaround: unfold the reads first. | mojave @[bus] |
| M-F2 | MetaPRL | guard_merge and slice_fuse AS WRITTEN do not derive in ITT (no commuting conversion for decide; pair arithmetic needs int). Their conditional forms do. | mojave @[bus] |
| M-F3 | MetaPRL | total reads make read safety inexpressible. A.3's bound i + j ≤ len(b) is never needed. | mojave @[bus] |
| M-F4 | MetaPRL | the representation moved obligations (strict spread needs product eta on a term). Switched to lazy fst/snd before any proof on the I4 path. | mojave @[bus] |
| M-D1 | MetaPRL | a module whose summary id is ≥ 2^30 cannot load its text archive (`Filter_summary.dest_id: not an int`); vir2 is stored as .prlb; fix is metaprl #88 | mojave @[bus] / @[bus] |
| M-D2 | MetaPRL | the mp shell fails past ~1,024 chars per phrase; mpdrive now refuses > 1,000 | mojave @[bus] |
| M-D3 | MetaPRL | an `export ()` after a failed step overwrote program 1's committed .prla (restored from git; verdict green); mpdrive now refuses export after an error | mojave @[bus] |
| L-F4 | Lean | Nat truncated subtraction manufactures a context-dependent rewrite that Int offsets do not. **Refined (row 15, amend-7 R1 HOLDS): with Int offsets the rewrite is still needed, and only its CONTEXT dependence goes away** | vir RESULTS-2 |
| L-F5 | Lean | the HEq cost is fixed per representation and does not grow with dynamic indices (program 2 = program 1 = 20) | vir RESULTS-2 |
| V-F1 | harness | the C1 class missed `≍` (HEq's notation): program 1 C1heq read 5, true 20 — vir's own needle defect | vir RESULTS-2 §0 |
