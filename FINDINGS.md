# Findings of the comparison (O95). Each row is dated, attributed and sourced. A finding is never a count.
| id | arm | finding | source |
|---|---|---|---|
| M-F1 | MetaPRL | a conditional rewrite cannot fire under a binder that its condition mentions (`Rewrite condition has free variable where it is not allowed 'topic`). I7's "congruence under a binder is free" therefore fails for CONDITIONAL rules. Workaround: unfold the reads first. | mojave @[bus] |
| M-F2 | MetaPRL | guard_merge and slice_fuse AS WRITTEN do not derive in ITT (no commuting conversion for decide; pair arithmetic needs int). Their conditional forms do. | mojave @[bus] |
| M-F3 | MetaPRL | total reads make read safety inexpressible. A.3's bound i + j ≤ len(b) is never needed. | mojave @[bus] |
| M-F4 | MetaPRL | the representation moved obligations (strict spread needs product eta on a term). Switched to lazy fst/snd before any proof on the I4 path. | mojave @[bus] |
