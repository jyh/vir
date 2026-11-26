# PREDICTIONS amendment 27 — OBJECT-NOCHECK-ENTRY (the eager entry check, policy 2)

Written 2026-11-25 by the 90th vir head, in the same commit as `object-NOCHECK/OBJECT-NOCHECK-ENTRY.md`, **BEFORE any file of its
route**. **What was known when this was written:** every ref at 8fc40b8 reads **0** commits by `git log --all -S` for `NE1`, `NE4`,
`compile_entry`, `EN1`–`EN3` and `ERRATA-NOCHECK-ENTRY`. The writer built NOCHECK (RESULTS-15) and has read `Driver3.lean`'s theorem
list, R4's statement, `SvA`/`TvA`, and `RouterProved.lean`. No entry file exists. The writer is the builder; each row is a count or a
statement read from artifacts, fixed before the first file.

| id | prediction | measured by | falsified if |
|---|---|---|---|
| NE1 | `compile_entry`'s premises contain **no `P σ` and no `NoFaultP`**: only compile_x86's shape premises, the decider's read-only predicate, its soundness, and e's triple. | `#print` of the statement | either appears |
| NE2 | `compile_entry` **names no program**: its constants come from S3's, VIRC's, L2's and x86lean's namespaces only. | `#print`, the K3 harness check's form | a program constant (`F`, `dF`, DEFLATE's) |
| NE3 | Its FAULT outcome states **every live cell unchanged**, derived from the read-only predicate (fork EN3 (a)). | the statement; the predicate's use in the proof | the FAULT clause carries no memory statement, or needs a premise beyond the predicate |
| NE4 | The composition (fork EN2 (a)) **reuses Driver3's pieces**: ≥ 2 of `head_call`, `after_done`, `after_exit` are used, and **0 lines change** in existing `s3/S3/*.lean` files (new files and the library root only). | the proof's references; `git diff --numstat 8fc40b8.. -- s3/S3` over pre-existing files | < 2 used, or an existing file edited |
| NE5 | The router needs **exactly 1 router lemma** beyond the decider's definition: `dF`'s soundness against R4's precondition. | new declarations in `k7/` | > 1 |
| NE6 | **15 < builds ≤ 40**, from the first entry file to `compile_entry` at EXIT=0. | `saltbuild EXIT=` lines in the route's logs (declared before the first build) | ≤ 15, or > 40 (which fires the checkpoint) |
| NE7 | `#print axioms compile_entry` and the router instance ⊆ {propext, Classical.choice, Quot.sound}. | the Audit rows | any other axiom |
| NE8 | `compile_x86`'s and `compile_x86_proved`'s `#print` are **byte-identical** to their 8fc40b8 captures. | `#print` before and after | any byte differs |

**Directions only:** the decider `dF`'s instruction count against `lower3u F`'s 651 (reported, as the cost of one eager check against
the 80 lazy check instructions removed); whether `dF` itself needs index checks (it reads cells 7–14 of an 87-cell region, so a
proof would let it run unchecked too; reported, not pursued).
**What a falsification would mean:** NE1 or NE3 falsified means the policy's guarantee ("FAULT before any effect, no proof asked of the
caller") is not what was built: posted as the result, not routed around. NE6 low is the same finding as NC7's (an estimate by analogy
runs high on this arm).
