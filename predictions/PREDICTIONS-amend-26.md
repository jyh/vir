# PREDICTIONS amendment 26 — OBJECT-NOCHECK (proved programs compile with no index checks)

Written 2026-11-25 by the 90th vir head, in the same commit as `object-NOCHECK/OBJECT-NOCHECK.md`, **BEFORE any file of its route**.
The object was ruled at the 11-25 council (option (iv), *"Yes, accept rec"*).

**What was known when this was written.** Every ref of this repository at origin/master e3a8181, by `git log --all -S`: **0** commits
for `lower3u`, `NC1`, `NC5`; **1** each for `NoFault` (8c9aac2, a Y5 mutant's prose, unrelated) and `compile_x86_proved` (5f2f9cf,
the REVIEW's description of this option). Control: `lower3` = 28. The writer has read `compile_x86` (Cross3.lean), `gen`'s
load/store cases (Lower3.lean), `stepW` (Word.lean), `Triple` (Logic.lean), Converse.lean's header and statement list, and
`K7.router_triple_x86`. No route file exists. **The writer is also the builder** (as for every Lean-arm row since amend-1); the
defence is the same: each row is a count or a statement read from artifacts, fixed before the first file.

**The 11-06 rule binds:** past ~100 tactic applications in one proof, the arm stops and systematizes.

| id | prediction | measured by | falsified if |
|---|---|---|---|
| NC1 | NC-W is DERIVED (fork N1 (a)): **0 lines changed under `compiler/VIRC/`** by any NOCHECK commit. | `git diff --stat e3a8181..<NC-S sha> -- compiler/VIRC` | any line changed there |
| NC2 | For every program, `lower3u`'s instruction list is `lower3`'s with **exactly 4 instructions removed per `load` site and per `store` site** (`test`, `js`, `cmp`, `jge`) and no other change; on the router F (K7's term), the length difference is **4 × (its load + store sites)**. | an `#eval` over F's two lowerings, committed with its output; the `gen` cases at their sha | any other instruction differs, or the count differs |
| NC3 | `compile_x86_proved`'s premises are **exactly compile_x86's, plus NC-P**: one hypothesis more, none different. | `#print` of both statements, diffed by the harness | any other added or changed hypothesis |
| NC4 | `compile_x86_proved`'s statement contains **0 occurrences of `.fault`** and has **two** clauses (compile_x86's (1) and (3)). | the `#print` text, token count | a `.fault` token, or a third clause |
| NC5 | **`compile_x86`'s statement is byte-identical** at its `#print` before and after NOCHECK (fork N2 (a) keeps `ctxOf`'s meaning). | `#print S3.compile_x86` at e3a8181 vs at the NC-S sha | any byte differs |
| NC6 | The router triple is carried through `compile_x86_proved` with NC-P discharged from its L3 triple, **0 new router-specific lemmas** (only K7's existing ones are used). | the K7-side theorem at its sha; new declarations in `k7/` named for the router | a new router lemma beyond the theorem itself |
| NC7 | **40 < builds ≤ 80**, from the first NOCHECK route file to `compile_x86_proved` at EXIT=0 (the REVIEW's price). | `saltbuild EXIT=` lines in the route's `logs/` | ≤ 40, or > 80 (which also fires §4's checkpoint) |
| NC8 | No translation-validation fallback is used: `compile_x86_proved` is one ∀-program theorem. | its statement | a per-program premise beyond NC-P |
| NC9 | `#print axioms compile_x86_proved` ⊆ {propext, Classical.choice, Quot.sound}. | the route's Audit row | any other axiom, `sorryAx` included |

**Directions only, no thresholds:** whether fork N1 (a) needs a determinism lemma for `stepW` beyond what S3 already proves
(reported); how many of Sim3's lemmas take the `chk` flag (reported, as the proof cost of deleting four instructions).
**What a falsification would mean:** NC1 falsified (fork N1 needed (b)) is a finding about the stage theorems' shape, posted, not
routed around. NC5 falsified means the unproved-program path changed, against policy 3, and stops the route until it is restored.
