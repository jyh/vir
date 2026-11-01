# Amendment 3 to PREDICTIONS.md (2026-11-01 00:3x, vir), C3: what counts as an aux rule

⚠️ **WRITTEN AFTER THE METAPRL ARM'S FIRST GREEN ON I4** (mojave @[bus], 00:25:59), on a ruling mojave asked for and did not score itself.
The Lean arm's I4 proof was written and committed earlier (vir e2fc1f4, 00:4x local commit, before this post arrived) and is not changed by this amendment.

## The question
mojave's chain unfolds the model's `read_u32` definition. That unfold is not one of the 7 given rules and not a stated aux rule. Does it count in C3?

## The ruling (both arms)
- Unfolding the DEFINITION OF AN A.2 FORM (guard · read_u32 · advance · let_lin · let_atom · return · drop) as a chain step **COUNTS as an aux rule**, once for each distinct form unfolded. Such a step replaces an E8 commutation by the model's own semantics, which is what an aux rule is. The Lean side is treated the same way: `aux_read_past_guard` and `aux_advance_past_guard` are proved by `rfl`, i.e. they ARE form unfolds, and they are counted.
- Unfolding U, F or the I2 spec bodies does **NOT** count. That is the inlining I2–I3 supply, the role [beta_lin] plays in A.2.
- Congruence under a binder stays free (I7). Where a logic CANNOT do it (MetaPRL F1: a conditional rewrite cannot fire under a binder its condition mentions), the workaround is counted by whichever count it falls under, and the failure is a FINDING.

## Scoring, with the limit beside it
P3 is scored on C3 under this ruling. **Because the ruling came after one arm's proof, every result reports BOTH readings:** `C3` (this ruling) and `C3strict` (only stated `aux_*` lemmas). A reader who rejects the ruling can score P3 on `C3strict`, and it decides P3 differently for the MetaPRL arm (3 vs 2).
