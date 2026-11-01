# Amendment 8 (2026-11-01, the 2nd vir head): the DEEP STATEMENT CONTROL (STATUS-vir row 18), PREREGISTERED BEFORE THE VARIANT IS BUILT

⚠️ This file was written AFTER program 2's L-DEEP chain (Deep2.lean) was green, and BEFORE any line of this variant existed. It predicts only that variant. No earlier threshold changes.

**The question (RESULTS-2 addendum 4, second control):** the deep chain has two context-dependent rules, and both take their side condition from the context. `aux_le_len_adv` takes `len(b0) ≥ 24` from the OUTER guard. Is that dependence a fact about the program or only a choice in how the rule was stated?

**The variant (L-DEEP-S):** a new file in which `aux_le_len_adv` is replaced by `aux_le_len_adv_own`. It rewrites `advance{b; i; s. guard{m ≤ y ∧ y + z ≤ len(s) + i; …}}` to `…len(b)…` under the premise **i < m** (a Nat fact about literals, with NO `Holds` premise). The guard's own conjunct `m ≤ y` carries the truncation case. Every other rule and the chain's shape are Deep2's. Deep2.lean is not edited.

**Prediction S1 (preregistered answer: YES, it is a statement choice):**
- (a) The variant's chain builds under saltbuild. **FALSIFIED if** the own-conjunct rule cannot be proved SOUND (its `Step.sound` case fails) or the chain does not build.
- (b) The variant still uses the same number of aux rules: P2S.C3deep = 7. The rule is still needed, and only its premise changes. **FALSIFIED if** ≠ 7.
- (c) Context use falls from 2 `Holds` premises in the chain to 1, and the 1 left is `aux_advance_idx`'s (counted as `.mem` occurrences in the scored block). **FALSIFIED if** it is not 1.
- (d) The strictness is load-bearing. With `i ≤ m` in place of `i < m`, the soundness proof FAILS, because at m = i, y = i, z = 0, len(b) < i the two guards disagree. This is a control, run red-backwards in a scratch copy.
