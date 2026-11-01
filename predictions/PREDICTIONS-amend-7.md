# Amendment 7 (2026-11-01, the 2nd vir head): the L-F4 test (STATUS-vir row 15), PREREGISTERED BEFORE THE VARIANT IS BUILT

⚠️ This file was written AFTER program 2's L-IDX and L-DEEP chains were green, and BEFORE any line of the Int-offset variant existed. It predicts only that variant. No threshold in any earlier file changes.

**The variant (L-IDX-Z):** program 2's shallow L-IDX chain (`router2_fusion`, Router2.lean) restated with the slice length and every offset as `Int` (as in mojave's model B). It uses a `SliceZ (n : Int)` and an `advanceZ` whose precondition is `0 ≤ i ∧ i ≤ n`, with J2–J4 unchanged. It lives in its own file. Router2.lean is not edited.

**The question L-F4 raises:** does `aux_advance_idx`, the rewrite `advance{b; 12 + (off − 12)} = advance{b; off}`, VANISH with Int offsets?

**Prediction R1 (preregistered answer: NO, it does not vanish as a rule, but it becomes CONTEXT-FREE):**
- (a) The rule is still USED in the variant's scored chain. slice_fuse still yields the index `12 + (off − 12)`, which is not syntactically `off`, and the two slice types differ, so a rewrite is still needed. ⇒ the variant's aux rules used (`P2Z.C3`) = program 2's `P2.C3` (6). **FALSIFIED if** P2Z.C3 < P2.C3, i.e. if the index rewrite is not needed at all.
- (b) Its side condition no longer depends on an enclosing guard. **The mechanical test is to CLEAR the payload guard's hypothesis before the side proof** (`by clear h2; omega`). With Int offsets this still builds. **FALSIFIED if** it does not build.
- (c) Control, red-backwards: the SAME `clear` applied to the Nat chain (Router2.lean's `aux_advance_idx` side proof, in a scratch copy) must FAIL to build. If the Nat chain also builds with the guard cleared, then (b) tests nothing and L-F4 as stated is refuted.
- (d) No direction is predicted for C1heq, C2cond or C5chain. They are reported as exploratory beside the verdict.

**What would refute L-F4 outright:** (c) builds, which would mean the Nat chain never needed the guard.
**What would refute R1 in L-F4's favour (L-F4's strong form, "the rewrite vanishes"):** (a) is falsified.
