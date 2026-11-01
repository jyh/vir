# Amendment 9 (2026-11-01, the 2nd vir head): the PROGRAM 3 L-FLAT control (STATUS-vir row 25), PREREGISTERED BEFORE THE VARIANT IS BUILT

⚠️ This file was written AFTER program 3's Lean arm (`route_acl_safe`, C1coe 54) was green, and BEFORE any line of this variant existed. It predicts only that variant. PREDICTIONS-program3's T1–T5 are unchanged and are scored on `route_acl_safe` alone.

**The variant:** `route_acl_safe_flat (b : WireBuf) (hv : 24 ≤ b.size ∧ wireRd b 0 = MAGIC) (st)`, with the same conclusion over `wholeSlice b`. A.1's ValidFrame becomes a hypothesis on a bare buffer, not a subtype, so there is no `.val`.
**The extractor, fixed by this file's commit:** P3F.C1coe = the same class as C1coe (↑ · .val · Subtype.val · .property) over the elaborated term of `theorem VIR.route_acl_safe_flat`.

- **F1 (the 54 is a representation choice, P1b's shape for the boundary):** P3F.C1coe = 0. **FALSIFIED if** ≥ 1.
- **F2 (the validity hypothesis carries no load in K3):** the variant builds with `hv` CLEARED before the proof (`clear hv`). F2 checks the length and the magic itself, so ValidFrame's refinement is never used. **FALSIFIED if** it does not build. *(Already visible, and therefore not a test, is that `.property` is 0 in route_acl_safe's term. The test is `clear`.)*
- **F3 (exploratory):** the proof script is the same text as route_acl_safe's (C5chain equal, 38).
