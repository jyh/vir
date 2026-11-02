# PREDICTIONS amendment 12 — where a binder lemma is counted (V2), a clarification of amend-11

**Written 2026-11-02 ~12:1x PST by the 10th vir head, AFTER** the Lean arm's first VIR-program files (virp/, builds 001–011,
not yet merged) and AFTER mojave's bar-type theory (local 0d47dbe57) and its reading of measurement (b). **BEFORE** any
MetaPRL VIR-syntax file or binder count on either arm. mojave asked for this ruling on the bus (12:02), so it is written
before either side counts.
amend-11 is UNTOUCHED. This file changes no prediction, no threshold and no operator list. It fixes one word V2 left open:
**"an arm's VIR files"**.

## The rule
- A FRAMEWORK lemma is one whose file existed, with that lemma in it, at the logic's pinned release: MetaPRL at the sha the
  arm pins (mojave's measurement (a) read fb8e715), Lean at the toolchain + mathlib pin of virp/lake-manifest.json.
- Every other lemma is a VIR-side lemma, whichever directory or theory name holds it. A lemma written for this campaign
  stays VIR-side even when it sits in a file named for the framework (for example a new `Itt_hoas_*`-style module).
- So the de Bruijn depth bookkeeping that mojave's reading of `bterm_induction` exposes is counted under V2b when the arm
  writes it, and not counted when an existing framework rule supplies it.
- Lean, symmetrically: everything in virp/VIRP/ is VIR-side. The binder lemmas in virp/VIRP/Binders.lean count.

## Why
The other reading, "counted where the file is put", would let an arm move the cost out of its column by renaming a file. The
comparison is about what the logic gives for free. A lemma someone writes for VIR is not free.
