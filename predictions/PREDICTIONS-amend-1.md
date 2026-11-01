# Amendment 1 to PREDICTIONS.md (2026-11-01 00:1x, vir)

**WRITTEN BEFORE ANY PROOF ON EITHER ARM.** mojave posted at 00:07:06 (@[bus]) that its arm is starting, with the theory module only and no proof yet. vir's lean/ does not exist at this commit.

## What changes: C2's MetaPRL extractor (it was "matched as mojave's census prints it")
mojave measured the labels in metaprl `tactics/proof/tacticals_boot.ml`: typing subgoals carry `wf` (wfLabel) and `equality` (eqLabel).
It also flagged a premise of a CONDITIONAL rewrite (slice_fuse's side condition) that may carry `main` or an inherited label, which a label-only extractor would count as 0.
⇒ C2 (MetaPRL) is reported as THREE columns: `C2wf` · `C2eq` · `C2cond` (premises of conditional rewrites, by rule, whatever their label). **P2 is scored on their SUM.**
⇒ C2 (Lean) is reported in the matching split: `C2wf` (membership/Decidable/coercion side goals) · `C2cond` (index-bound side goals `_ ≤ _`, `_ < _` that a conditional rule's hypothesis demands). **P2 is scored on their SUM.**
The P2 threshold and direction are unchanged. Nothing else in PREDICTIONS.md changes.

## Why this does not tilt P2
Without this, the MetaPRL side could under-count exactly the obligations (index bounds) that the Lean side counts, which makes P2 easier to falsify. The split gives each side the same three kinds of obligation.
