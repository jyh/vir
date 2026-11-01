# PREDICTIONS amendment 10 — the typing-style amendment B → B′ (2026-11-01, 8th vir head)

**Written AFTER the MetaPRL arm's B′ proofs of all three programs** (mojave, branch `mojave/vir-arm-bprime`, tools
bae7fbe, 14:45–14:58 PST) and after its A.2 transcription check. **Written BEFORE any Lean B′ file exists:** at the commit
that adds this file, `lean/` holds no carrier, no B′ module and no A.2 parser (`git ls-files lean | grep -ic carrier` = 0).
P1–P5, Q1–Q5, T1–T5 and amendments 1–9 are UNTOUCHED. This file adds a second scoring of the same programs. It is not a
replacement for the first.

## What B′ is (the style rulings, council 2026-11-01 §A)
- MetaPRL: theorems are rules with `[wf]` subgoals, registered in `intro`. There is no `top`: the carriers are typed
  (`wirebuf = list{int}`, `vslice = wirebuf × int`, declared `state` and `verr`). The I1 operators are `prim`s that state
  only their typing. Every defined term gets a proved wf rule in `intro`, and the theorems carry no typing premises.
- Lean (the mirror, built by vir): the same split between UNINTERPRETED and DEFINED, fixed here before the first proof.
  - UNINTERPRETED, as fields of ONE structure `Carrier` that every B′ theorem takes as an argument: the state type, and the
    operators `wire_u32 · can_access · has_tokens · dec_tokens · take` with the drop codes. They are fields, never `axiom`s.
  - DEFINED, as in the shallow embedding: `vlen · advance · read_u32` and everything built from them. The I1 slice and
    read laws are therefore THEOREMS, exactly as on the MetaPRL side, and are never stated as fields.
  - The wire is `List Int`. The slice is the flat pair (wire, offset), mirroring `vslice`, so the Lean B′ arm is UNINDEXED.
- An A.2 PARSER (Lean): A.2's surface text (I2's specs, I3's U, A.3's F, program 2's J2–J4) is parsed into the deep
  embedding. The parse is compared with the hand-written deep terms by `decide`/`rfl`. A difference is a finding.

## Re-score rules (each count keeps its amend-1..9 definition; the B′ artifacts are its input)
- **C4vir (new column, I5's "axioms of the VIR"):** MetaPRL = the `prim` declarations in `vir*.ml` on the B′ branch.
  Lean = the operator and type fields of `Carrier`. Codes and carriers count on both sides, one each.
- C4 stays the arm's OWN extra axioms beyond the logic and beyond C4vir.
- MetaPRL figures on B′ are POST-PROOF readings. Every MetaPRL B′ verdict below is EXPLORATORY, and only the Lean side is
  predicted.

## Predictions (Lean B′ mirror, pinned before its first proof)
- **B1.** On program 1, Lean B′ C1heq = 0, because the B′ slice is unindexed (the P1b reasoning, now on the B′ carrier).
  **FALSIFIED if** C1heq ≥ 1.
- **B2.** C4vir is EQUAL on the two arms for program 1's module (8 on MetaPRL: `state`, `verr`, four operators, two codes).
  **FALSIFIED if** they differ. If the Lean side needs a field the MetaPRL side does not, or the reverse, that is the finding.
- **B3.** Both arms keep C4 = 0 under B′. **FALSIFIED for an arm if** C4 ≥ 1.
- **B4 (transcription).** The Lean parser reproduces every hand-written deep term of programs 1–2 (I2 · I3 · A.3's F · J2–J4).
  A mutant that swaps one read offset is RED. **FALSIFIED if** any parse differs from its hand-written term, or if the
  mutant stays green.
- C1–C3, C5, C6 on the Lean B′ mirror: no direction. Reported beside B's figures.

## What would show this amendment unfair
A Lean field with no MetaPRL counterpart that is added silently · a Lean B′ proof committed before this file · the
MetaPRL B′ figures quoted as predicted.
