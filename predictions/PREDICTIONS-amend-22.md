# PREDICTIONS amendment 22 — the SLang prediction note (encoding against tooling), before the SLang phase

Written 2026-11-06 by the 25th vir head, on the 11-06 council's order: *"pin SL5(a)(b) and write a one-page PREDICTION NOTE before
the SLang phase runs: the gaps, the parts ledger, the encoding and tooling hypotheses, and a stated prediction for SLang."*
**Written BEFORE the MetaPRL arm's first SLang file.** `git log --all -S` over the MetaPRL arm's own working clone (the one holding mojave/vir-l2, tip 54a2abe21)
reads 0 commits for `SLang`, `L1SLang` and `ssig1` (control `y5` 63, `wfs2` 27), and amend-20
(PUBLIC #40, bd0f3be) is the only file that states the sorted language. **Written AFTER** the MetaPRL arm's L2 Y5 steps 1–8 in
progress (parts through 118g, 11-06 09:11) and the three domain gaps below. So no clause here can claim to be blind to them.

## 1. SL5(a)(b) are pinned as amend-20 states them, and are not re-read
(a) the L1 stage's C5 ≤ **25,332** tokens. (b) the framework stage plus the L1 stage ≤ **69,794** tokens. Both bounds come from
amend-19's measured U = 19,130 and S = 50,664 (RESULTS-9 I5), and were committed at bd0f3be before any SLang file. This note does
not move them. Against Lean's 509 tokens (RESULTS-9 I3), (a)'s bound is 49.8× and (b)'s is 137.1×.

## 2. What is on record (the gaps and the parts ledger)
- **Three domain gaps in MetaPRL's L2 Y5**, each closed by a CARVING on Y5 and its invariant, a predicate that cuts the encoding
  down to the object's terms: D8 (grammar sorts, `wfs2`), D9 (name scoping, `scoped`) and D8a (a prim's arity, carved into D8).
  Lean's L2 arm needs none of them: mutual inductive types, de Bruijn contexts and a usage mask give the same facts by
  construction. The counterexamples (FINDINGS M-F9–M-F11) go public with RESULTS-7's MetaPRL column, not before.
- **The council's stop:** a FOURTH domain gap before the 11-08 cap stops Y5, which is then declared with its ledger.
- **The parts ledger is the arm's to declare at the cap.** At this note, step 7 was parts 89–99 and step 8 is parts 100–118g;
  steps 9–10 are open. The carving rows alone measured 9,254 tokens at eda567ed2, before D9 and D8a. Lean's whole semantic typing
  is 13,155 tokens over 1,092 lines (RESULTS-7 Y7).

## 3. The two hypotheses, stated so they can disagree
- **ENCODING.** MetaPRL's cost comes from the extrinsic representation: every theorem over untyped `BTerm` needs a recogniser, and
  then a carving to keep the encoding's junk out. A sorted language type removes the recognisers. The cost should fall sharply,
  and it should fall at the RECOGNISER sites.
- **TOOLING.** The cost comes from the proving machinery: tactic support, how scripts are driven, and replay. A sorted type leaves
  that unchanged, so the cost should fall little, and it should fall evenly rather than at recogniser sites.

## 4. The stated prediction (scored from SL5's and SL8's own figures; nothing new is counted)
- **D1 (encoding dominates).** SL5(a) HOLDS: the L1 stage ≤ 25,332 tokens. **FALSIFIED** if it exceeds that. If so, the encoding
  hypothesis cannot explain even half of amend-19's S.
- **D2 (tooling is not zero).** The L1 stage stays > **5,090** tokens, which is 10× Lean's 509. **FALSIFIED** if ≤ 5,090. If so,
  the encoding explains nearly all of the gap and tooling is minor.
- **D3 (where it falls).** SL4 HOLDS: the L1 rule derives with NO recogniser. If D1 also holds, the saving is attributed to the
  removed recognisers. If SL4 fails and D1 holds, the saving is reported with no attribution.
- **D4 (the tactic line).** By the 11-06 rule, tactic-building time is a separate line in the arm's ledger. **D1 and D2 are
  scored on C5 WITHOUT that line.** The line is reported beside them, with no direction.
- **The joint reading.** D1 and D2 both holding, i.e. 5,090 < L1 stage ≤ 25,332, is the prediction: **both causes are real, and
  the encoding is the larger.** D1 alone falsified favours tooling. D2 alone falsified favours encoding alone.

## 5. What would show this note unfair
a SLang file on the MetaPRL arm in a commit before this file's sha · SL5's bounds or D2's 5,090 re-read after the arm's first SLang
proof · the tactic line folded into C5 after the counts are seen. L2 on a sorted language (which would remove D8 and D9) is a
separate question, which the new (C) at SLang's landing puts to him. It is not predicted here.
