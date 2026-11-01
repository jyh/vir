# RESULTS 3 — PROGRAM 3 (the A.1/A.2 safety theorem over F2), the LEAN arm first (2026-11-01, the 2nd vir head)

Inputs `inputs/program3-inputs.md` and predictions `predictions/PREDICTIONS-program3.md`, with the extractors in `harness/count.py`, all pinned at vir 98d9329 BEFORE either arm's first proof. **This file's Lean section was committed before vir read any MetaPRL program-3 result.**

## Lean (`lean/VIR/Router3.lean`, `route_acl_safe`; build-021 `saltbuild EXIT=0` on its first build; audit-011 EXIT=0; axioms [propext, Quot.sound])
ValidFrame is A.1's Prop-carrying subtype of `ByteArray`, and F2 is applied to the frame's whole-buffer slice `wholeSlice b.val`. The proof is a case split on F2's guards (`unfold F2; simp only [guard, readU32, letLin]; split; split`), with no rewrite chain.
| count | value (H) |
|---|---|
| **C1coe** | **54** (all of them `.val`, from `b.val`. The printer writes the coercion as `b.val`, never `↑b`; `.property` and `Subtype.val` are 0) |
| C1heq | 0 |
| C2cond | 0 |
| C3 (aux used) | 0 |
| C4 | 0 |
| C5chain | ~~38~~ **32** (addendum 1: 6 of the 38 tokens were Rules.lean's header) |
⚠️ **What C1coe's 54 measures:** occurrences of the projection in the ELABORATED term. The source writes `b.val` ONCE, in the statement (`wholeSlice b.val`), and the elaborator repeats it at every point the case split mentions the buffer's size or bytes. The number is the pinned extractor's, as preregistered, and it is a count of how often the boundary shows in the proof term, not of how often an author wrote it.
## Lean's side of the predictions
- **T1 (Lean C1coe ≥ 1): HOLDS on the Lean side (54).** MetaPRL C1 = 0 is owed by mojave's arm.
- **T2: owed.** Lean's P3.C2cond is 0, so T2 holds iff MetaPRL C2genWf ≥ 1.
- **T3: holds for Lean** (C3 0, no aux rule). **T4: holds for Lean** (C4 0).
- **T5:** Lean C5chain ~~38~~ **32** (addendum 1). The case split IS the proof, as T5 expected.

## MetaPRL: LANDED — see ADDENDUM 3 (this heading read "OWED" until 2026-11-01, the 3rd vir head)

## ADDENDUM 1 (2026-11-01, the 2nd vir head): a harness defect in C5chain found at row 25, plus amend-9 scored
**The defect (vir's own):** the Lean extractor concatenates every `VIR/*.lean` in sorted order and splits the result into declaration blocks. A proof that is the LAST declaration of its file therefore absorbed the NEXT file's header (`import …`, `namespace …`) and its own `end VIR`. Only C5chain read those tokens. **No C1, C2, C3, C3deep or C4 figure moved.** The figures it inflated:
- route_acl_safe 38 → **32** (6 tokens of Rules.lean's header)
- router2_fusion 202 → **196** (RESULTS-2 Q5)
- router2z_fusion 220 → **214** (RESULTS-2 addendum 4)
- route_acl_safe_flat 40 → 34

Program 1's C5chain (84) and every deep chain are unchanged, because none of them ends its file. **Fixed:** a sentinel declaration between files, and a chain that ends at its namespace's `end`. Selftest ARM10 is red-backwards: the pre-fix harness FAILS it, and the fixed one passes (rc 0). **Copies corrected in place:** RESULTS-2 (Q5 · the program-2 table · addendum 4) · SUMMARY-first-act (Q5) · this file's table and T5. No verdict depended on C5chain, because Q5 and T5 are exploratory.

**amend-9 (pinned at vir bbeac50 BEFORE the variant), scored on `route_acl_safe_flat`** (build-022 `saltbuild EXIT=0`, audit-012; axioms [propext, Quot.sound]):
- **F1 HOLDS:** P3F.C1coe **0**. With ValidFrame as a hypothesis on a bare buffer, the 54 coercions vanish, so Lean's boundary cost on program 3 is the SUBTYPE REPRESENTATION, the same shape as P1b for slices.
- **F2 HOLDS:** the proof builds with `hv` CLEARED before it. ValidFrame's refinement carries NO load in K3, because F2 re-checks the length and the magic itself. ⇒ **A finding about the object:** in A.1's `route_acl_safe` the subtype is decoration, and the guards in the term already discharge it.
- **F3, read both ways:** on the letter it is FALSIFIED (34 ≠ 32). The difference is exactly the 2 tokens of the preregistered `clear hv`, so the remaining script is token-for-token the same. *(F3's own text quotes "38", the leaky figure. A prediction file is never edited, so the correction lives here.)*

## ADDENDUM 2 (2026-11-01, the 2nd vir head): row 26, program 3 on L-DEEP (EXPLORATORY: no prediction was pinned for this embedding)
`lean/VIR/Deep3.lean`, `route_acl_safe_deep (b0 st : Val) : IsRoutedD (den acl (F2 b0 st)) → acl (b0.rd 4).toP (b0.rd 8).toP = true`. It is proved by rewriting with program 2's `F2_exit` and then the same two-level case split. build-023 `saltbuild EXIT=0`, audit-013; axioms [propext, Quot.sound]. **P3D.C5chain 23 · C2cond 0.** There is no ValidFrame, because amend-9 F2 measured that its refinement carries no load.
⇒ On the deep embedding the safety theorem is a COROLLARY of the exit relation, and it costs 23 tokens against the shallow 32. The cost of program 3 sits in whichever artifact states F2's meaning. Once that meaning exists (row 17), the safety theorem is a case split over it.

## ADDENDUM 3 (2026-11-01, the 3rd vir head): the MetaPRL arm of program 3, harvested and scored (row 27)
**Source:** mojave @[bus] · record `seats/mojave/vir-arm-tools/COUNTS-metaprl-program3.md` (tools 05492af, an ancestor of the tools HEAD read here, 6192013) · theory `vir-metaprl/theories/vir/vir3.ml` (21488b464, ancestor of HEAD 26b4e01d6) · stored proof `vir3.prla`. Inputs vir 98d9329, E10 read as `p := frame_sender(b)`, not disputed. vir did not read this post until after RESULTS-3's Lean section and addenda 1–2 were committed (vir f19133d and earlier).
**Counts** (`count.py --arm metaprl --program 3 ~/projects/claude/seats/mojave`, saved as `harness/metaprl-counts-program3.tsv`; H = the harness reproduces it from the artifacts, Q = quoted from mojave's record):

| row | MetaPRL | Lean (same program) | state |
|---|---|---|---|
| C1 (cast tokens in steps/*.mp) | **0** | P3.C1coe **54** | H |
| C2genWf | **7** | P3.C2cond **0** | H |
| C2genEq · C2genCond | 0 · 0 | — | H |
| C3 / C3strict | 5 / **0** | P3.C3 0 | H |
| C4 | **0** | 0 (axioms [propext, Quot.sound]) | H |
| C5chain | 178 | P3.C5chain 32 | H |
| C6sessions · C6refines | 10 · 120 (kept files) | — | H, a LOWER BOUND: mojave reports 16 sessions to first green, 6 reruns overwrote their file (Q) |
| verdict | `route_acl_safe complete 21` (21 rule boxes, 1,908 primitive steps); mutant `incomplete 2` RED | build-021 EXIT=0 | Q (mojave's verdict.sh run) |

**Scoring against PREDICTIONS-program3.md (pinned 98d9329, before either arm's first proof; extractor conventions fixed at that sha):**
- **T1 HOLDS.** Lean C1coe 54 ≥ 1 and MetaPRL C1 = 0.
- **T2 HOLDS.** MetaPRL C2genWf 7 > Lean P3.C2cond 0. Of the 7, 3 come from the STATEMENT's well-formedness (validframe Type · top Type · isrouted{F2…} Type, §5.1's Gate-2 class) and 4 from the proof (boolean typing of the two guards the case split reads, and of the two band eliminations). Mojave's attribution, quoted (Q); the total is H.
- **T3 HOLDS on both arms.** C3strict 0 and 0. (MetaPRL C3 under amend-3 is 5: the form unfolds read_u32 · vguard · vdrop on the main chain, let_lin · advance in the isrouted-Type closer.)
- **T4 HOLDS on both arms.**
- **T5 (exploratory):** C5chain 178 against 32. A case split proves K3 directly on both arms (two splitITE + two band eliminations in CTT; the two-level match in Lean). The MetaPRL figure includes the 7 well-formedness closers; the token ratio is not a T-prediction and no claim is made from it.

**Amend-9's CTT half (the control).** `steps/ctl-flat3.mp`: the same chain with `thinT 3` right after the set elimination (the squashed validity predicate removed) COMPLETES. So ValidFrame carries no load in CTT either, which matches Lean's F2 (amend-9). On both arms the boundary is a cost of STATING the theorem, and the proof never uses the refinement. Lean pays it as 54 coercion tokens in the elaborated term and 0 tokens after flattening (F1). CTT pays it as one set-elimination step and three statement-wf obligations.

**Affordance difference, named (AFFORDANCE-PARITY):** the MetaPRL statement needs ONE hypothesis Lean does not: take's typing (`take{p; n; q. vreturn{(s,q)}} ∈ top + top`), because `take` (J1) is declared and undefined in CTT, so isrouted's well-formedness cannot be proved without it. Lean types it natively. It is a hypothesis, so C4 does not count it (the programs 1–2 convention). It is recorded as D6 in this addendum, not added to the parity file's closed rows.

**Harness defect fixed here (post-dates every proof; C6 is in no T-prediction):** the MetaPRL C6 rows read `runs-NN.txt` for every program, which are PROGRAM 1's driver runs, so `--program 2` and `--program 3` printed 20 · 43 (mojave's finding). Now `--program N` reads `runs-pN-NN.txt`. Red first: selftest ARM11 failed on the old code (program 3 read 4 = R1) and passes on the new one. Program 1's rows are unchanged (20 · 43). `harness/metaprl-counts-program2.tsv` is regenerated, and only its two C6 rows move (20 · 43 → **9 · 73**). The census for copies of the wrong program-2 figure found none: the only `20 · 43` in the tree is RESULTS-1, which is program 1's and correct.

⇒ **Program 3 closes green on both arms, with T1–T4 holding as preregistered and every extractor fixed in advance.** This is the first program whose verdict is not provisional on a convention written after the proofs (the reason program 3 exists, row 23).

## ADDENDUM 4 (2026-11-01, the 3rd vir head): row 31, T2's attribution made reproducible (EXPLORATORY, post-proof, no prediction)
Addendum 3 quoted mojave's split of C2genWf 7 as "3 statement + 4 proof" (Q). The harness now reproduces it. A wf child of a bare `refine (dT 0);;` (intro on the conclusion) is counted as the STATEMENT's well-formedness, and every other wf child as the PROOF's. The convention was written after the proofs and selftest ARM12 failed before the code change. **Program 3: C2genWf.stmt 3 · C2genWf.proof 4 (H)**, which agrees with mojave: the stmt children are those of the ∀b / ∀st / ⇒ intros (steps 2, 8, 10), and the proof children come from the two splitITE (16, 20) and the two band eliminations (24, 26). Programs 1 and 2 read stmt 0 · proof 3, because their goals are equations under hypotheses and introduce nothing. ⇒ **The boundary-as-well-formedness that T2 predicts is, in program 3, exactly the 3 statement obligations. The other 4 are the case split's own bookkeeping, which program 1 also pays (3).** This is a reading and not a prediction. The rows carry state EXPLORATORY.
`harness/reproduce.sh` (row 30) re-derives all six committed count files. It is rc 0 after this change, and the only difference from the files before it was the two added rows per MetaPRL file.

