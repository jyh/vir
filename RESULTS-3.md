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

## ADDENDUM 5 (2026-11-01, the 3rd vir head): row 32, MetaPRL C5 is now H (post-proof; C5 carries no direction)
⚠️ **The table below is SUPERSEDED by addendum 6. Program 1's C5 is now 10 · lexical 487 over its five path lemmas, and both of mojave's token figures reproduce exactly. Read addendum 6's table.**
mojave's manifest `vir-arm-tools/STORED.tsv` (tools 4131276, @[bus]) names each program's stored-proof script and archive. `count.py` reads it: **C5** = the refine lines of that script · **C5tok** = their whitespace tokens (the same unit as C5chain) · **C5.inArchive** = the number of refine arguments that occur, whitespace-normalised, as a `String` node of the named `.prla`. Selftest ARM13 failed before the code change and again before the bare-string fix. The archive QUOTES a string only when it must (`String "(dT 0)"` beside `String (autoT)` and `String logicAutoT`), and the first extractor, which read only quoted strings, matched 11/12 and 20/21.

| program | C5 | C5tok | inArchive | mojave's figure (Q) | difference, named |
|---|---|---|---|---|---|
| 1 | 5 | 179 | 5/5 | 11 tactics · 487 tokens | the manifest names `steps/20.mp` (router_fuse) only, and mojave's 11 include the 5 path lemmas; the token unit differs (mojave's is not stated) |
| 2 | 12 | 688 | 12/12 | 12 tactics · 1,236 tokens; manifest commit says 11/11 | the tactic count agrees; the token unit differs; 11/11 against 12/12 is mojave's to read (asked) |
| 3 | 21 | 178 | 21/21 | 21/21 | agrees; C5tok = C5chain because the stored script IS the scored chain |

⇒ **Every MetaPRL row of programs 1–3 is now either H or a named Q.** The Q rows left are the verdict lines, C6's lost sessions (6 overwritten), and the step and box counts.

## ADDENDUM 6 (2026-11-01, the 3rd vir head): row 34, C5 over every manifest row, in mojave's lexical unit
mojave added one STORED.tsv row per program-1 path lemma and named the unit (@[bus]). It is LEXICAL tokens of each refine's argument, `[A-Za-z_][A-Za-z_0-9']*|\d+|<<|>>|[^\sA-Za-z_0-9]`. A lemma's block in a shared script runs from the `cd` naming it to the next `cd` naming ANOTHER theorem. Subgoal cds (`cd "1"`, `cd "../2"`, `cd "/vir/vir3/<thm>/2/1"`) stay inside the block. The first extractor ended a block at ANY cd and read program 1 as 6 and program 2 as 1. Selftest ARM14 failed on both shapes before each fix.

| program | C5 (refines) | C5lex | C5tok (whitespace) | C5.main | inArchive | mojave (Q) |
|---|---|---|---|---|---|---|
| 1 | **10** | **487** | 280 | 5 (router_fuse) | 10/10 | 10 · 487 (mojave corrected its own "11 tactics" to 10) — **agrees** |
| 2 | **12** | **1,236** | 688 | 12 | 12/12 | 12 · 1,236 — **agrees** (mojave reports its 11/11 as a needle defect in its own check) |
| 3 | **21** | 259 | 178 | 21 | 21/21 | 21 tactics, no token figure stated |

⇒ **MetaPRL C5 is H on all three programs and agrees with mojave's figures in mojave's unit.** C5chain (whitespace, scored chain) is unchanged. The Lean C5 rows count lines and tokens of VIR/*.lean, so they are a different unit and no ratio is drawn.

## ADDENDUM 7 (2026-11-01, the 3rd vir head): row 33, the Lean inputs reproduced from a CLEAN build
`lean/.lake/build` was moved aside (not deleted), then `../../saltbuild.sh` gave **build-024 `saltbuild EXIT=0`** and `../../saltbuild.sh Audit.lean` gave **audit-014 `saltbuild EXIT=0`**. The logs are in `lean/repro/`, not `lean/logs/`, because a reproduction run is not an iteration toward a proof and the whole-tree Lean C6 row counts every log in `logs/` (it would have moved 41 → 43).
- **axioms.txt: byte-identical** to the committed file when it is re-derived from audit-014.
- **terms.txt: identical except line 1**, the `saltqueue: ticket … pid=N` line the wrapper prints, which differs by construction (pid 71108 → 23250). No count reads it.
- ⚠️ **A NEEDLE DEFECT IN THE REGENERATION RECIPE, found here:** the bank's recipe (`grep "depends on axioms"` → axioms.txt) misses Lean's other form, `'X' does not depend on any axioms` (`VIR.Deep.router_fusion_deep_steps`), and puts it into terms.txt instead. The committed files were right. The recipe as written would have produced a wrong pair. **The recipe that reproduces the committed files exactly (checked on audit-013):** axioms = lines matching `depends on axioms|does not depend on any axioms`; terms = every other line except `saltbuild EXIT=`.
⇒ **The Lean inputs to every C1 row reproduce from a clean build.** With row 30's `reproduce.sh` (rc 0), the chain from the sources to every committed count is now re-run end to end on the Lean side. The MetaPRL side re-derives from mojave's artifacts but is not rebuilt here (mojave's verdict.sh is mojave's).


## ADDENDUM 8 (2026-11-01, the 4th vir head): row 35, paris's STEP 3 read against F_exit
**What was read, at the object:** the spike tree `~/projects/claude/wt/x86lean/o95-spike` at **2c0b059** (paris's, private, no remote), `git status` clean. Its pins resolve: `.lake/packages/vir` HEAD = **vir 2ab9d98** (F_exit as committed here, imported, not copied) and `.lake/packages/x86lean` HEAD = **public b1848ac**. The receipt `audit/axioms-step3.log` is tracked at 2c0b059. Its last line is `saltbuild EXIT=0`, the sorryAx control fires (`control_sorry` → `[sorryAx]`), and `Router.Refines.repaired_refines` → `[propext, Classical.choice, Quot.sound]`. `VIR.Deep.F_exit` → `[propext, Quot.sound]`, the same as vir's own audit.
**The statement (Router/Refines.lean, `repaired_refines`).** Fix `acl`, a machine state `s` with `Live s` and `rip = 0x1000`, and `buf off len σ`. Assume:
- `len` = rsi read unsigned;
- BufRel: the buffer's bytes are memory at rdi + i, for i < len;
- AclRel: `acl p t` is bit t%8 of the byte at 0x301d + 8p + t/8, for t < 64;
- StRel: σ p is the signed dword at rdx + 4p + 0x3000;
- topic < 64 whenever len ≥ 24;
- the buffer is disjoint from every bucket cell.

Then there is an n at which `runP repaired n s` has stopped, and its exit satisfies `Exit s _ p (den acl (F (.slice buf off len) (.state σ)))`. The proof opens with `rw [VIR.Deep.F_exit]`, so **the specification it refines is exactly row 11's exit relation.**

**What it establishes for the compiler application:**
1. **Program 1's lowering is verified end to end, for every state, once A.4 is repaired.** Paris proves the machine refines F. vir's `U_exit = router_fusion_deep.trans F_exit` (vir 9a7e5bf) shows U has the same exit relation. So the chain from spec composition U, through fused F, to the x86 code closes by composition. The composed theorem is not stated as one Lean term, so that is a reading, not a build.
2. **Each `Exit` clause is the strong form F_exit supports:**
   - TRUNCATED → 0x1040 with memory unchanged;
   - UNAUTH_OR_RATE → 0x1041 or 0x1042 with memory unchanged;
   - OK → 0x1043 with the payload slice at rax = rdi + 24 and length rsi; rdx is kept, StRel holds for the decremented σ' that `den` returns, and memory is the input with exactly one dword written;
   - `badPayload` and every other shape → False. Program 1's F cannot reach them, so these clauses add no escape hatch.
3. **A.4 as written does NOT lower soundly** (step 2's kernel-checked witnesses, E2/E3). Paris drove the E2 mutant (jb → jl) red against the ∀-state proof itself, at the two places that read the length guard. The E3 order was not driven here and paris declares that.

**Limits (they ride with the verdict):**
- **One invocation.** The theorem relates one run to one `F` application. AclRel reads an ABSOLUTE region (0x301d, the address the program's `leaq` puts the table at). StRel is relative to rdx. Nothing keeps the two regions from overlapping. That is harmless for one call, because the ACL is read before the one write (paris's finding (2)). A multi-call refinement, where state flows from one call to the next, would need the disjointness the single-call theorem does without.
- **Non-vacuity is argued, not built.** BufRel, AclRel and StRel each DEFINE their abstract value from memory (buf, acl and σ can always be read off `s.mem`). So the hypotheses are jointly satisfiable for any live s at 0x1000 with topic < 64 and the buffer placed away from the 16 GiB cell span. No Lean witness instantiates `repaired_refines` on a concrete state. Paris's three `decide` controls run the program and do not discharge the theorem's hypotheses.
- **The audit was read, not re-run.** Its sha, its tracked status and its pins were checked. A clean rebuild of the spike outside paris's tree is STATUS-vir row 36.
- **I6's "code disjoint" is vacuous in x86lean** (a Program is not in memory), as paris states. Any claim about self-modifying code is outside the theorem. That is a property of the x86lean model, not a gap in the proof.
- **Program 2 is not lowered.** Paris's answer at @[bus]: A.4 lowers F only, and a program-2 lowering would test paris's lowering, not the object's. **F2_exit (vir 06ff140) is recorded as OFFERED AND UNUSED.**

## ADDENDUM 9 (2026-11-01, the 4th vir head): row 36, step 3 REBUILT independently
A fresh `git clone` of the spike was checked out at **2c0b059** into vir's session scratch, so no `.lake` was copied. Lake fetched **x86lean from github.com/jyh/x86lean at b1848ac** and **vir at 2ab9d98** itself (`info: … cloning`). Then `saltbuild.sh` (build: 31 jobs, 13 X86 modules compiled, **`saltbuild EXIT=0`**, 0 `sorry` in the log) and `saltbuild.sh audit/Axioms.lean` (**`saltbuild EXIT=0`**).
**The axiom lines and the EXIT line of the rebuilt audit are byte-identical to paris's committed `audit/axioms-step3.log`**, all 21 `#print axioms` rows included. The logs are copied to `lean/repro/row36/`. Paris's tree was not built in or written to.
⇒ The step-3 receipt is reproduced from source by a party other than its author. Limit: the build machine and the toolchain (the spike's `lean-toolchain`) are the same box's, so this is a reproduction of the build and not an independent kernel.

## ADDENDUM 10 (2026-11-01, the 4th vir head): row 37, the composed theorem and a non-vacuity witness, BUILT
A new vir Lake project, `compose/`. It requires paris's spike **pinned at 2c0b059**, and vir 2ab9d98 and x86lean b1848ac come in transitively at the spike's own pins. `compose/Compose/Lowered.lean`, through saltbuild: **build-002 `saltbuild EXIT=0`**, **audit-001 `saltbuild EXIT=0`**, sorryAx control fires. Rebuilt after the mutant as build-004, EXIT=0.
- **(a) `lowered_refines_U`** is `repaired_refines` with `den (U …)` in place of `den (F …)`, rewritten by `den_U_eq_F = U_exit.trans F_exit.symm`. It depends on `[propext, Classical.choice, Quot.sound]`. **Program 1 is now ONE Lean term from the spec composition U to the x86 code, for all states under I6.** This replaces addendum 8's "by composition (a reading)".
- **(b) `witness_applies`** discharges every hypothesis on one concrete state. The state is live, rip 0x1000, rdi 0x10000, rsi 100, **rdx 2^48**; the buffer holds MAGIC, sender 0, topic 0 and zeros; the ACL byte is 1 and the bucket is 5. `acl` and `σ` are read off the state's memory, so AclRel and StRel hold by `rfl`. BufRel and topic < 64 hold by `decide`, and buffer/bucket disjointness by `bv_omega`. **The theorem is not vacuous.** Positive control on the same state: `witness_ok_control` (`decide`) shows the run takes the OK path, 17 steps to 0x1043 with the cell going 5 → 4.
- ⚠️ **FINDING: paris's own control state does NOT satisfy the theorem's `hdisj`.** `Router.start` puts rdx = 0x8000, and the bucket array for all 2^32 senders then spans [0xB000, 0xB000 + 2^34), which covers the buffer at 0x10000. **Red backwards:** with `wRdx := 0x8000` (build-003-mutant-rdx8000, `saltbuild EXIT=1`) the ONLY error is `w_disj`'s `bv_omega`, at Lowered.lean:83. Then source restored. That is not a defect of the theorem: its controls are concrete runs, not instances of it. But a reader taking "the controls are instances of the refinement" would be wrong. I6's disjointness is over the WHOLE sender range, because `p` is a `UInt32` read from the buffer. A tighter statement could bound it by the senders the ACL admits; that is not commissioned.
- **Limit:** one witness, on the OK path. The three drop paths are covered by the ∀-state theorem, but no witness instantiates them.

## ADDENDUM 11 (2026-11-01, the 4th vir head): rows 39–41 — drop-path witnesses, the compiler's cost, the two-call spec
All rows are in `compose/`: **build-006 `saltbuild EXIT=0`** and **audit-002 `saltbuild EXIT=0`**. All 20 audited declarations are at most `[propext, Classical.choice, Quot.sound]` and the sorryAx control fires. build-005 failed (EXIT=1) only on the four controls (`Mem` derives `BEq`, not `DecidableEq`); the fix compares `.mem.bytes`, as paris's controls do.
- **Row 39, every exit witnessed.** `Compose/Drops.lean` gives one concrete state per drop outcome: TRUNCATED (len 10), UNAUTH by magic (`0x4D534700`), UNAUTH by the ACL bit (clear), and RATE (bucket 0, the E3 shape). Each discharges every hypothesis of `lowered_refines_U`. One `decide` control per state names the exit and shows the memory bytes unchanged: 0x1040 in 3 steps · 0x1041 in 6 · 0x1041 in 11 · 0x1042 in 13. With addendum 10's OK witness, **all five machine paths are instances of the theorem.** The generic lemmas `aclOf_rel` / `sigOf_rel` (AclRel and StRel for ANY state, by `rfl`) and `disj_of` (any state with rdi 0x10000, rdx 2^48, len ≤ 100) are what make that cheap.
- **Row 40, the compiler's proof size** (`harness/compiler-counts.tsv`, exploratory, POST-PROOF, no prediction). It is read from paris's spike AT the pinned sha `2c0b0594…` by `git show`, because the working tree moves (ARM15: a later commit must not move the pinned count; the mutant that reads HEAD reds it). C5 units, non-blank lines · whitespace tokens:

| layer | what | C5 | C5tok |
|---|---|---|---|
| layer0 | AsWritten + Repaired (programs, concrete controls, step-2 witnesses) | 109 | 1,256 |
| layer1 | Steps + Paths (per-address steps, five ∀-state paths) | 313 | 3,579 |
| layer2 | Bridge + Refines (the abstraction and the refinement) | 438 | 3,872 |
| spike total | | 860 | 8,707 |
| vir compose/ | rows 37–41 | 222 | 2,135 |

  `CC.theorems` = 81. ⇒ **The abstraction bridge (layer 2) costs more than the machine paths (layer 1).** No ratio to the two arms is drawn, because the C5chain units count the scored fusion chain only. `reproduce.sh` now re-derives 7 files, rc 0. Limit: the compose rows read vir's working tree, not a sha.
- **Row 41, the spec side of a multi-call refinement** (`Compose/MultiCall.lean`, imports vir's F_exit only):
  - `F_ok_iff`: OK exactly when the four guards hold, returning exactly decTokens and b0 + 24;
  - `ok_state`: the returned state is the input with only the sender's cell decremented;
  - **`two_ok_same_sender`: two successive OK calls from one sender need ≥ 2 tokens at the start, and leave σ − 2. Rate limiting composes.**
  - `drop_no_state`.

  Red backwards: claiming 3 tokens (build-007-mutant-3tokens, EXIT=1) reds exactly that lemma's `omega`. Then restored, build-008 EXIT=0. It sits in compose/ so lean/out does not move. It is OFFERED to paris as the spec for a machine-level multi-call theorem, which would ALSO need the ACL/bucket disjointness that the single-call theorem does without (addendum 8).
