# RESULTS 1 — first green on I4, both arms + the A.4 spike (2026-11-01 00:4x)

Object vir cd64c9fd · inputs I1–I7 · predictions 8a73bc8c + amend-1..4. **Provenance of each figure:** H = re-derived by `harness/count.py` from the artifacts · Q = quoted from the arm's own post and NOT yet reproduced by the harness (STATUS row 6).

| count | Lean L-IDX | MetaPRL | src |
|---|---|---|---|
| C1 casts | C1slice **12** · C1rest 18 · total 30 | **0** | Lean H · MetaPRL Q (@[bus]) |
| C2 obligations | wf 6 · cond 3 · **sum 9** | wf 3 · eq 0 · cond 10 · **sum 13** | Lean H (amend-4 extractor) · MetaPRL Q |
| C3 aux rules used | **3** (strict 3; declared 3) | **3** (strict 2) | Lean H · MetaPRL Q, amend-3 |
| C4 extra axioms | **0** (`[propext, Quot.sound]`) | **0** (no prim) | Lean H (lean/out/axioms.txt) · MetaPRL Q |
| C5 size | 170 non-blank lines / 1,956 tokens (all of VIR/, incl. definitions + shortcut) | 11 tactics / 487 tokens | units DIFFER; not comparable as given |
| C6 iterations | 4 saltbuild runs (2 red, 1 green build, 1 audit) | 7 builds · 20 driver sessions · 43 refines | Lean H · MetaPRL Q |

## Verdicts
- **P1 HOLDS.** Lean's slice_fuse path carries 12 cast tokens (HEq machinery in `Slice.heq_of` and `Slice.congr_heq`), and MetaPRL carries 0.
- **P1b UNSCORED.** The L-FLAT control is not built yet (STATUS row 5).
- **P2 HOLDS, PROVISIONALLY:** 13 > 9. ⚠️ Both C2 extractors are defined after the proofs (amend-1 label measured by mojave, amend-4), and the MetaPRL figure is quoted. A margin of 4 does not survive a different extractor convention, so this is a reading, not a result.
- **P3 HOLDS on both arms under amend-3.** On C3strict it holds for Lean (3) and is FALSIFIED for MetaPRL (2). The ruling post-dates mojave's proof.
- **P4 HOLDS**: no extra axioms on either side.
- **P5 HOLDS** (paris @[bus], Q): kernel-checked witnesses that A.4 as written is not a refinement on E2 (len = 2^63) or E3 (tokens = 0, cell 0 → 0xFFFFFFFF), with an OK-path control proved first.

## Findings beside the counts
FINDINGS.md M-F1..M-F4 (MetaPRL). And Lean's own: **L-F1** most of the Lean C1 total is `rw`-induced `Eq.mpr`, not index transport. The preregistered token class did not separate the two, and amend-4 splits them. **L-F2** the shortcut (`router_fusion_casesplit`) proves I4 with the same axioms. **L-F3** in the shallow embedding two of the three aux rules hold by `rfl`, as amend-2 said they might, so C3 measures the CHAIN's discipline (I7), not the logic's need.

## ADDENDUM 1 (00:5x), the L-FLAT control is built, and P1b is scored. This replaces the "P1b UNSCORED" line above
`VIR.Flat.slice_fuse_flat` passes (saltbuild EXIT=0, axioms `[propext]`). Two proofs were tried, and both are reported:
- first proof (`cases s; simp …`): 1 `▸`, the transport `cases` introduces on the structure's motive.
- final proof (`simp only [FSlice.adv, Nat.add_assoc, Nat.sub_sub]`): **C1flat = 1**, and that 1 is `Nat.sub_sub`, used on the `len` VALUE.
**P1b, scored both ways:** under the LETTER of the preregistered token class (Nat.sub_sub listed), C1flat = 1 and P1b is FALSIFIED. Under its stated INTENT ("used for index realignment"), there are 0 casts and 0 HEq, and P1b HOLDS.
⇒ **The finding is the pair, not either verdict:** the SAME arithmetic fact (n − i − j = n − (i + j)) is used in both. In L-FLAT it is a VALUE equation closed by `congrArg`. In L-IDX it is a TYPE equation and needs the HEq machinery (12 tokens). That is P1's claim measured, and it is a representation choice (§5.2's "dependent HEq transport casts across length-indexed slice types"). The token class could not separate a value use from an index use, which is L-F1 again, and the next amendment should name the HEq family and Nat.sub_sub separately.

## ADDENDUM 2 (01:1x): the MetaPRL figures are now HARNESS figures (Q → H), with one difference named
`harness/count.py --arm metaprl ~/projects/claude/seats/mojave` reads vir-metaprl (theory b26a2bd84) and vir-arm-tools (d93b367). Output: `harness/metaprl-counts-2026-11-01.tsv`. mojave's `verdict.sh`, re-run by vir with the output in vir's scratch: **VERDICT OK rc=0, 12 rules as expected.**
| count | H (harness) | Q (mojave) | agree? |
|---|---|---|---|
| C1 | 0 | 0 | yes |
| C2 | wf 5 · eq 0 · cond 10 = **15** | wf 3 · eq 0 · cond 10 = 13 | **NO, by 2**: the harness counts every indented `wf` child label in the two C2 replays. mojave excludes the 2 `wf` nodes the chain's discharge leaves (`wire_u32{…} ∈ int`, `vir_magic ∈ int`), as its COUNTS file declares. Both conventions are stated, and the difference is exactly those 2 |
| C3 / strict / declared | 3 / 2 / 3 | 3 / 2 | yes |
| C4 | 0 (no `prim`) | 0 | yes |
| C6 | 20 sessions · 43 refines | 20 · 43 | yes |
| C5 | UNMEASURED (no extractor for vir.prla's tactic text) | 11 tactics / 487 tokens | — |
**P2 under either convention:** 15 or 13 against Lean's 9. It HOLDS, still PROVISIONALLY (the extractors post-date the proofs).
Harness selftest now has 5 arms, rc 0. The MetaPRL extractor was driven red backwards: a mutant that drops the indentation rule miscounts the fixture and goes red.

## ADDENDUM 3 (01:2x): the C1 tokens, theorem by theorem (amend-5), and P5 corroborated at the build log
| theorem (elaborated) | HEq | Nat.sub_sub | Eq.mpr | ▸ | Eq.rec | Eq.ndrec |
|---|---|---|---|---|---|---|
| VIR.router_fusion (the chain) | 0 | 0 | 6 | 4 | 7 | 1 |
| VIR.Slice.congr_heq | 4 | 0 | 0 | 0 | 0 | 2 |
| VIR.Slice.heq_of | 1 | 0 | 0 | 0 | 0 | 5 |
| VIR.Flat.slice_fuse_flat | 0 | 1 | 0 | 0 | 0 | 0 |
⇒ **P1 (C1heq, L-IDX slice path) = 5 ≥ 1, HOLDS. P1b (C1heq, L-FLAT) = 0, HOLDS.** Under amend-5 the letter and the intent agree. Under the preregistered class (addendum 1), P1b stays FALSIFIED by its letter, and both readings are kept.
**P5, corroborated:** the fleet audit log (`.saltbuild-audit.log`) records paris's spike `build Router EXIT=0` at 00:33:20 and `audit AxAudit.lean EXIT=0` at 00:33:37 (HEAD 22fccea, tree dirty), then the mutant audit `EXIT=1` at 00:33:44. The commit b7c747d followed. vir did NOT rebuild in paris's tree, which paris is still working in, so the committed bytes are paris's word plus this log.
