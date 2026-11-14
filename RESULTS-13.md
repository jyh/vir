# RESULTS-13 — layer L5, the standard library (O95; OBJECT-L5 at vir a35589c; amend-24; erratum L5-E1)

Scored 2026-11-14 by the 76th vir head. Both arms are closed:
- **Lean:** l5/ on l5-lean. LV8's assembly and the router are on master by #70 and #71. Every score below that has a harness arm
  reads it from l5/out/*.tsv (`count.py --arm lv9 | l5 | lv10`), each pinned in `harness/reproduce.sh` at its counts commit.
- **MetaPRL:** mojave/vir-l5 at **2d9a6c7f0** (census row 589: 15 modules, 948 complete grounded, 0 ungrounded), read from a clone
  at the pin by `count.py --arm metaprll5 --base d257d2f29 --ext 2d9a6c7f0` into `l5/out/metaprl-counts-l5.tsv`. Its reading,
  `l5/SCORING-METAPRL-L5.md`, was committed BEFORE any figure was taken from a virl5 module. It was amended twice before any count,
  both times for LV10's alpha-renaming, and says so.

`harness/reproduce.sh` reads **28 files, rc 0**. Every extractor below was added red first. Selftest arms ARM59–64 each have a
mutant, and every mutant is KILLED.

## The declarations, each written before the files or counts it governs
| arm | what | where |
|---|---|---|
| Lean | L5's language, the routines, LV8's map | l5/DECLARATIONS-LEAN.md (first form + Addenda 1–5), l5/LV8-MAP.md (Addenda 1–11) |
| Lean | LV9's node and call (Add. 6) · LV4's case cut (Add. 7) · LV5's population (Add. 8) · LV7 read mechanically (Add. 9) · LV10 by shape (Add. 10) | l5/DECLARATIONS-LEAN.md, each committed before its count |
| MetaPRL | G0–G8, A1–A12 | theories/vir/DECLARATIONS-L5-METAPRL.md at 2d9a6c7f0 (the arm's) |
| scorer | the MetaPRL reading; LV3's and LV6's names given by the arm (bus 11-14 09:15) | l5/SCORING-METAPRL-L5.md |

## The scoreboard
| | Lean | MetaPRL |
|---|---|---|
| **LV1** L1–L4 untouched | **HOLDS, provisional**: W8.defsEdited 0 on l1–l4 from 4017931 to 060f5d3 (control: 13 files over 7f82f94..4017931). It is re-read at the Lean L5-closed sha | **HOLDS**: 0 virl1–4 files changed d257d2f29..2d9a6c7f0; 0 virl5 modules name an L4 module |
| **LV2** no new axiom or prim | **HOLDS**: audit-040, 243 rows within the three axioms, 0 sorryAx (control sorryAx) | **HOLDS**: 0 prims in virl5_*, 0 framework files changed |
| **LV3** CE both directions | **HOLDS (author read, Q)**: `type_ι : HasType₂ Γ Δ e τ → HasType₅ …` (premise ⊢₂ only); `ce_step` is an iff with NO premise; `faults₅_ι`. C5: CE.lean 1726 tokens | **HOLDS (author read, Q)**: `ce_tc : tc5 ~ tc2` and `ce5_step : l5step ~ l2step`, each under BTerm{0} ∩ L2Run membership only (stronger than G4: equal functions). C5: the CE chain is 13,822 tokens, of which virl5_tc2t, 2,996, is a VERBATIM copy of L4's (A4, reported apart) |
| **LV4** the fix case is the largest | **FALSIFIED**: the larger fix arm, appKFix, 151, against pres₅.op 722 (0.209). The two fix arms summed (264, BESIDE) are still below op | **UNREACHED** by declaration G7 (semantic typing priced out; 0 virl5_sem files) |
| **LV5** Lean pays in transport | **FALSIFIED**: 29 CAST_RE hits over the 13 L1′ files, 4 in the application/fix arms | reported, no direction: no analogue |
| **LV6** MetaPRL pays in wf | no analogue (0) | **FALSIFIED**: 32/6 over the arm's six L1′ rules against L2's 42/6 (BESIDE: 2516/676 over every virl5 rule) |
| **LV7** premises name sizes only | **HOLDS**: 0 content premises over the five (18 premises); copyWithinR 0 BESIDE | **HOLDS**: 0 over the five, 14 of 14 triples read; every triple's content variables were found, the positive control; l5_copy_self 0 BESIDE |
| **LV8** the library abstracts | DEFLATE **HOLDS** (`safety₅`, `correct₅`; 0 lemmas that unfold a routine body). Router **VACUOUS** (V-F8: no routine fits F; R4₅ by `triple_ι`) | **UNREACHED** (G6: the router part needs its own declaration; 0 virl5_router files) |
| **LV9** the code collapses | **FALSIFIED** for both programs. DEFLATE: 7 calls, 2778 → 2866 nodes, −88. Router: 0 calls, 0 removed | **UNREACHED** (G6) |
| **LV10** no duplication | **HOLDS**: 0 equal shapes among 10 pairs (all six shape lengths differ) | **HOLDS**: 0 equal shapes among the five; l5_copy_self 0 BESIDE |
| **LV11** compiler, no per-routine lemma | UNSCORED until S3 | UNSCORED |

## What the layer says (a reading; the cells above are the record)
- **The library is sound and content-free on both arms.** LV1, LV2, LV3, LV7 and LV10 hold on both. The routines' triples name
  regions, sizes and bounds only, which is DEFLATE's D7 shape carried to a library.
- **It does not shrink the programs that use it.** On the Lean arm DEFLATE grew: one item per step became a chunk per call, and
  the chunk's plumbing outweighs the loop body it replaced. The router never used a loop (V-F8). J3 (a) chose its routines from
  what the two programs "hand-code", and the router hand-codes none of them. The MetaPRL arm did not reach either program (G6, and
  DEFLATE is Lean-only).
- **Where L1′ pays is not where amend-24 put it.** On Lean, preservation's single `op` rule, which carries the four memory
  operations, costs about five times the fix arm. Casts spread across every preservation arm, at about one each, rather than
  gathering at the application. On MetaPRL, the six L1′ rules carry FEWER wf labels per rule than L2's six (32/6 against 42/6).
- **Process findings:** FINDINGS V-F8 (the router has no loop). LV9's TABLE note is in LV8-MAP Addendum 11, BESIDE: a DEFLATE
  without the unread table would read +78. LV10's signature collision (fillR and copyWithinR share (int×int×int, 1, unit)) was
  found while building the instrument and recorded in Addendum 6 before any count.

## Limits, beside the verdicts
- LV1 (Lean) is provisional until a Lean L5-closed sha is named. LV3 on both arms is an author read of named statements (Q),
  not a mechanical one.
- LV4, LV6, LV8 and LV9 each have an UNREACHED or no-analogue side. No comparison is drawn across a missing cell.
- C5 for LV3 is file-level tokens, BESIDE. No direction was predicted.
