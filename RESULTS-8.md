# RESULTS-8 — layer L3, the router as an L2 program (O95; OBJECT-L3 at vir 18df3a4; amend-18; erratum L3-E1)

**The Lean column; UNSEALED 2026-11-05** on the MetaPRL arm's L3 declarations (the Captain's pace ruling (C), 11-05). Every Lean
figure is a row of `l3/out/counts-l3.tsv` (`harness/count.py --arm l3 l3`) or `l3/out/counts-z1.tsv` (`--arm w8 --base dc95b53`),
or is labelled as something else. Lean L2-closed sha: dc95b53. The MetaPRL column is scored when that arm builds L3.

## The declarations (amend-18), both written before the arm's first L3 file, neither arm reading the other's
| arm | file | commit (time) | sha256/16 |
|---|---|---|---|
| Lean | `l3/DECLARATIONS-LEAN.md` | vir 9de7857 (2026-11-03), SEALED until the MetaPRL post | bf6646d9fec4a931 |
| MetaPRL | `theories/vir/DECLARATIONS-L3-METAPRL.md` in mojave's metaprl clone, copied byte for byte to `l3/DECLARATIONS-METAPRL-ae4c349b2.md` | ae4c349b2 (2026-11-05 16:13 PST) on mojave/vir-l2, parent 265c1b8e1, 0 `virl3_` files at it | ae80ac5b7c42aef0 |

Both hashes were re-read at the unseal (the Lean file at 9de7857 and at the branch tip, the MetaPRL file at ae4c349b2). The
MetaPRL arm's post of its declarations said it had not read anything under `l3/`, any Lean L3 file or branch, or the Lean
declarations; it had read ERRATA-L3 at fcaae75, whose L3-E1 names the Lean arm's R3False file and two lemma names (declared by
that arm). The Lean branch was not pushed until after that post. The MetaPRL declarations defer one item: the L2-closed sha, to
be posted with counts before its first `virl3_` file.

## The rows (inputs/L3-programs.md R1–R8), Lean
| row | theorem(s) | file |
|---|---|---|
| R1 | `F_typed` · `U_typed` · `U_tx_typed` — `(w:cap) ; {w} ⊢₂ · : cap` | VIRL3/Typing.lean |
| R2 | `R2` — ⟦U⟧₂ ≠ ⟦F⟧₂, one witness world (U's bucket 0, F's 1) | VIRL3/Inequality.lean |
| R3 | `R3` — ⟦U_tx⟧₂ = ⟦F⟧₂ on every store whose world has sender and topic in [0, 4) (L3-E1's reading; the theorem assumes LESS than `layout`) | VIRL3/Rollback.lean, VIRL3/Sym.lean |
| R4 | `R4` — {RegionAt p 87 f} F {v. v = ⟨p⟩ ∧ RegionAt p 87 (postF f p)}, layout's pure part as hypotheses | VIRL3/RouterTriple.lean |
| R5 | `R5_contents` (postF agrees with f off the bucket and out cells) · `R5_frame` (beside any R, by `frame`) | VIRL3/RouterTriple.lean |
| R6 | `R6` — over any list of in-range frames, sender s's emits ≤ its initial tokens; `R6_call` (each call is R4) | VIRL3/Trace.lean |
| R7 | `R7` — the variant ending `ret 1` has no type | VIRL3/Refusals.lean |
| R8 | `R8` — sender = NS index-faults at the bucket load; no triple whose precondition admits that world (proved WF, not assumed) | VIRL3/Refusals.lean |
| L3-E1 | `R3_false_order` · `R3_false_alias` — R3 as pinned is false | VIRL3/R3False.lean |

All 10 row theorems present (`L3.rows.present` 10). `audit-001`: 14 theorems, each within propext · Classical.choice ·
Quot.sound (R7: propext only); control `control_sorry` prints sorryAx (`L3.control` 1). The transcription check
(`harness/transcribe_l3.py`, selftest ARM37): F, U, U_tx built from the inputs file's TEXT equal the Lean terms, SAME ×3.

## The predictions (amend-18 Z1–Z9), Lean
| | prediction | Lean | verdict |
|---|---|---|---|
| Z1 | no L2 (or L1) definition edited, dc95b53 → L3 tip | **0** L2 · **0** L1 (`counts-z1.tsv`; positive control 2fccab7 → 8c3320f reads 17) | HOLDS |
| Z2 | transport casts on the L3 files = 0 | **0** (`L3.Z2.casts`, CAST_RE) | HOLDS |
| Z3 | R2 by evaluation, citing no triple | **0** `Triple` in Inequality.lean; R2 cites `run₂_steps` · `den₂_of_steps` · `soundness₂_steps` only | HOLDS |
| Z4 | R3 is the largest L3 proof by C5 | R3 (Rollback+Sym) **851** tokens; R4+R5 (RouterTriple) **1,170** (`L3.Z4.*`) | **FALSIFIED** |
| Z5 | R4 from the rules, no ⟶₂ in its proof | **0** step tokens in R4's proof (`L3.Z5.stepInR4`) | HOLDS |
| Z6 | R5's caller half is one `frame`, no locality lemma | `frame` **1**, locality lemmas **0** (`L3.Z6.*`) | HOLDS |
| Z7 | R6 in the logic; no `fix` in a term | `fix` in the terms **0**; R6 is a structural induction over `List` | HOLDS; R6 C5 **696** reported (`L3.C5.Trace`) |
| Z8 | R7, R8 each ≤ 15 proof lines | R7 **8** · R8 **17** (`L3.Z8.*`; R8's world-is-WF lemmas, 21 lines with their statements, BESIDE) | R7 HOLDS · **R8 FALSIFIED** |
| Z9 | L3 proof C5 > virp program-1 router C5 | **3,874** (the R1–R8 files) against **1,617** (virp Router · Exits · Sep · Trace) | HOLDS (scope beside: virp WITH its language files is 7,055) |

## What the Lean arm found, for the paper
- **L3-E1 was found by writing R3's proof, not by running it**: the ANF order of F's loads (before its guard) and the overlap of
  the ACL rows with the buckets for topics ≥ NT are invisible in virp's U = F, where loads are total and drops abort.
- **L2 has no `if` rule and no pure-`let` rule.** R4 derives both from `pure_step_rule` with L1's `determinism`
  (`ite_true_rule`, `ite_false_rule`, `letRet_rule`); that is where `L3.Z5.stepInFile` (2) comes from, BESIDE R4's own 0.
- **Two methods, one arm:** R3 is an equality of meanings and is proved by SYMBOLIC RUNS (`simp` through `run₂`, the world's
  lookups as rewrite rules, five branches); R4 is a triple and is proved by the RULES. The rules proof is the larger (Z4).

## Limits
- C5 rows are whitespace tokens per FILE, comments stripped; R3's figure includes the symbolic-run kit in Sym.lean, R4's
  includes R5 and the frame-field definitions. A per-theorem split could order Z4 differently; it is not what Z4's extractor
  reads, and the extractor was fixed (ARM38) before these figures were taken.
- `L3.Z5.stepInFile` counts the capitalised forms only; the helper's `step₂_ret_none` (lowercase) is a fourth token beside it.
- R4 and R6 carry layout's pure part as Lean hypotheses (sender, topic in range), not as `⌜·⌝` inside the assertion.
- R6 bounds emits by the INITIAL tokens with the initial bucket non-negative; frames are written by the caller between calls
  (cells [p, p + 67)), and the bound is about R4's post-states, each call justified by `R6_call`.
