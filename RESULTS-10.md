# RESULTS-10 — layer L4, concurrency with locks (O95; OBJECT-L4 at vir e80bd25; amend-21; errata L4-E1, L4-E2, L4-E3)

**The Lean column; UNSEALED 2026-11-08** on the MetaPRL arm's L4 declarations (the Captain's pace ruling (C), 11-05, as at L3). Every
Lean figure is a row of `l4/out/counts-l4.tsv` (`harness/count.py --arm l4 l4`) or `l4/out/counts-q1.tsv` (`--arm w8 --base 7f82f94
--ext 4017931`), a theorem name, a commit, or an `EXIT=` line in `l4/logs/`. Lean L3-closed sha 7f82f94; Lean L4-closed sha 4017931 (no
`.lean` file changes after it). The MetaPRL column was scored on 2026-11-10 at that arm's L4-closed sha d257d2f29, by `count.py --arm metaprll4`, whose reading
was committed before the arm's first L4 rule (section "The MetaPRL column" below). **`harness/l4-counts-lean.tsv` is the record of the counts as sealed (2026-11-06)**: the counts
below were taken then, before the MetaPRL declarations existed, and re-derived unchanged at the unseal (40 of 40 `--arm l4` rows; the
nine W8 rows re-run). Shas here are the published ones; the branch was rewritten once before its first push, to redact home paths in
forty build logs, and `L4-SHA-MAP.tsv` maps every pre-rewrite sha (which `l4/` prose and commit bodies from before it cite).

## The declarations, each written before the files it governs, neither arm reading the other's
| arm | file | commit | sha256/16 |
|---|---|---|---|
| Lean | `l4/DECLARATIONS-LEAN.md` | vir bddbd40 (first form); addenda 1–7 below | at the tip `ba5b73e0457292ca` |
| MetaPRL | `theories/vir/DECLARATIONS-L4-METAPRL.md` in mojave's metaprl clone, copied byte for byte to `l4/DECLARATIONS-METAPRL-ccfe03d24.md` | ccfe03d24 (2026-11-08) on mojave/vir-l4, parent 2d63bef28 = its L3-closed sha, 0 `virl4_*` files at it | `bca726412efe43ff` |
| MetaPRL, amended | the same file with F11 (the L4 errata read, N4's term fixed by L4-E2, Q5's population), copied to `l4/DECLARATIONS-METAPRL-d2fc1bb1b.md` | d2fc1bb1b, 0 `virl4_*` files at it | `7dea85c6afd27021` |

Lean addenda, all on the sealed branch, before the rows they govern:

| addendum | content | commit |
|---|---|---|
| 1 | erratum L4-E1: `par` binds its two results | (before Typing4) |
| 2 | `I` keyed by region BASE; Shared / Ext / Assn₄ / safe₄ named | 43c4d23 |
| 3 | Q6's typed configuration; scope = typed configurations; preservation OWED | c260f41 |
| 4 | N4 in Router4.lean; N4-S with ∃ t and I_b | 980d9d9 |
| 5 | N4-V at the join configuration; EmitsT; the closing compile NT₄.cc | 1a72bb7 |
| 6 | Q6 preservation: the typed configuration and the moves of Ω | 769bd99 |
| 7 | "C5 of a row": PRIMARY the in-layer proof closure, BESIDE root-only, closure with definitions, file-level; declared before `--arm l4` and before any figure | 6caa19f |

**Blindness, what crossed, both directions.** (1) **Lean → MetaPRL, 2026-11-06:** a bus post of mine named the Lean arm's embedding ι (a V-F5-class leak), self-reported on the bus the same minute (STATUS 163). (2) **Lean → MetaPRL, 2026-11-08 06:33–06:37:** the arm ran `git log --oneline -1` in vir's working checkout, then on the sealed branch, and read tip c55fac1's subject: it names `safe₄_par`, says 65 % of the Lean S closure is a reusable library, and gives "S 2,635 vs V 8,382". The arm declared it unprompted, before anyone asked, in its declarations and on the bus; no `l4/` file was opened. **Label at scoring, V-F5's: F6's step-indexed safety predicate and Q4's Lean direction are INFORMED on the MetaPRL arm.** vir's fault as much as its: sealed figures in a commit subject, in a checkout the other arm can reach (FINDINGS V-F7). (3) The MetaPRL arm's declarations, read by vir at the unseal, are what the unseal waits for; they postdate every Lean L4 file, so nothing in the Lean column is informed by them.

## The rows (inputs/L4-programs.md §3), Lean
| row | theorem(s) | file |
|---|---|---|
| N1-T | `N1_typed` | Programs.lean |
| N1-V | `N1_V` — every terminating run of N1 returns 2 (invariant `R1` over ⟶₄*) | Values.lean |
| N1-S | `N1_S` — `{emp} N1 {v. v ∈ ℤ}` under I₁ | Programs.lean |
| N2 | `N2_untyped` — no ⊢₄ typing (Δ cannot give one capability to both `par` sides) | Programs.lean |
| N3 | `N3_typed` · `N3_no_triple` (via `triple₄_invariant`; the release's precondition is the counterexample) | Programs.lean |
| N4-T | `F₄_typed` · `N4_typed` | Router4.lean |
| N4-S | `F₄_S` — each side keeps ℓb's invariant (every bucket ≥ 0) and returns its world as `postF₄ f p t` for the token t it read | Router4.lean |
| N4-V | `N4_V` — at every ⟶₄*-reachable configuration whose two `par` sides are `ret`, each world holds `postF₄` for its thread's token and, for every sender s, the emits naming s across both threads are ≤ g₀(q + s) | RouterV.lean |
| CE | `ce_fwd` · `ce_bwd` (both directions on ⟶ through ι) · `ce_pure` | CE.lean |

## The predictions (amend-21 Q1–Q8), Lean
| | prediction | Lean | verdict |
|---|---|---|---|
| Q1 | L1–L3 untouched (W8) | W8 7f82f94..4017931 over `l1/VIRL1`, `l2/VIRL2`, `l3/VIRL3`: defs 0, theorems 0, new files 0 on each | HOLDS |
| Q2 | no new axiom | `audit-018`: 157 theorems, every one within propext · Classical.choice · Quot.sound; 3 depend on none | HOLDS |
| Q3 | `par₄_rule` C5 ≤ 3 × L2 `frame` C5 | `par₄_rule` is proved from ⟶₄ (Rules4.lean, via `safe₄_par`), no side condition naming a region. **C5 (PRIMARY, addendum 7): `par₄_rule` 1,398 vs L2 `frame` 237, 5.90×.** BESIDE: root-only 126 vs 155 (0.81×) · closure with definitions 3,698 vs 3,749 (0.99×) · file-level 7,273 vs 595 (12.2×) | **FALSIFIED** on the primary reading (> 3×); the root-only and with-definitions readings stay under the line, the file-level over it |
| Q4 | C5(N1-V + N4-V) > C5(N1-S + N4-S) | **V 8,395 vs S 7,557, 1.11** (each a union counted once). BESIDE: root-only 418 vs 1,141 (REVERSES) · with definitions 14,017 vs 10,771 · file-level 12,109 vs 4,722 | direction HOLDS on the primary reading, ratio reported; root-only reverses |
| Q5 | MetaPRL wf rate | Lean: no analogue (0) | — |
| Q6 | a typed configuration has no race, nothing assumed beyond ⊢₄ | `Q6_no_race` (typed configurations, 17ea0e6) and, stronger, `Q6_typed_program`: a closed ⊢₄-typed program, from the empty store and lock table, has no race at ANY ⟶₄*-reachable configuration (`pres₄`, Preserve4.lean); control `N1_no_race` | HOLDS |
| Q7 | CE both directions | `ce_fwd` · `ce_bwd` | HOLDS; C5 2,163 (21 blocks), root-only 644, with definitions 3,978, file-level 1,768 |
| Q8 | one deadlocking program with `{emp} e {_. False}` | `D_triple_false` · `D_blocks` (it reaches `Blocked₄`, never a fault) | reported |

## Red backwards (a mutant that restores the defect, the arm firing where it should)
| mutant | what it restores | where it is red |
|---|---|---|
| 001–005 | (the 26th head's; listed in their commits) | each at its intended obligation |
| 006 | VOID: no decrement, but it stopped at `F₄_S` and never reached N4-V; declared in its commit, not counted | — |
| 007 | the bucket store writes t, not t − 1 (F₄_S stubbed so the build reaches N4-V) | `th_step`'s decrement clause, nowhere else |
| 008 | RT₄'s acquire gives the continuation its capability WITHOUT ownership | `pres₄`'s acquire case and `rt_of`'s acquire case, nowhere else |

## What the Lean arm found, for the paper
- **The value claims need the thread's PROGRESS, not only the shared state.** N4-V's invariant names each thread's stage (a suffix of
  F₄ under the values its lets have bound), whether it has decremented, and the token it read; region invariants alone (N4-S) cannot
  say how many emits there were, which is H5's own finding, now proved on both programs.
- **Naming a thread's stages cost a compiler, not a list.** The stages are `NT₄.cc ρ [] S` for a suffix S of F₄ and ONE expected
  environment ρ per thread: a step binds the value ρ already holds, so the stage's term never changes shape. The substitution lemma
  (`NT₄.cc_subst`) is the one place de Bruijn indices are touched.
- **Preservation at L4 is L2's frame-form preservation with the lock table as part of the frame.** The free locks' regions are a
  shared part (`Shared` with the trivial invariant); acquire moves a region from it into the thread's Ω, release and newlock move
  one back. The same `Shared` serves the triple (Safe.lean) and preservation.

## Limits
- The C5 readings count Lean tokens per `l4/DECLARATIONS-LEAN.md` addendum 7, in-layer: a name in an imported layer is not followed (`L4.*.crossRefs` lists each). Name resolution reads the last dotted component, so an over-match is possible; `l4/C5-NOTES-SEALED.md` is the post-hoc reading of where Q3's and Q4's tokens sit, NOT a scored row.
- N4-V is stated at the configuration the join steps from (both sides `ret`): the last at which both worlds are allocated. Every
  terminating run passes through one; a run that never reaches it is not described by N4-V (whether one exists is a liveness
  question, outside partial correctness, Q8's point).
- Q6's "no race" is by region BASE (two threads' enabled accesses through one ⟨p⟩); a cell-level race across two bases is excluded by
  the store's well-formedness and is not restated (addendum 3).
- The adequacy of the triple (`triple₄_adequate`) is the object's reading of a triple; the triple itself is the thread-local
  safety predicate (addendum 2's reason).
- Mutant 007 stubbed `F₄_S` to reach N4-V; mutant 008 adjusted the two structural lemmas' acquire lines to the mutated rule. Both
  are declared in their commits; neither edit survives (files restored by copy, the next build EXIT=0).

## The MetaPRL column (scored 2026-11-10 by the 60th vir head)

Every MetaPRL figure is a row of `l4/out/counts-l4m.tsv`, produced by the command in `l4/out/counts-l4m.cmd`
(`count.py --arm metaprll4 --base 2d63bef28 --ext d257d2f29`, selftest ARM57, whose units were committed before the arm's first L4
rule). Base 2d63bef28 is the arm's L3-closed sha; d257d2f29 is the sha the arm closed L4 at (its closing census, 2026-11-10 22:56:
17 `virl4_*` modules, 1,464 GROUNDED, 0 UNGR, 0 INCOMPLETE, 0 PRIM). The harness counts the same 1,464 stored derivations there.
Q5's six are the arm's F6 rules on `triple4K` (declarations F15, the re-proof): `triple4K_par`, `triple4K_newlock`, `triple4K_acquire`,
`triple4K_release`, `triple4K_frame`, `triple4K_let`.

⚠️ **LIMIT, beside every MetaPRL figure:** 2d63bef28 and d257d2f29 are in the MetaPRL arm's LOCAL tree and on no public remote at this
commit. The rows are reproducible from the artifacts only once that arm publishes them (as at RESULTS-9).
⚠️ **LIMIT, beside every C5:** a use of `reduce` admits every `virl4_*` reduce rule into the closure, fired or not, so each C5 is an
UPPER BOUND; other resources are not modelled.

| | prediction | MetaPRL | verdict |
|---|---|---|---|
| Q1 | L1–L3 untouched | `virl1/2/3_*` defs edited 0 · rules edited 0 · files changed 0 | **HOLDS** |
| Q2 | 0 prims in `virl4_*` | prims 0 · framework files 0 · 1,464 GROUNDED (the arm's census) | **HOLDS** |
| Q3 | parallel rule from ⟶₄, no side condition naming a region | `triple4K_par`, proved from ⟶₄ through `safe4K`, no region-naming side condition (read by hand, declarations F15). C5 185,852 over 231 rules, root 11,438. BESIDE: L2 `triple_frame` C5 55,583, ratio **3.34** (reported; the 3× line is Lean's only). The first-generation `triple4_par` is 137,287 | **HOLDS** (the statement); ratio reported |
| Q4 | C5(N1-V + N4-V) > C5(N1-S + N4-S) | **V 361,314 (601 rules) vs S 1,439,383 (534 rules), 0.25**. Root-only V 5,473 vs S 13,531 (also reverses). `n4_side` alone is 1,068,014, almost all of it `n4_core` (1,059,883): N4-S re-proves L3's F proof on `triple4K` | **FALSIFIED** on this arm; **INFORMED** |
| Q5 | rate₄ ≥ rate₂ | `[wf]` labels **41/6 vs L2's 42/6**. BESIDE: every `virl4_*` rule 4,417/1,127 · every `virl2_*` rule 3,442/1,170 · L2 program rules + frame 70/12 · `virl2_rules` 269/70 | **FALSIFIED by one label** on the primary reading; the whole-layer reading reverses (3.92 vs 2.94) |
| Q6 | no data race from typing | `q6a`: a `tc4`-typed configuration with `store_ok{s}` has `race4 = bfalse`, for every `k`, `n`, `dl`, `T` (one configuration). Red control closed in both halves (`q6r_tc`, `q6r_race`, counted). Q6b (preservation over ⟶₄*) not proved: the arm priced it at a full port of `virl2_semr` to `tc4m` and recommends no spend before the 11-12 EOD cap | **HOLDS at one configuration**; the reachable-configuration form **UNREACHED** (written at the cap); **INFORMED** (route) |
| Q7 | CE both directions | `ce_step` (one equation for every `s`, `k`, the table carried unchanged: F9's two iffs) · `ce_fault` · `ce_typing` · `ce_tc`. C5 442,676 over 374 rules, roots 231 tok | **HOLDS** |
| Q8 | one deadlocking program, `{emp} e {_. False}` | `q8_deadlock` on `triple4K`, for every `J` with `J 0 [0]`. C5 176,177 over 344 rules | reported |

**The rows (inputs/L4-programs.md §3), MetaPRL:** N1-T `n1_ty` · N3-T `n3_ty` · N4-T `n4_ty` · N1-S `n1_s` (C5 681,625) · N1-V `n1_v`
(85,181) · N3 `n3_nt` (refuted through `adeq4K` at the empty start; 110,088) · N4-S `n4_side` (1,068,014) · N4-V `n4_v` (347,298) ·
erasure `l4succ_erase`, `fault4_erase`, `effstep4_erase`, `lockop_index_erase` (84,629) · adequacy `adeq4K` (105,028). maxSteps 59
(`virl4_ceq:ceP_mk`), under the 11-06 line of ~100. N2 has no MetaPRL theorem (its row is the typing's refusal, read at Q6's control (i)).

### Readings that ride with the figures
- **INFORMED (V-F5's label, FINDINGS V-F7):** F6's step-indexed safety predicate and Q4's Lean direction (the arm read a Lean commit
  subject naming "S 2,635 vs V 8,382" on 11-08); Q6's route (the arm's declared read of a fleet status row of vir's that named a Lean
  route). The Q4 verdict here goes AGAINST the direction the arm read.
- **The two arms' V and Q6 statements are not the same strength, in opposite directions.** MetaPRL's `n4_v` counts at EVERY reachable
  configuration still inside the par; Lean's `N4_V` at the join only (its own Limits). Lean's Q6 includes preservation
  (`Q6_typed_program`); MetaPRL's is one configuration. A cross-arm C5 ratio on Q4 or Q6 compares different theorems.
- **Q6b, written at the cap (2026-11-12, the 70th vir head; STATUS-vir 275): UNREACHED on the MetaPRL arm.** Q6b is preservation of Q6a's race-freedom over ⟶₄*, i.e. at every reachable configuration. The arm's own price, at the object (l4/RESULTS-10-METAPRL-FRAME.md, Q6a and the closing census): a full port of `virl2_semr` to `tc4m`, days of work. The arm recommended no spend before the 11-12 EOD cap. No Q6b proof or attempt was posted on the bus through byte 101,177,676 (15:0x PST), so the cell's "UNREACHED (written at the cap)" is now its own line here. If a Q6b theorem lands at a MetaPRL commit dated before the cap, this line is superseded by it, and not otherwise. Q6 on this arm stays **HOLDS at one configuration**. Lean's Q6 includes preservation (`Q6_typed_program`), so the two arms' Q6 are different theorems (the bullet above).
- **Why V is cheap here:** `n1_v` computes the reach sets by the kernel's rewrites (`l4reach{16} = nil`), so N1-V needed no invariant;
  `n4_v` carries the counting invariant `b(sd) + #{past decrement} = tk sd`. S is dear because `triple4K` does not reuse L3's proof
  object: N4-S re-proves F over copies of L3's four definitions (checked equal to `virl3_eq`/`virl3_tri` after renaming).
- **Statement readings, each checked by hand against the object or the arm's declared term:** N4-S's post is `∃t. 0 ≤ t ∗ …` (a side
  cannot know `b`'s history; forced by a failed check that `l3_fpost` on cells 0…82 depends on `w` alone); N4-V carries `not(p1 = p2)`
  (object-given: each `w` is its own region); N1-S reads `v ∈ ℤ` as `∃n:int. v = venc n`; Q8 carries the `J 0 [0]` premise; no closed
  `adeq4K` instance is proved for Q8 or N1-S (the rows are the triples); `triple4K_free` and N4's par assembly are not claimed.
- **Red controls:** N1-V, N3, Q6a (both halves), the lock rules and Q8 fire as declared. LOCALIZED (driven at a lemma, not by replaying
  the row): N1-S (`n1_nl`), N4-S control (1), N4-V, release (two lemmas), newlock (first clause only). N4-S control (2) was NARROWED
  after a non-firing first run, before its decisive run: weaker evidence than a control declared once. Several are reported (Q) from the
  arm's tools, not re-driven here.
- **Order departures, method rules only, no statement moved:** `lupd` taken in probe before its declaration; route (A)'s amendment and
  its probe closures in the same minute; the N4-S walk helpers declared after the probe and before any count (declared-before-COUNTED).
  The atoms change and route (A) rest on bus posts for declared-before-built, the intermediate declaration hash not being committed.
- **Generations:** frame and let have three proof generations and par two that were proved; the scored rules are the `triple4K` re-proof
  (frame 82,817 · let 87,780 · par 185,852), the first generation beside (75,378 · 81,495 · 137,287). The frame
  (`l4/RESULTS-10-METAPRL-FRAME.md`) carries every per-commit reading this column summarises.
- **What vir got wrong while reading:** at N4-V it accepted the pay store as "the only store to cell 2" while the bucket store also
  matched the emit test (an over-count check missed; caught before scoring); a fleet status row of vir's carried Lean route detail an
  arm could read (the Q6 INFORMED label); `fac9abd14` counted 1,438 rules until the arm committed the missing archive at d257d2f29.
