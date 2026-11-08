# RESULTS-7 — layer L2, the imperative core (O95; OBJECT-L2 at vir dec0cdd; amend-16; errata L2-E1, L2-E2)

**Both columns.** The Lean column was published from the branch l2-lean, and the MetaPRL column was added 2026-11-07 (below). Every Lean figure is a row of `l2/out/counts-l2.tsv`
(`harness/count.py --arm l2 l2`, re-derived by `harness/reproduce.sh` at that file's own commit, rc 0) or of
`l2/out/counts-w8.tsv`, or is labelled as something else. The two arms' declarations (amend-16) are quoted here when the
branch is unsealed (STATUS-vir 121); the MetaPRL column is scored when that arm posts L2 closed (STATUS-vir 122).
The Lean L2-closed sha is **dc95b53** (l2-lean).

**The MetaPRL column, scored 2026-11-07 by the 31st vir head.** The arm did not post L2 CLOSED. Its Y5 drive was STOPPED, on
the helm's order @98,656,349, under the Captain's 11-06 rule (*"a FOURTH domain gap before the cap STOPS it and is declared
there"*), and the arm declared Y5 at that stop @98,664,693. Every MetaPRL figure below is a row of `l2/out/counts-l2m.tsv`:
`harness/count.py --arm metaprll2 --base ec912bd80 --ext 73bd3ac0d <clone of mojave's metaprl tree>`. ec912bd80 is the arm's L1-closed sha;
73bd3ac0d is the stop's tip, 19 `virl2_` modules, 1,362 stored rules. The command was re-run at scoring and reproduced byte for byte.
Anything that is not such a row is labelled as something else.

## The declarations (amend-16), both written before the arm's first L2 file, neither arm reading the other's
| arm | file | commit (time) | sha256/16 |
|---|---|---|---|
| Lean | `l2/DECLARATIONS-LEAN.md` | vir 161a6fc (2026-11-03 08:54 PST), SEALED until the MetaPRL post | 0b17b029e13a3bf5 |
| MetaPRL | `theories/vir/DECLARATIONS-L2-METAPRL.md` in mojave's metaprl clone, copied byte for byte to `l2/DECLARATIONS-METAPRL-d3a3f91a7.md` | d3a3f91a7 (10:52 PST), the first commit of mojave/vir-l2 on ec912bd80, 0 `virl2_` files at it | c156e11f78f6a303 |

Both hashes were re-read at the unseal (the Lean file at 161a6fc, the MetaPRL file at d3a3f91a7). The MetaPRL arm's post of its
declarations said it had not read `l2/DECLARATIONS-LEAN.md`, any `l2/` file or this branch, and the Lean branch was not
pushed until after that post. A later MetaPRL text amendment (a99bea205, after the fifth refuter pass) is read when its column is scored.

### The MetaPRL declarations after d3a3f91a7: four departures on Y5, each declared before its count
The `sha256/16` column is this file's convention, measured at scoring from each commit's blob. The arm's own D10 post quoted git
blob ids instead (`46ecd53af3eb5556 → 2e981d3ce87f94d9`). Those name the same two files, under a different hash.
| departure | what it does to Y5 | commit | DECLARATIONS sha256/16 before → after | Lean |
|---|---|---|---|---|
| D8 (ruled (A), @97,423,855) | carves Y5's domain to grammar-sorted terms (`wfs2`) | 9065db501 | d8e336313f96c125 → 41035d70dee6ac8e | by construction (mutual inductive types) |
| D9 (ruled (A′), @97,501,252) | carves Y5's domain to scoped capability names (`scoped`) | abbebbd36 | 41035d70dee6ac8e → d8c0eedca3f1d203 | by construction (de Bruijn Γ + usage mask) |
| D8a (ruled (A″), @97,520,873) | carves a prim's argument list to the object's arity (a D8 amendment) | d478a00ca | d8c0eedca3f1d203 → ed46762f7225cdf1 | by construction |
| D10 (ruled (a), @98,653,117) | widens the arm's index fault to the let congruence (OBJECT-L2 §2, L2-E1/E2) | 517d086da (decl. 73bd3ac0d) | ed46762f7225cdf1 → 37ea118b7bc9fb15 | `IndexFault.letE` |
The file at 73bd3ac0d is copied byte for byte to `l2/DECLARATIONS-METAPRL-73bd3ac0d.md` (sha256/16 37ea118b7bc9fb15).

## The scoreboard (amend-16 Y1–Y8)
| prediction | Lean (l2/) | MetaPRL (mojave) | verdict |
|---|---|---|---|
| Y1 C4vir = 0 | **0** (`L2.C4vir`); axioms beyond the standard three **0** (`L2.C4`, `L2.audit` 205 rows, control 1) | **0** (`L2M.Y1.primFigure`: `virl2_*` prims 0 + framework prims whose own text names a VIR term 0). BESIDE: 3 generic prims added in `itt_bar_list` and `itt_bar_res`; L2's trusted base is 34 prims in 6 files (`L2M.trustedBase.*`; ITT release prims not included) | both HOLD |
| Y2 W8 = 0 | **0** (`W8.defsEdited`, base 37c209e, ext dc95b53; `W8.thmEdited` 0, `W8.newFiles` 0 beside) | **0** (`L2M.Y2.defsEdited`, `virl1_*` at ec912bd80 vs 73bd3ac0d; rules edited 0; one new L1 file beside, `virl1_induct`, amend-19's) | both HOLD |
| Y3 the frame proof uses no ⊢₂ | `L2.Y3.frame` **0**, `L2.Y3.op_frame` **0**, with the proof control live (`L2.Y3.control` 1: closure-004, typing2 9) | **0** on both axes: by name, `virl2_typing` rules in `triple_frame`'s 35-rule closure 0 (control 46 live); by statement, closure rules naming a ⊢₂ term 0 (control 246 live). The arm's refiner dependency set (its D6, 37b871ec8) has no `virl2_typing` member, with its control 3 live. That figure is the arm's, not the harness's | both HOLD |
| Y4 no side condition | **2** explicit binder groups (`L2.Y4.frameExplicitBinders`: R and the triple). Locality is in the four small axioms, one per operation, not in the frame theorem (STAGE limit) | **5** premises as stated (`L2M.Y4.framePremises`): four well-formedness premises (P, R, Q ∈ Assn, e ∈ BTerm{0}) and the triple. No disjointness or locality premise. Ruled (a) MET, with the method not matched to Lean's binder count (STATUS-vir 134) | both HOLD |
| Y5 semantic typing as §5 states it, read with L2-E1 + L2-E2 | `L2.Y5.closed` **1** · `L2.Y5.open` **1** · fuel in their statements **0** · bound premises in ⊢₂ **0** (3 inductives); M3 stays TYPED. Red backwards: `mutant-002` (no-fault triple) EXIT=1, one error, at the IndexFault branch | **NOT PROVED: STOPPED AT D10** (see below). Preservation PROVED (`pres2_aux`); progress, the frame lemma and the reach induction NOT REACHED | Lean HOLDS · MetaPRL STOPPED |
| Y6 M1–M5 agree | **16 of 16** acceptance theorems (`L2.Y6.theorems`): 7 · 5 · ⊥ · ILL-TYPED · 55 | **NOT REACHED**: there is no `virl2_prog` module at 73bd3ac0d (`L2M.Y6` Q); the arm opened SLang at the stop | agreement NOT SCORED |
| Y7 linear-context structure (EXPLORATORY) | mask lemmas **21** (`L2.Y7.maskLemmas`); semantic typing's C5 **1092** lines / **13155** tokens over its 9 route files | the five `virl2_sem*` modules' C5, **of an UNFINISHED proof**: **5,947,819** tokens over 846 stored rules (`L2M.C5tok.virl2_sem` 3,720,543 · `_semr` 2,030,684 · `_sems` 163,474 · `_semt` 32,007 · `_semc` 1,111), stale extras kept out. BESIDE, Y5's departure lines, by statement content: carvings D8+D8a 74 rules / 269,666 tok · D9 1 / 18 · D10 3 / 3,618 (overlap 0) | reported |
| Y8 one least fixed point | `L2.fix` **1**, `L2.continuity` **1**; no fuel | **1** `fix`: `den2c` (`virl2_den.ml:44` at 73bd3ac0d, the bar type's fix over configurations, D4's amendment). This is READ, not a harness row (`L2M.Y8` is Q). The codomain is BTerm{0}, weaker than D4's Val, and the arm declares Val × Store owed | both HOLD (MetaPRL by reading) |

C6 for the Lean arm: **79** logged saltbuild runs (`L2.C6`; one log each: 67 builds · 4 audits · 1 audit control · 4 closures · 2 mutants · 1 scratch).
Binder lemmas (`L2.binder`, the leanp binder row on VIRL2/): **13**.

## MetaPRL Y5: stopped at the fourth departure
- **The stop.** D10 arrived as the arm's own finding @98,646,216. The head-only `is_ifault` read bfalse at every let, so a let
  stuck at an index fault in its bound term was a fault `triple_i` did not permit. Y5 was false as defined. vir ruled (a): give
  `is_ifault` the let congruence, because OBJECT-L2 §2's fault is a configuration with no step. The helm counted D10 as the
  fourth gap under the 11-06 rule and stopped Y5. **The arm and the scorer both read D10 differently** (@98,660,464; @98,663,002):
  D8, D9 and D8a NARROW Y5's domain, while D10 adds no hypothesis and corrects the arm's own definition up to the object, so it
  is an arm DEFECT the drive found, not a carving. Whether that counts as the rule's "fourth domain gap" was the Captain's word.
  **His word, council 2026-11-08: "Yes (a)". The stop STANDS, recorded as the helm's judgment: D10 is a defect in the arm's own definition, not a domain carving; progress, the frame lemma and the reach induction are unreached.**
- **Red backwards (D10).** Mutant 6d015121d (mojave/vir-l2-d10-mutant, never merged) restores the head-only definition. There,
  `is_ifault_let`'s own script leaves `bfalse = <e1's head-only test> in bool` open, which is false at an index-faulting e1.
  **LIMIT: this is "shown unprovable with what was run". It is not refuted by a concrete instance** (no concrete store was built).
- **The parts ledger at the stop** (the arm's, tools 2c55f45 `l2/sem/Y5-PARTS-LEDGER.md`): route steps 1–7 DONE (parts 1–99);
  step 8 PRESERVATION PROVED (parts 100–148, `pres2_aux` at 9f4166b70); progress (`prog2`), the frame lemma and the reach
  induction NOT REACHED. Census at 517d086da: 1,362 rules, every one GROUNDED, 0 INCOMPLETE, 0 PRIM (the arm's count, which
  agrees with `L2M.rules` 1,362).
- **What the gaps say about the method.** D8, D9 and D8a are invariants Lean gets by construction (mutual inductive types, de
  Bruijn contexts, a usage mask), and D10 is a clause Lean's `IndexFault` carries by construction. FINDINGS M-F9 to M-F11 are the
  counterexamples that forced the three carvings. A sorted language type (amend-20, SLang) is the arm's next phase, and L2 restated
  over it would remove D8 and D9. That question goes to the Captain at SLang's landing (STATUS-vir 149).

## The literal §5 formula
OBJECT-L2 §5's semantic-typing statement, read with §5's NO-FAULT triple, is false, twice, in Lean:
`semantic_typing_literal_false` (M3, an out-of-bounds load that is typed) and `A0_typed` + `A0_faults` (alloc(0)). Errata
L2-E1 and L2-E2 permit exactly the INDEX faults, and Y5 is scored against that reading on both arms.

## Limits
- Y4's binder count reads the frame theorem's explicit `( … : … )` groups; its implicit `{P} {e} {Q}` are metavariables.
- The frame rule is cheap by construction of the semantic triple (it quantifies over every frame); a reader comparing arms
  compares the frame theorem AND the four small axioms.
- Y5's open form closes Γ ; Δ by substitution (`Binds`): each available capability is bound to some ⟨p⟩ owning region(p).
  The `fuel` and `bounds` rows are token counts over two statements and three inductive blocks; they can miss a premise
  spelled otherwise, and they say nothing about a premise hidden in a definition the statement names.
- Y7's C5 counts whole files, lemmas used elsewhere included.
- MetaPRL: the departure lines (Y5 BESIDE) count rules whose STATEMENT names the carving or fault predicate. A large rule that
  mentions `wfs2` once is counted whole, so 269,666 is an upper bound on the carving's cost, not its price.
- MetaPRL: Y7's figure is the C5 of an unfinished proof plus whatever the route still needs. It is not comparable to Lean's
  13,155 as a ratio, and no ratio is printed.
- MetaPRL: Y3's name axis can miss a typing rule applied by resolution that is named in no closure text (`L2M.Y3.limit`). The
  arm's refiner dependency set covers that case, but it is the arm's figure.
