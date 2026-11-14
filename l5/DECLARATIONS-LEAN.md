# L5, the Lean arm's declarations (amend-24, "owed by each arm before its first L5 file")

Written 2026-11-13 by the 71st vir head, on branch l5-lean (cut from l5-pin 86402f8: the OBJECT-L5 pin a35589c, amend-24 17ef02f,
erratum L5-E1 86402f8), ONE commit after them and BEFORE any `.lean` file under `l5/`. **SEALED:** the bus carries only this file's
commit sha and sha256 until the MetaPRL arm has posted its own L5 declarations (FINDINGS V-F5's rule, as at L3 and L4). Both are
quoted into the L5 scoreboard.

## The L4-closed sha, and what L5's proofs may cite
- **Lean L4-closed sha: vir 4017931** (RESULTS-10; `git log 4017931..caf23c0 -- l4/VIRL4` reads 0 commits). L5's proofs cite only
  definitions and theorems of `VIRL1`, `VIRL2` and `VIRL3` present at caf23c0, and, for LV8 alone, the DEFLATE and compiler theorems
  amend-24 names (`safety`, `deflate_driver`, `router_refines`) at caf23c0.
- **L5 extends L2, not L4** (OBJECT-L5 J1 (a): *"one conservative-extension theorem over L2"*; L3 adds no language). `par` and the
  locks are not in L5; a library routine called under `par` is not an L5 row.
- **L1–L4 are IMPORTED, never edited (LV1).** LV1 reads `count.py --arm w8` over each of `l1/VIRL1`, `l2/VIRL2`, `l3/VIRL3`,
  `l4/VIRL4` with BASE = 4017931 and EXT = this arm's L5-closed sha.

## The representation, and the choice it forces (declared before any proof, so it is scored, not discovered)
- **L1′ is a NEW type and judgement with an embedding of ⊢₂, never an edit of L2 (LV1's "new, not in place").** L1's `Ty B` and
  `Tm S` are closed inductives; the annotated arrow `τ₁ →[k] τ₂` (erratum L5-E1) is a type former and `ret a [d₁ … d_k]` and the
  lending call are term formers, so none of them fits L1's extension point (`ESig` adds base types and ops only).
  ⇒ **Declared: fresh mutual syntax `Ty₅`, `Atom₅`/`Tm₅` in `l5/`**: L1's formers over S₂ with `arr` carrying `k : Nat`, plus
  `retK (a) (ds : List Nat)` and `callK (τ₂) (a₁ a₂) (cs : List Nat) (e)` (`let x:τ₂, c₁′ … c_k′ ⇐ a₁ a₂ [c₁ … c_k] in e`; x = #k, cᵢ′
  = #(k−i)), with structural embeddings `ιT : Ty₂ → Ty₅` (k = 0 on every arrow) and `ι : Tm₂ → Tm₅`. Substitution, well-scopedness
  and the runtime typing are re-stated for `Tm₅`. **This duplication is the Lean price of a type former, and it is COUNTED in C5 on
  its own reported line `L5.syntaxCopy`**, as `L4.syntaxCopy` was.
- **Δ keeps L2's form**, a mask `List Bool` over Γ (`HasType₂ Γ Δ e τ`); a lent capability is a position. The arrow carries a COUNT
  k, never names or sizes: which region a capability is, and its size, are facts of the logic (L5-E1 (5)).
- **Rejected, and why:** encoding a lending call as k nested L2 `store`-shaped ops. It would type, but it is not a function: the
  callee could not be a λ/fix value passed as an atom, and J1 (a) asks for capabilities in FUNCTION TYPES.

## ⊢₅, the meaning, and the triple
- **⊢₅ = ⊢₂'s rules over `Tm₅` plus three:** `lam`/`fix` at `τ₁ →[k] τ₂` check the body with k fresh `cap` variables in Γ and Δ = exactly
  those (the self variable of `fix` is cap-free); `retK a ds` needs Δ = {ds} exactly and a : τ with `hasCap τ = false`; `callK` needs
  the cᵢ DISTINCT members of Δ, removes them, binds the cᵢ′, and checks e with the rest of Δ plus the cᵢ′. Everything else, including
  `ret`'s Δ = ∅, is L2's.
- **⟶₅ is L2's substitution step over `Tm₅`, plus:** a call steps by substituting the argument and the k capability VALUES ⟨pᵢ⟩ into
  the body, under a return frame; `retK v [⟨q₁⟩ … ⟨q_k⟩]` in that frame steps to e with x := v, cᵢ′ := ⟨qᵢ⟩. No fuel, no step index:
  `fix` is L1's unfolding, as at L2.
- **Semantic typing is proved as L2's Y5 was, SYNTACTICALLY:** a runtime typing `RT₅` (L2's `RT` with return frames) preserved along
  ⟶₅*, plus progress, giving `TripleIF` with index faults only (errata L2-E1/E2 carried up). LV4's "fix case" is read on this proof:
  the per-constructor cases of preservation and progress, C5 per case.
- **The triple is L2's semantic `Triple`/`TripleIF` from ⟶₅**, so a routine's spec is a triple on a `callK`, with each lent region
  as `RegionAt p n f` before and `RegionAt p n f′` after (same p, same n: L5-E1 (5)).
- **CE (LV3):** `ι` commutes with ⟶ in both directions (`Step₂ c c' ↔ Step₅ (ι c) (ι c')`) and `HasType₂ Γ Δ e τ → HasType₅ (ιT Γ) Δ
  (ι e) (ιT τ)`, with `Faults` preserved both ways.

## The routines (J3 (a)), their names and their triples, before their proofs
Each is a closed `fix` value of an annotated arrow; all regions hold `Int` (J2 (a)); bounds are premises in the LOGIC.
- `copyR : (int × int × int) →[2] unit`, (s, d, len): pre `RegionAt ps ns f ∗ RegionAt pd nd g`, `0 ≤ s`, `0 ≤ d`, `s + len ≤ ns`,
  `d + len ≤ nd`, `0 ≤ len`; post the same regions with `g′ i = f (s + (i − d))` for d ≤ i < d + len, `g′ i = g i` otherwise, f unchanged.
  (DEFLATE's back-reference copy is the SAME-REGION case: a separate `copyWithinR : (int × int × int) →[1] unit`, forward byte order,
  overlap allowed, as RFC 1951 requires; whether it collapses into copyR is LV10's to measure, not this file's to decide.)
- `fillR : (int × int × int) →[1] unit`, (d, len, v): `g′ i = v` on [d, d + len), g elsewhere.
- `cmpR : (int × int × int) →[2] bool`, (a, b, len): result = `∀ i < len, f (a+i) = g (b+i)`, both regions unchanged.
- `scanR : (int × int × int) →[1] int`, (from, to, v): the least i ∈ [from, to) with `f i = v`, else `to`; region unchanged.
- `bitR : (int × int) →[1] (int × int)`, (pos_bit, k): Appendix S's `bits(k)` at pos_bit over a byte region: (value, pos_bit + k), the
  region unchanged; pre `pos_bit + k ≤ 8·n`, `0 ≤ k ≤ 16`. **No premise on the contents (LV7)**: a cell outside [0, 256) is read by
  the same arithmetic as at L2 (DEFLATE's `bitAt` over Int) and the post says what it returns.
- **Acceptance (LV8, LV9):** `l5/` re-expresses DEFLATE's step program and the L3 router over these, and proves `safety`'s statement,
  `deflate_driver`'s L2 statement and the router's L3 theorem for the re-expressed terms by citing only the routines' triples.

## Where L5 lives
A SEPARATE lake project `l5/` (lib `VIRL5`), requiring `l3` by PATH (which requires `l2`, then `l1`), and `deflate` by PATH for LV8,
mathlib at salt's pin (packages APFS-cloned from `l4/`, manifest written by edit, never a bare lake update). Every build goes
through `l5/logged-build.sh` (saltbuild, one log per run, `l5/logs/`, the replay filter of k5/LOGS-FILTER.md from the first build),
judged by its `saltbuild EXIT=` line alone. The tactic rule of 11-06 binds: past ~100 tactic applications in one proof, stop and
systematize; tactic-building time is a separate ledger line.

## Planned files (a renamed file is declared again before it is scored)
`VIRL5/Syntax.lean` (Ty₅, Atom₅, Tm₅, ιT, ι, subst) · `VIRL5/Typing5.lean` (⊢₅) · `VIRL5/Step5.lean` (⟶₅, Faults₅) · `VIRL5/CE.lean`
(LV3) · `VIRL5/Runtime5.lean`, `Preservation5.lean`, `Progress5.lean`, `Y5L5.lean` (semantic typing; LV4 per case) ·
`VIRL5/Routines.lean` (the six terms and their typings) · `VIRL5/Specs.lean` (their triples; LV7) · `VIRL5/Deflate5.lean`,
`VIRL5/Router5.lean` (LV8, LV9) · `Audit.lean` (`#print axioms` over every theorem; LV2).

## ADDENDUM 1 (2026-11-13, the same head, BEFORE any `.lean` file under `l5/`): three representation facts the text above left loose
Writing `Syntax.lean` against L1's substitution showed three places where the text above cannot be implemented as written. Each is a
representation choice inside L5-E1, not a change of it; nothing in amend-24 moves.
1. **The capability lists are ATOMS, not indices.** `ds`/`cs` are `List Atom₅`: `.var n` at typing time, `⟨p⟩` (`.const (.cap p)`)
   after substitution, exactly as L2's op operands are (`load(.var n, a)`). Index lists could not be substituted.
2. **The judgement carries the count:** `HasType₅ Γ Δ e τ k` reads "e returns a τ and hands back k capabilities". `ret` and L2's
   `retCap` are k = 0; `retK a ds` is k = |ds| with Δ = exactly the ds (distinct); `letE`'s bound term is k = 0; `ite`/`case` give
   both branches the same (τ, k).
3. **The lending call is TWO formers, not one:** `appK a₁ a₂ cs` (a TAIL call that lends cs = exactly its Δ and returns the callee's
   (τ₂, k)) and `letK τ j e₁ e₂` (`let x:τ, c₁′ … c_j′ ⇐ e₁ in e₂`; e₁ at (τ, j) with Δ₁, e₂ with Δ₂ plus the j new capabilities; x =
   #j, cᵢ′ = #(j−i)). The `callK τ a₁ a₂ cs e` named above is the derived form `letK τ |cs| (appK a₁ a₂ cs) e`. ⟶₅ then needs NO
   return frame: `letK τ j (retK v qs) e₂` steps to e₂ with x := v and the cᵢ′ := qᵢ, and `letK` steps under its first term as `letE`
   does. L2's `app` stays a former (k = 0, Δ = ∅), so ι is the identity on every L2 former.

## ADDENDUM 2 (2026-11-13, the same head, after Step5/Preservation5 built and BEFORE Progress5 exists): ⟶₅ was missing one rule
Porting L2's progress showed a typable configuration with no step: `letK τ 0 (ret a) e₂`. Its head is typed at (τ, 0) by `ret` (k = 0),
which `letK` accepts at j = 0, but `letKRet` fires only on a `retK`. So ⟶₅ gains **`letKRet0`: `letK τ 0 (ret a) e₂` steps to
e₂ with x := ⟨a⟩**, the j = 0 reading of `letKRet` (no capability comes back). It is a gap in the Lean arm's step relation, not in the
object or L5-E1, and it is recorded here before the progress theorem that found it is written. Files changed: Step5 (the rule), CE (its
impossibility on ι's image, like the other three), Preservation5 (its case, `letKRet` with no constants). No amend-24 row moves.

## ADDENDUM 3 (2026-11-13, the same head, BEFORE Progress5 is committed; its first build l5-023 found it): the mirror-image gap
`letE τ (retK a []) e₂` is typable too: a `retK` with the empty list is at (τ, 0), which `letE`'s head accepts, but `letRet` fires
only on `ret`. So ⟶₅ gains **`letRetK0`: `letE τ (retK a []) e₂` steps to e₂ with x := ⟨a⟩** (`retK a []` is `ret a`). The same
files change as for Addendum 2. Two gaps of one class in one hour: the step relation was written from the term formers, not from
the typing rules' (τ, k) pairs, and progress is the theorem that reads it the second way.

## ADDENDUM 4 (2026-11-13, the 72nd head, AFTER bitR at (pos_bit, k) was built (vir 5e2782a, l5-047) and BEFORE any LV8 file): bitR's cursor
The declared argument `pos_bit` forces the routine to divide by 8 on every bit, and with L2's prims (no division) that is a loop
LINEAR in pos_bit (5e2782a's `div8`, by repeated subtraction). A bit reader whose cost per bit grows with the input is the wrong
library routine, and at LV8 it cannot sit inside DEFLATE's step, whose fuel is a constant (`KSTEP`). DEFLATE already keeps its cursor
as (byte, bit) (cells `cBY`, `cBI`). So **`bitR : (int × (int × int)) →[1] (int × (int × int))`, (by, bi, k): the k bits from bit bi
of byte by, least significant first; returns (value, (by′, bi′)), the cursor k bits on**, the region unchanged. Pre: `0 ≤ by`,
`0 ≤ bi ≤ 7`, `8·by + bi + k ≤ 8·n`, k = the count (no k ≤ 16 bound: the proof does not need it). The post states the value as the
SAME function of pos = 8·by + bi as at 5e2782a (`bitsF`), and the cursor as (pos + k) / 8, (pos + k) % 8: the division moves to the
SPECIFICATION and leaves the code. **Still no premise on the contents (LV7).** `div8` and its triple are removed with it (no other
routine used it). 5e2782a stays in the history as the record of the first form; its builds and audit-009 are kept and counted.

## ADDENDUM 5 (2026-11-13, the 72nd head, BEFORE any cost file; LV8-MAP.md infrastructure 2): the COST clause
LV8's statements run the step term at a constant fuel (KSTEP), so a mode that calls a routine fits only if the CALL's step count is
known, and LV8 forbids learning it by unfolding the routine's body. So each routine gains, beside its triple, a **cost lemma**
proved WITH the routine (it is the library's own, not the client's):
`Cost₅ P e n` := for every σ with P σ, framed by any σf (Disj, WF, as in Triple₅), `run₅ n (e, σ ⊎ σf)` is TERMINAL.
⟶₅ is deterministic (Run5.lean's `step₅_det`), so this says the run stops within n steps; with the triple it says where.
The routines' costs are LINEAR in their count argument, `a · len + b`, with a and b constants written in the lemma (no big-O).
For bitR the per-bit constant includes DEFLATE's `BITc` run, counted through the embedding from DEFLATE's own counted steps
(not re-derived). Composition rules (`letE`, `letK`, `letOp`, `ite`, the calls) add the counts, plus one step per head; they live
in `Cost5.lean` with the run lemmas they need. The triples are NOT changed: the cost is a second lemma per routine, so nothing
already scored at 5e2782a…b0c363b is re-proved.

## ADDENDUM 6 (2026-11-14, the 76th head, AFTER LV8's assembly and Router5 and BEFORE any LV9 count is taken): LV9's reading
amend-24 LV9 asks for "the AST nodes removed … COUNTED (per program, per routine)", but it does not define a node. This addendum
defines it, before the first count:
- **A node** is one constructor of `Tm₅` or `Atom₅`. Types (`Ty₅`), ops, constants' payloads and list cells are not nodes; they
  ride inside the node that carries them.
- **A routine atom** is a `.fix τ₁ k τ₂ e` with k ≥ 1. Embedded L2 code has k = 0 everywhere, because ιA writes 0. A routine
  atom counts as ONE node, and its body is the library's, not the program's. It is NAMED by a FINGERPRINT (τ₁, k, τ₂, nodes of
  e), which the instrument computes from the six library definitions themselves (bitR, copyR, fillR, scanR, cmpR, copyWithinR)
  and checks pairwise distinct. A signature alone is NOT distinct: τfill and τcopy are both int × (int × int), so fillR and
  copyWithinR share (int×int×int, 1, unit). This was found while writing the instrument, before any count. A routine atom whose
  fingerprint matches none of the six is printed UNKNOWN, and the harness refuses the log.
- **A call** is one occurrence of a routine atom.
- **Per mode (DEFLATE):** L2 = nodes(`lift₅ m`) for DEFLATE's own mode term m (ιE maps constructor to constructor, so this is
  m's node count). L5 = nodes of that mode's `modes₅` entry. **Removed = L2 − L5**, computed by the harness from the two
  printed numbers and reported WITH ITS SIGN. The modes are the seven entries of `modes₅` that are not `lift₅`: READ, FIXLENS,
  SCOPY, BUILD, DECODE, COPY, REP. Every other mode is `lift₅` of its own term and reads 0 by construction. The harness checks
  that, and does not assume it.
- **Per program:** DEFLATE's total is nodes(ιE `stepT`) − nodes(`stepT₅`). The ROUTER's is nodes(ιE F) − nodes(F₅), with F₅'s
  calls; LV8-MAP Addendum 9 already reads it as 0 and 0 (V-F8).
- **Direction (LV9, per program):** HOLDS iff calls ≥ 1 AND removed > 0. Otherwise FALSIFIED.
- **Instrument:** `l5/Lv9.lean` (`#eval` over the defined terms, one tab-separated `LV9` line per row), run through
  logged-build.sh as `lv9-NNN`. `count.py --arm lv9` reads the newest lv9 log, refuses one without `saltbuild EXIT=0`, and
  recomputes every difference. Its selftest arm is written red first.

## ADDENDUM 7 (2026-11-14, the 76th head, BEFORE any LV4 count is taken): LV4's case cut
Line 40 above reads LV4 on "the per-constructor cases of preservation and progress, C5 per case". This fixes the cut, written
before any per-case figure was looked at:
- **The cases** are the top-level arms of `pres₅` (Preservation5.lean, one arm per `Step₅` constructor, written `  | name …`) and
  of `progress₅` (Progress5.lean, one arm per `RT₅` constructor, written `  | _, …, .name …`). An arm's text runs from its `|` line
  to the line before the next top-level arm, or to the end of the theorem. Nested `|` lines belong to the arm that contains them.
- **C5 per case** is whitespace tokens after comments are stripped, the same strip C5 uses everywhere (`l4_strip`). Lines are
  reported beside.
- **The fix case** is the Step₅ arms that unroll a `fix`: `appFix` (k = 0) and `appKFix` (k ≥ 1, the body checked with its
  annotated Δ). PRIMARY: the LARGER of the two ALONE. LV4 HOLDS iff it is strictly larger than every non-fix arm of both
  theorems. The ratio to the next-largest arm is reported. BESIDE: the two arms summed, which is not the verdict, because summing
  two arms against single arms would favour the prediction. Progress has no fix arm: its fix branch sits inside the `app`/`appK`
  arms, which count as application cases.
- **Instrument:** `count.py --arm l5`, rows `L5.LV4.*`, selftest arm written red first. The same arm reads LV2 from the newest
  `l5/logs/audit-NNN.log` (EXIT=0, each `#print axioms` line within the three, a `sorryAx` count of 0), and refuses a control log.

## ADDENDUM 8 (2026-11-14, the 76th head, BEFORE any LV5 count is taken): LV5's population and its "application or fix case"
- **The L1′ files** are the eight language files planned above (Syntax · Typing5 · Step5 · CE · Runtime5 · Preservation5 ·
  Progress5 · Y5L5) plus the five language helpers the plan did not name, declared here before they are scored: Shift5 · Subst5 ·
  Weak5 · RTSubst5 · SemBase5. The routines, DEFLATE's and the router's files, the logic (Logic5, Ops5) and the cost files are not
  L1′ files.
- **A hit** is one match of CAST_RE (count.py, the L3 Z2 extractor, ≍ included) after comments are stripped.
- **The application or fix case** is the application arms of `pres₅` (appLam · appFix · appKLam · appKFix) and of `progress₅`
  (app · appK), cut as in Addendum 7. LV5 HOLDS iff the total is ≥ 1 AND hits in those arms are ≥ half of the total. Hits per file
  are reported beside.
- Same instrument: `count.py --arm l5`, rows `L5.LV5.*`, its selftest arm written red first.

## ADDENDUM 9 (2026-11-14, the 76th head, BEFORE any harness read of LV7): LV7's content premise, read mechanically
- **A routine's triple** is its `<name>R_spec` theorem in VIRL5 (bitR, copyR, fillR, scanR, cmpR, copyWithinR). LV7 names five
  routines; copyWithinR is the sixth and is reported BESIDE the five.
- **Its content variables** are the binders of the statement typed `Int → Int` (a region's contents).
- **Its premises** are the arrow premises between the statement's last `∀ …,` and `Triple₅`. **A content premise** is a premise
  that names a content variable as a whole word. The precondition's `RegionAt p n f` is the region itself, not a premise.
- LV7 HOLDS iff the five read 0 content premises. Same instrument: `count.py --arm l5`, rows `L5.LV7.*`, selftest arm red first.

## ADDENDUM 10 (2026-11-14, the 76th head, BEFORE any LV10 count is taken): LV10's duplication, read by shape
- **A routine's shape** is its whole atom (`.fix τ₁ k τ₂ body`) printed with EVERY integer constant replaced by `_`. Types,
  operators, primitives, de Bruijn indices, capability counts and the other constants are kept. An element's int encoding can only
  show up as integer constants (widths, bases, masks), so two routines that "differ ONLY in an int encoding of their element"
  have EQUAL shapes. Equal shapes are a necessary condition, and the reading is generous to duplication, which makes it the strict
  test of a prediction of 0.
- **LV10's count** is the number of unordered pairs among the five LV7 names with equal shapes. copyWithinR's pairs are reported
  BESIDE. LV10 HOLDS iff the count is 0. A pair that reads equal is the measured trigger OBJECT-L5 names for polymorphism: a fork
  for a sitting, not a change made here.
- **Instrument:** `l5/Lv10.lean` (`#eval`, one `LV10` line per pair), run as `lv10-NNN`. `count.py --arm lv10` reads the newest
  green log. Its selftest arm is written red first.
