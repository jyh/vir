# K5, the declarations (STATUS-vir 295; amend-23 K5), written BEFORE any K5 file

Written 2026-11-12 by the 67th vir head. **K5:** *"Under C4 (b), the overflow exit is proved UNREACHABLE for DEFLATE's step
whenever n and OUTMAX are < 2³², with no per-input premise."* Falsified if the bound needs a premise on the input, or the exit is
reachable.

## K5-0, a FINDING, recorded before the route: S2's overflow clause is DECLARED and not PROVED
DECLARATIONS-S2.md (l. 39) promises: *"the word machine reaches the OVERFLOW exit only where an IR step would compute an int
outside the range."* No theorem in compiler/VIRC states it. `s2_refines` and `compile_refines` carry `∨ W'.1 = .ovf` in all three
clauses, which is the WEAKER direction. It says a source behaviour is matched OR the machine overflows, and never when it may
overflow. The clause's OTHER half, *"on no run does it produce a different finished value"*, IS proved (`s2_converse`,
`compile_converse`: a word run that finishes is a source answer). Read at the statements 2026-11-12: the only `ovf` theorem in
VIRC is `run_ovf`, an example (Lower2.lean:133). **So K5 cannot be read off the compiler as built: it needs the missing direction first.** This is not a defect in what is
proved. It is a declared clause with no theorem behind it, and K5 is the first prediction that needs it.

## K5-1, the S2 lemma owed (compiler side, generic over L2 programs, K2's form: one ∀-program theorem)
`s2_noovf`: under `s2_refines`'s hypotheses, if every L2 arithmetic primitive the SOURCE run applies returns an int in
[−2⁶³, 2⁶³) (`InRangeRun`, a predicate on the ⟶₂ run: every `.p2` and `.p1` int result is `inRange`), then no word-machine run
in the simulation's image reaches `.ovf`. Route: Sim2's per-step match already relates an IR int result to `chk n`. `chk n = .ovf`
iff `¬ inRange n` (Word.lean l. 43). S1 preserves values (`TRel`), so the IR's int results are the source's.
**InRangeRun is a predicate on the program's VALUES and never on its input bytes.**

## K5-2, the DEFLATE lemma owed (deflate side)
`deflate_inrange`: for n < 2³² and OUTMAX < 2³², every ⟶₂ step of the DEFLATE step term from a world satisfying Safety's `Inv`
applies primitives whose int results lie in [−2⁶³, 2⁶³). Route: `Inv`'s cell bounds already give every value read a magnitude
≤ c·(n + OUTMAX + 3626) (lengths ≤ 15, symbols < 288, cursors ≤ 8n, output ≤ OUTMAX, addresses `IN + n + OUTMAX + k` below L0).
The products are bounded by the step program's own operands (the `imul` the pin added: `wt · 2`, and `acc + x · wt` with
`wt ≤ 2¹⁶` by `kcap`). Per mode, from the mode lemmas in Step.lean. The bound uses n and OUTMAX ONLY, and K5's falsifier is a
premise on the bytes.

## K5-3, the composition
`deflate_noovf := s2_noovf` at DEFLATE's step term with `deflate_inrange` (and `safety`, for the run staying in `Inv`). Its
statement names DEFLATE. It is a statement ABOUT a program, so K3 (the DRIVER names no program) is not touched.

## What would show K5 wrong (findings, never routed around)
- `deflate_inrange` needs a hypothesis on the bytes of b (beyond `x < 256`, D7's open reading);
- some mode's arithmetic genuinely exceeds 2⁶³ at n, OUTMAX < 2³² (then the exit is REACHABLE: K5 FALSIFIED, reported as such);
- `s2_noovf` needs a per-program hypothesis other than InRangeRun (K2/K6's spirit).

## Order
K5-1 first: it is generic, and it closes K5-0 for every program, so the router (K7) gets it too. Then K5-2, then K5-3.

## Addendum 1 (68th head, 2026-11-12, BEFORE any K5 Lean file): K5-1 is split at S1, and the split is declared here
K5-1 is proved in two parts, because Sim2 relates the IR to the word machine and S1 relates the source to the IR.
- **K5-1a `s2_noovf` (S2, in VIRC/NoOvf.lean).** The in-range predicate is stated on the IR run, i.e. on S1's image of the
  program. `Opd.InR ρ o`: every `.prim` sub-operand of `o` that evaluates (`Opd.eval ρ`) evaluates to a value whose int, if it
  has one, satisfies `inRange`. `StepInR I`: the operands the IR step at `I` evaluates are `InR` (`ret o`: o · `letOp _ os _`:
  every o in os · `app f x`: f and x · `ite o`/`case o`: o · `letE`, `done`: nothing). `InRangeRun I₀ := ∀ n I, IRN n I₀ I →
  StepInR I`. **Statement:** under `s2_refines`'s hypotheses and `InRangeRun (.run (lowerT e) ρ₀ [], σ)`, every word run from
  `W₀` (`WN T k W₀ W'`) has `W'.1 ≠ .ovf`. Corollary `s2_refines_noovf`: clause (1) of `s2_refines` without its `∨ .ovf`.
  Route: (i) a pure word-machine fact: a `stepW` to `.ovf` evaluates some head operand to `.ovf`; (ii) `opd_noovf`, by the same
  induction as `opd_sim`: a typed, accepted atom whose IR image is `InR` never evaluates to `.ovf` in the word machine (the only
  `.ovf` sources are `chk` at add/sub/mul, and `InR` gives `inRange` of exactly that result); (iii) `step_noovf` per construct;
  (iv) the run, by induction on the word run, with `stepW` deterministic.
  Sim2.lean is NOT edited: K5-1a is new theorems beside it.
- **K5-1b (S1, owed after K5-1a).** `InRangeRun` on the IR follows from the declared ⟶₂ predicate (every `.p1`/`.p2` int
  result the source run applies is `inRange`), through S1's `Match`/`TRel` (values preserved). Written as its own declaration
  before its file, if the transfer is not a one-line corollary of S1.
- **What would show this wrong:** `s2_noovf` needing a hypothesis beyond `InRangeRun` and `s2_refines`'s own (a finding, K5's
  third falsifier); or an `.ovf` source in `stepW` that no head operand explains (then (i) is false and Word.lean has a fourth
  exit path nobody declared).

## Addendum 2 (68th head, 2026-11-12, after K5-1a PROVED and BEFORE any K5-1b file): K5-1b's statement and route
- **The source predicate.** `Atom.InR₂ a`: every `.prim` sub-atom of a that evaluates (`Atom.eval`) evaluates to an atom whose
  int, if it is one, satisfies `inRange`. `Tm.HeadInR t`: the atoms t's NEXT step evaluates are `InR₂` (`ret a`: a ·
  `letE _ e₁ _`: e₁'s head · `letOp _ as _ _`: every a in as · `app a₁ a₂`: both · `ite a`/`case a`: a). `SrcInRange S₀ :=
  ∀ S, Steps₂ S₀ S → Tm.HeadInR S.1`. This is the declared "every .p1/.p2 int result the source run applies is inRange",
  written per reachable configuration. **It names values only, never input bytes.**
- **Statement.** `compile_noovf`: under `compile_refines`'s hypotheses and `SrcInRange (instL 0 vs e, σ)`, every word run from
  W₀ has `W'.1 ≠ .ovf`. Corollary `compile_refines_noovf`: compile_refines (1) without its `∨ .ovf`.
- **Route.** (a) `ir_step_match`: from `Match I S`, an IR step goes to a finished state, or to a state matched to the SAME S
  (a `letE` push), or to one matched to a ⟶₂ successor of S. The NotLet case is sim_step's own case analysis, re-stated for a
  NotLet code (`step_notlet`, a copy of sim_step's body after its `normalize`, since S1.lean is not edited) plus `src_steps`:
  an IR step forces a ⟶₂ step (through `ARel.eval` and `stepFn₂_sound`). (b) `ir_reach`: every IR state reachable from a
  matched start is finished or matched to a reachable source configuration. (c) `ARel.inR`: a related operand of an `InR₂`
  atom is `InR`. (d) `inRangeRun_of_src`, then `s2_noovf`.
- **What would show it wrong:** an IR state reachable from the start that is neither finished nor matched (then S1's
  simulation has states nobody characterised, a finding about S1), or a hypothesis beyond SrcInRange.

## Addendum 3 (68th head, 2026-11-12, after K5-1b PROVED and BEFORE any K5-2 file): finding K5-2-0, and K5-2's route re-declared
**K5-2-0, a FINDING about this file's own K5-2 route sentence.** It reads *"`Inv`'s cell bounds already give every value read a
magnitude ≤ c·(n + OUTMAX + 3626)"*. Read at Safety.lean l. 50–293 (InvG, facts, InvM), that is FALSE AS WRITTEN: `Inv` bounds
the cells it needs for Φ and the table reads, and leaves others bounded BELOW only, e.g. `cPEND` (`0 ≤ pd` in SNLEN, LENX, DSTD,
DSTX), `cDIST` (`0 ≤ f cDIST` in DSTX), and every cell outside the named ones (no clause bounds an arbitrary cell). The step
program loads `cPEND` 7 times and `cDIST` twice (Step.lean, census of `.load` sites). So `deflate_inrange` CANNOT be read off
`Inv`. This is not yet a K5 falsifier: a missing upper bound in an invariant is not a premise on the bytes, and every value
the program writes is computed from bounded ones. It means K5-2 must carry a bound `Inv` does not.
**Route (declared now; the author's choice, posted with both arms):**
- **(A, TAKEN) a checked runner over the existing traces.** `stepFn₂C` = `stepFn₂` that refuses (returns `none`) when the
  configuration's head atoms are not `InR₂`; `run₂C`. Generic lemma: `run₂C k c = (.ret a, σ')` ⇒ `SrcInRange c` (⟶₂ is
  deterministic, `step₂_det`, so the run's configurations are all the reachable ones, and the last is terminal). Per mode: the
  mode's existing `run₂`-by-`simp` trace (Step.lean, 93 sites) is re-run with `stepFn₂C`; each arithmetic site's range is an
  `omega` side goal from the facts that trace already holds, PLUS a global magnitude invariant `Mag`: every world cell is in
  [0, 2⁴⁰] when n, OUTMAX < 2³² (stated first, proved preserved per mode from the same traces' written values).
- **(B, NOT TAKEN) a generic magnitude checker** over app-free named terms (Fit.lean's `plen` class, 27 of 28 modes) with a
  soundness proof once and a `decide` per mode. Not taken: the mul sites (`8·tb`, `wt·2`, `acc + x·wt`) need per-mode facts
  (`wt ≤ kcap`), so the checker would take per-mode interval hypotheses, which is route A's work in another form, plus a
  soundness proof A does not need.
- **Price, stated before the first file:** A re-runs the mode traces (Step.lean 2,466 lines; 28 modes) with range goals, and
  proves `Mag` preserved. Estimate 1–3 days of builds. If `Mag` fails for some cell (a value that grows without bound across
  steps), K5 is not falsified by that alone (overflow needs an arithmetic site), but `Mag` must then be replaced by that
  cell's own bound, and that is reported.
- **Where:** a NEW project `k5/` requiring `compiler` and `deflate` by path (bridge/'s form: packages APFS-cloned, manifest by
  edit), so neither is edited (D2's spirit; deflate's counts stay put).

## Addendum 4 (69th head, 2026-11-12, after 22 of 28 modes are in range from `Inv` alone, BEFORE any `Mag` file): `Mag` re-declared
**K5-2-1, a FINDING about Addendum 3's `Mag`.** Addendum 3 declares `Mag` as *"every world cell is in [0, 2⁴⁰]"*, proved preserved
per mode. That uniform form is NOT PRESERVED by the step program: three writes double a cell, so no uniform bound is closed under
them — DECODE `x+1 := 2·cv + b` (Step.lean l.1510), BUILD phase 3 `cLEFT := 2·left − c` (l.1044), BUILD phase 2
`cCODE := 2·(code + cp)` (l.1007). Each is bounded only through a COUNTER (l, j). Addendum 3's own fallback applies ("`Mag` must
then be replaced by that cell's own bound, and that is reported"): this is that report. It is not a K5 falsifier.
**Measured before this addendum (k5/K5/Safe1–4.lean, SafeRead.lean, vir f3d47b6):** 22 modes are in range from `Inv` alone with
n, OUTMAX < 2³² — HDR TABLE READ HDRB HDRD SHDR SLEN SCOPY DHDR DH2 DH3 DH4 FIXLENS CLREAD CLPUT LENS LSYM REP SYM SYMD DSTD COPY.
The other six read a cell `Inv` leaves unbounded: SNLEN, LENX, DSTX, LREP (`cPEND`, `cDIST`), DECODE (`x+1`), BUILD (`cLEFT`,
`cREST`, `cTOTAL`, `cCODE`).
**`Mag n om f`, declared now (k5 only; DEFLATE is not edited).** Let em = `f cRET` when `f cMODE = mREAD`, else `f cMODE` (the
mode a READ returns to, as `InvM.read` reads it), and let X = X0 n om.
- **P1** em = SNLEN → 0 ≤ `f cPEND` ≤ 65535. *Made by* SLEN (`pend := acc`, acc < kcap SLEN = 65536); *kept* (READ writes no PEND).
- **P2** em = LENX → 0 ≤ `f cPEND` ≤ 258. *Made by* SYMD (`pend := lb`, lb an LBASE cell of the read-only area, ≤ 258).
- **P3** em ∈ {DSTD, DSTX} or (`f cMODE` = DECODE and `f (X+3)` = DSTD) → 0 ≤ `f cPEND` ≤ 289. *Made by* LENX
  (`pend := pd + a`, pd ≤ 258 by P2, a < kcap LENX = 32).
- **P4** em = LREP → 0 ≤ `f cPEND` ≤ 11. *Made by* LSYM (`pend := 3 | 3 | 11`).
- **D1** em = DSTX → 0 ≤ `f cDIST` ≤ 24577. *Made by* DSTD (`dist := db`, db a DBASE cell, ≤ 24577).
- **C1** `f cMODE` = DECODE → 0 ≤ `f (X+1)` < 2^`f X` (with Inv's 1 ≤ `f X` ≤ 15, so < 2¹⁵). *Made by* reqDecN (l := 1, cv := 0);
  *kept by* DECODE's non-hit branch (l := l + 1, cv := 2·cv + b, b ∈ {0, 1}: 2cv + b < 2^(l+1)).
- **B1** BUILD, phase 2 → 0 ≤ `f cCODE` and `f cCODE` + 636 ≤ 636·2^j (j = `f cINDEX`). *Made by* phase 1's end (code := 0, j := 1:
  636 ≤ 1272); *kept by* `code := 2·(code + cp)`, j := j + 1 with cp a count ≤ nn ≤ 318: 2code + 2cp + 636 ≤ 2(code + 636).
- **B2** BUILD, phase 3 → 0 ≤ `f cLEFT` ≤ 2^j ∧ 0 ≤ `f cREST` ≤ 318·j ∧ 0 ≤ `f cTOTAL` ≤ 318·j. *Made by* phase 2's end (left 1,
  rest 0, total 0, j := 1); *kept by* left := 2·left − c (stored only when ≥ 0), rest/total += c with c a count ≤ 318.
Every other clause is vacuous outside its mode, so a step that does not ENTER one of these modes keeps `Mag` by the frame (the
cells it writes are none of `cPEND cDIST X X+1 cCODE cLEFT cREST cTOTAL`, or it leaves the clause's mode).
**`Mag_init`** (MODE = TABLE: every clause vacuous) and **`Mag_step`** (`Inv ∧ Mag` before a step ⇒ `Mag` after it, for each of
the 28 modes, from Safety's own step lemmas' explicit writes) are owed; with them each of the six wrappers takes its range
facts from `Inv ∧ Mag` as the other 22 take theirs from `Inv`.
**What would show this wrong:** a write to one of these cells not in the census above (re-run it over Step.lean before
`Mag_step`, by `command grep -n 'store \[' | grep -F` per cell name AND per `x" ) (.i k)` offset — the two needle shapes); a
clause that `Mag_step` cannot close (reported as a finding with the cell and the write, never widened silently).

## Addendum 5 (69th head, 2026-11-12, after `Mag.lean` (vir f9d81a3) and BEFORE the DECODE wrapper): clause F1, a gap in Addendum 4
**K5-2-2, a FINDING against Addendum 4 (mine, the same head).** Addendum 4 lists DECODE's unbounded read as `x+1` (cv) only.
Read at the trace (k5/K5/Modes4.lean `decode_step_inR`), DECODE also computes `fs + c` and `2·cv + b − fs` with
`fs = f (tb + 16 + l)`, the table's `first[l]` cell, which no `Inv` clause bounds (`sane` bounds count and offset only) and no
Addendum 4 clause names. Addendum 4's census was by CELL NAME and by `x + k` offset; `first[]` is addressed from `tbb`, a third
shape it did not search. ⇒ the census law for this campaign: search every address SHAPE the program uses (named cell, `x + k`,
`tbb + k (+ j)`, `IN + n + om + k`), not the shapes the author already has in mind.
- **F1** (global, every mode) ∀ t ∈ [0, 2], ∀ l ∈ [1, 15]: 0 ≤ `f (tbase n om t + 16 + l)` ≤ 636·2¹⁶. *Initially* 0 (the tables are
  in the zeroed tail, `initCell_tail`). *Written only by* BUILD (census over Step.lean's `tbb` shape, 2 stores: l.994
  `first[0] := 0`, l.1008 `first[j] := 2·(code + cp)`), and at l.1008 B1 gives code + 636 ≤ 636·2^j with j ≤ 15 and cp ≤ 318, so
  2·(code + cp) ≤ 636·2^16. Every other store's address is outside the 3 × 15 cells (Safety's own table-frame lemmas are the
  route; their use is `Mag_step`'s).
With F1, DECODE's obligations close: cv < 2¹⁵ (C1), fs ≤ 636·2¹⁶ (F1), c and o from `sane`.
