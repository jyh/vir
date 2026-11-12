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
