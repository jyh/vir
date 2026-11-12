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
