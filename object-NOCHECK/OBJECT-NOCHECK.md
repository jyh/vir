# OBJECT-NOCHECK — proved programs compile with NO index checks (O95, option (iv))

**Pinned 2026-11-25 by the 90th vir head, BEFORE any file of its route**, on the Captain's word at the 11-25 council (ask 4,
option (iv) beside option (iii): *"Yes, accept rec"*). The policy is the one agreed in his 11-15 walkthrough with vir and recorded
in `REVIEW-O95-2026-11.md` :114–121. Predictions: `predictions/PREDICTIONS-amend-26.md`, in this file's commit.
**Nothing in this file is edited after its pin.** An erratum goes in `errata/ERRATA-NOCHECK.md`.

## 0. What exists (read at master e3a8181)
- S2 lowers every `load`/`store` to a bounds test that jumps to ONE fault exit (`compiler/VIRC/Word.lean:99–110`, the `.fault`
  branch of `stepW`). S3 emits it as four instructions per access: `test rax,rax; js FAULT; cmp rax,rdx; jge FAULT`
  (`s3/S3/Lower3.lean`, `gen`'s `load` and `store` cases).
- `S3.compile_x86` (`s3/S3/Cross3.lean`) carries every ⟶₂ run of an accepted program to the machine, in three clauses; clause (2)
  says a FAULTING source run ends at FAULT (or OVF, or RES).
- An L2 `Triple` (`l2/VIRL2/Logic.lean:52`) gives, from any state satisfying its precondition, that **no reachable configuration
  FAULTS** (its first conjunct). The router's L3 triple is carried to the machine by `K7.router_triple_x86` with no router lemma.

## 1. The policy (his, 11-15)
1. **A proved program called internally** gets NO index check: its code has none of the four instructions above.
2. **A proved program called by an external caller without a proof** gets ONE EAGER check of the triple's decidable precondition at
   entry; a failing check goes to FAULT before any effect.
3. **An unproved program** keeps today's lazy per-access checks: `lower3` and `compile_x86` are unchanged in meaning.
Only INDEX checks are in scope. The overflow checks of C4 (b) (`jo` to the OVF exit) stay in every lowering; removing them is K5's
question (unreachability per program), not this object's.

## 2. The target (the route the council named)
- **NC-P, the premise.** `NoFault vs e σ :≡ ∀ c, Steps₂ (instL 0 vs e, σ) c → ¬ Faults c`. Every L2 triple supplies it at any
  state satisfying its precondition (frame ∅), by its first conjunct.
- **NC-W, the word-level consequence.** Under NC-P and `compile_refines`' premises, no word run of the S2 image from `s2_init`'s
  start reaches `.fault`.
- **NC-L, the unchecked lowering.** `lower3u`: `lower3` with the four check instructions of every `load`/`store` omitted and
  nothing else changed.
- **NC-S, the theorem.** `compile_x86_proved`: compile_x86's premises, `lower3u` in place of `lower3`, plus NC-P; its conclusion has
  compile_x86's clauses (1) and (3) and NO fault clause, and no state in it is FAULT.
- **NC-R, the application.** The router triple carried to the machine through `compile_x86_proved`, NC-P discharged from the
  router's L3 triple.

## 3. The forks (each with its recommendation; each proceeds on it under the 08/31 law, both arms posted)
- **N1 — how NC-W is obtained.** (a) DERIVED, whole-run: ⟶₂ and `stepW` are deterministic and `.fault` is terminal, so a word run
  reaching `.fault` against compile_refines' clauses (1) and (3) forces a source run that faults (S1's converse already classifies
  source runs, `compiler/VIRC/Converse.lean` `src_classify`). No S1/S2 file changes. (b) THREADED: NC-P carried as an invariant
  through S1's and S2's forward simulations. **Rec (a)**: it reuses the three clauses as proved and edits no stage. (b) is the
  fallback if (a) meets a clause that does not pin the word run's length.
- **N2 — how the unchecked lowering is built.** (a) ONE FLAG: `Ctx3` gains a field `chk : Bool`, `gen` emits the four instructions
  iff `chk`, `ctxOf` sets `chk := true`, and Sim3's load/store lemmas take the in-bounds fact when `chk = false` (it holds at each
  such step, because the word step there did not go to `.fault`). (b) A COPY: a separate `gen'` and a copy of Sim3 (~6,600 lines
  in `s3/S3/` at e3a8181) in a new directory. **Rec (a)**: (b) duplicates the largest proof in the repository to delete four
  instructions. Under (a) the statement of `compile_x86` must not change; that is a prediction (amend-26 NC5).
- **N3 — the eager entry check (policy 2).** An L2 `Assn` is a `Prop` on stores, so "the triple's decidable precondition" has no
  general form. (a) DEFERRED: policy 2 is a stated limit until NC-S lands; its object (the decidable fragment, the entry code, and
  its theorem) is written then, with its own predictions before its first file. (b) now, with a precondition fragment fixed today
  before any NC-S file has shown what the theorem needs. **Rec (a)**: the council's named route is NC-P → NC-L → NC-S; the entry check
  composes on top of NC-S and is priced separately, outside the 40–80 below.

## 4. Price (an ESTIMATE, the REVIEW's, not a measurement)
40–80 builds and 2–4 vir heads for NC-W, NC-L and NC-S together (REVIEW-O95 :120). **CHECKPOINT:** at 80 logged builds without
`compile_x86_proved` at EXIT=0, the arm stops and posts the translation-validation fallback for S3 (C1 (b): a per-program check
that the program's accesses are in range, then `lower3u` for that program only) BEFORE taking it.

## 5. What this object does NOT claim
no removal of overflow checks · no change to unproved programs' code · no external-caller entry check (N3 (a)) · no claim about
speed (no figure is measured) · no MetaPRL arm (option (iii) is mojave's, separate) · no claim beyond `compile_x86`'s own trust
(XED decode and the S4 differential run).
**What would show this object wrong:** `compile_x86_proved` stated after its proof · `compile_x86`'s statement changed ·
a premise in `compile_x86_proved` beyond compile_x86's and NC-P · an index-check instruction left in `lower3u`'s output, or any other
instruction removed · NC-P discharged for the router by a router-specific lemma rather than from its triple.
