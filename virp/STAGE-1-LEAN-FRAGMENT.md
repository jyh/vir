# VIR program, Lean arm — stage 1: the router fragment through all six steps

O95, council 2026-11-02 §C. The predictions were pinned first, at vir d558682 (`predictions/PREDICTIONS-amend-11.md`, merged
622c6d4). The where-it-counts clarification is `predictions/PREDICTIONS-amend-12.md`. Everything below is checked Lean 4 +
mathlib (toolchain v4.32.0-rc1, mathlib at salt's pin). Every build ran through the fleet's `saltbuild`, and each was judged
by its `saltbuild EXIT=N` line in `virp/logs/`.

## The design, as declared before the first file (amend-11 D1–D4)
- **Terms: unscoped de Bruijn indices, typing extrinsic.** Index 0 is the innermost binder. Substitution is DEFINED, and its
  lemmas are proved here (V2 counts them).
- **Meaning: ⟦p⟧ : Store → Part (Store × Label).** It uses mathlib's `Part`. There is NO FUEL. Termination is a theorem.
- **Store: typed and region-separated.** The frame buffer, the token buckets and the ACL are separate fields. So the regions
  are disjoint by construction, and `can_access`, `has_tokens` and `dec_tokens` are DEFINED over them. Nothing is uninterpreted.
- **A drop ABORTS.** The meaning of a drop returns the store the call was entered with, as the x86 drop leaves memory unchanged.

## The six steps, file by file
| step | what | file | the rules |
|---|---|---|---|
| 1 | VIR terms (the fragment) | `VIRP/Syntax.lean` | `Atom` (var, lit, MAGIC, len, ≥, =, ∧, can_access, has_tokens; runtime sl/tok/bool), `Tm` (let_lin{dec_tokens}, advance, read_u32, guard, return, drop) |
| 2 | display forms, wf | `VIRP/Syntax.lean` | `Atom.show`/`Tm.show` print A.2's concrete syntax; `Tm.wf n`: every variable bound. `U_wf`, `F_wf` |
| 3 | small-step semantics, DEFINED | `VIRP/Semantics.lean` | `Step`: five rules (let_lin, advance, read_u32, guard-true, guard-false), each substituting a value; `Steps`; `Final` |
| 4 | static semantics | `VIRP/Typing.lean` | `ATy` (atoms BORROW), `Use` (consume: a token is LINEAR, a slice AFFINE), `HasType`: a `return` needs every token consumed, and a `drop` may discard |
| 5 | well-typed programs are safe | `VIRP/Safety.lean` | `progress`, `preservation`, `safety` (a typed closed program never gets stuck), `soundness` (a run to a final configuration computes ⟦e⟧) |
| 6 | the denotation | `VIRP/Semantics.lean`, `VIRP/Safety.lean` | `den`, `denote`; `HasType.den_dom`: a typed program's meaning is DEFINED |
| — | the router | `VIRP/Router.lean` | U (I3: the I2 specs composed) and F (A.3's fused term) as deep terms; `U_typed`, `F_typed`, `U_total`, `F_total`, **`U_eq_F`: ⟦U⟧ = ⟦F⟧ for every store** |

## Added after the first page: the closed form, and the ACL ruling
- `F_closed` (build-012, audit-002 EXIT=0): ⟦F⟧ σ written out as nested ifs over `rd32`, `acl` and `bucket`. It is the form
  paris's backend simulation starts from. Mutant `mutant-003-closedoffset` (emit offset 12 for 24) is RED.
- **Ruled (R), 2026-11-02, at paris's finding:** `canAccess` is defined for any topic, while the machine's ACL bit for a topic
  ≥ 64 lies in another principal's row. F is NOT given a topic guard, because the object is frozen. The layout relation
  carries the aliasing instead, so the backend theorem speaks of RELATED stores only, and the ACL span it separates is
  2^35 + 2^29.

## What was checked
- `virp/logs/build-011.log`: `saltbuild EXIT=0`, the whole library (696 lines in six files, 32 theorems).
- `virp/logs/audit-001.log`: `#print axioms` on 14 theorems. Each is a subset of {propext, Classical.choice, Quot.sound}.
  None has `sorryAx`.
- **Positive control** `virp/logs/audit-control-001.log`: a theorem closed by `sorry` prints `sorryAx` in the same audit.
- **Linearity mutants, both RED as required** (the same typing tactic that proves `F_typed`):
  `mutant-001-toktwice` returns the CONSUMED token, and the unsolved goal is that its slot is `none`;
  `mutant-002-tokdropped` returns without consuming the fresh token, and the unsolved goal is `some tok ∉ Γ'`.

## Readings against the predictions (the author's, until the harness extracts them, STATUS-vir row 76)
- **V1 (Lean):** C4vir = 0. No structure field, `axiom` or `opaque` stands for a VIR operator or code. The `Store` fields are
  the three regions (data), and each operator is a definition over them.
- **V2a (Lean):** 6 stated lemmas mention `subst` (ATy.subst_closed, ATy.subst, Use.subst, HasType.subst,
  Atom.eval_subst, den_subst) — ≥ 3 as predicted. **Reported beside it, not counted under the frozen operator list:** 4
  lemmas about `ins`, the list insertion that is substitution's context/environment counterpart (getElem?_ins, length_ins,
  mem_ins_of_mem, set_ins), and `ATy.weaken`. No `shift` exists, because only CLOSED values are ever substituted.
- **V6 (Lean):** 0 uses of `Part.fix` / `PFun.fix`. ⟦U⟧ and ⟦F⟧ are total by `HasType.den_dom`, a structural induction.
- **V7 (Lean):** progress, preservation and soundness against ⟦·⟧ all close, with no fuel and no primitive step rule.

## Limits
- This is the FRAGMENT: `let_atom`, binops and relops beyond the fragment come next (V3 measures `let_atom`).
- Linearity is enforced syntactically (step 4). The SEMANTIC reading, linear types as resource predicates under a separation
  algebra with the frame rule, is not built yet.
- `rd32` reads 0 out of range and `dec_tokens` saturates at 0. These are definitions chosen here; the layout relation to x86
  (paris's half) is what will test them against the machine. V4 and V5 wait on that.
- `U_eq_F` is I4 at the NEW meaning, and it relies on the abort. On an ACL failure, U drops AFTER `dec_tokens`, so its
  inner result carries a store with one token fewer (visible in the unfolded goal, build-010); F drops before decrementing.
  The two agree only because `abort` returns the entry store on every drop. No mutant drives "without the abort" yet.
