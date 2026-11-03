# Layer L1, the typed pure core: the Lean arm, all six steps (O95; OBJECT-L1 at vir dc44f15; amend-13 E1–E4, amend-14)

**What is proved.** `l1/` is a new lake project (lib `VIRL1`, 843 lines in 7 files, toolchain v4.32.0-rc1, mathlib at salt's
pin, packages APFS-cloned from virp/). Every build went through the fleet's `saltbuild` via `l1/logged-build.sh` and was judged
only by its `saltbuild EXIT=N` line in `l1/logs/`. The library build is `build-012.log`, `saltbuild EXIT=0`.

| step (OBJECT-L1) | where | the theorems |
|---|---|---|
| 1 terms, over Σ | `Syntax.lean` | `Sig` (B, C, P, O + arities, P's interpretation), `Ty`, MUTUAL `Atom`/`Tm` (nested `List Atom` operands), `subst` of a closed value |
| 2 grammar, dforms, wf | `Syntax.lean` | `Atom.wf`/`Tm.wf`, `Tm.IsProgram`, display forms `Atom.show`/`Tm.show` |
| 3 small-step, DEFINED | `Semantics.lean` | `Atom.eval`, the inductive `Step` (6 rules, one context), `Steps`, `stepFn` + `stepFn_sound`, `run_steps` |
| 4 static semantics | `Typing.lean` | `HasTypeA`/`HasTypeL`/`HasType` (Prop); `HasTypeA.unique`, `HasType.unique`; weakening; the substitution lemma (atoms, lists, expressions) |
| 5 safety | `Safety.lean` | canonical forms, `Atom.eval_total`, `preservation`, `progress`, `determinism`, `safety` |
| 6 the denotation | `Denot.lean` | `Φ`, `Φ_cont` (ω-Scott continuity), `den := Part.fix Φ`, `den_unfold` (THE UNFOLDING EQUATION), `soundness` / `soundness_steps` / `den_of_steps`, `den_typed` (SEMANTIC TYPE SOUNDNESS, by the fixpoint's approximations) |
| Σ₁ | `L1.lean` | `S₁` (int, bool; the nine operators of §1's table, DEFINED), `O = Empty`, `lawful`, and the step-5/6 theorems at Σ₁ with no hypothesis on Σ left |
| K1–K5 | `Programs.lean` | each typed; K1/K3/K4/K5 ⟶* `ret a` with ⟨a⟩ = 120 / 42 / 7 / 55 and `den` = that value; **K2 `¬ (den K2).Dom`**, by the approximation chain (`Part.Fix.mem_iff`): LEASTNESS, not the unfolding |

**Axioms.** `l1/Audit.lean` prints 35 theorems (`logs/audit-001.log`, EXIT=0). Every one depends on a subset of {propext,
Classical.choice, Quot.sound}: 12 on all three, 13 on propext + Quot.sound, 10 on propext alone. The positive control
(`AuditControl.lean`, `logs/audit-control-001.log`) prints `sorryAx` for a sorried theorem, so a clean line means something.
**Mutants** (`l1/mutants/`, each must be RED): M001 claims K1 = 121, M002 claims K2 reaches a `ret`. Both have EXIT=1, failing at
the `rfl` that carries the value.

**How the design calls came out (declared in amend-13 E1–E4, nothing changed after).**
- Σ is a parameter for EVERYTHING, semantics included. The L1 theorems carry exactly two hypotheses about Σ (`Sig.Lawful`:
  P total at its arity, a boolean constant reads as a boolean) plus `S.O → False` (O₁ = ∅) for progress. That is W3b.
- **Substitution is of CLOSED values only** (CBV, closed programs). So no shift is defined, and weakening is at the OUTER end
  of the context, which needs no index arithmetic. That is why the binder-lemma count is low (below).
- The denotation is `Part.fix Φ` over one value domain (OBJECT-L1 §6). The continuity side condition is ONE theorem
  (`Φ_cont`, 12 lines) from mathlib's `ωScottContinuous.bind`/`apply`/`const`. The unfolding equation is then mathlib's
  `Part.fix_eq_of_ωScottContinuous`.

**Counts (PRELIMINARY: read by hand at the object; the harness extractor is owed, red first, before RESULTS-6 quotes them).**
W1 C4vir: 0 (no axiom, opaque or structure field standing for an L1 construct; P₁ is defined by `Prim.interp`). W2a binder
lemmas by amend-13's operator list (`subst`; no `shift`/`rename` defined): **4** (`HasTypeA.subst`, `HasTypeL.subst`,
`HasType.subst`, `HasType.subst0`). **amend-13 predicted ≥ 6, so W2a reads FALSIFIED** pending the harness. The cause is the
closed-value design above: it was not a choice made to move the count (E1 declares de Bruijn and extrinsic typing, and both
hold), and it is recorded as a finding, not routed around. W6: `Part.fix` 1 use (`den`); leastness used in `den_typed` and
`K2_diverges`; W6b: 1 continuity theorem. W7: all six steps close with no fuel and no primitive step rule.

**Not done (declared, nothing cut):** adequacy (OBJECT-L1 §6 step 6b) · the harness rows for W1/W2/W6 on `l1/` and RESULTS-6 ·
W3 (the extension test, after BOTH arms close) · the MetaPRL arm (mojave, building now). The L1→L2 statement (§8) is proved at L2.
