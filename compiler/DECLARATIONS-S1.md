# Compiler S1, the declarations (amend-23 "owed before S1's first file": K1's population, K3's whitelist)

Written 2026-11-11 by the 61st vir head, ONE commit after the pin a5edcc7 (OBJECT-COMPILER + amend-23), and BEFORE any `.lean`
file under `compiler/`. A renamed or added file is declared again here before it is scored.

## What S1 may cite
- `VIRL2` and `VIRL1` at master 1189b49 (L2 closed, RESULTS-7; Y5 closed): `Tm₂`, `Atom`, `Step₂`/`Steps₂`, `stepFn₂`,
  `Faults`, `opStep`, `Store`, `HasType₂`, and the L1 `Step`/`stepFn` they lift. **L1 and L2 are IMPORTED and never edited**
  (amend-23 D2's rule, applied to the compiler as well).
- Nothing from `l3/`, `l4/`, `virp/`, `compose/`, `x86compose/`, or any DEFLATE file. Those are PROGRAMS or other campaigns.

## Where S1 lives
- A SEPARATE lake project `compiler/` (lib `VIRC`) beside `l1/` … `l4/`. It requires `l2` by PATH (`../l2`) and mathlib at salt's
  pin, with packages APFS-cloned from `l3/` and the manifest written by edit (never a bare lake update). Every build goes through
  `compiler/logged-build.sh` (saltbuild, one log per run, `compiler/logs/`).
- **Files (planned names):**
  - `VIRC/Fragment.lean`: C2's predicate, a checked `Bool` function (every `lam`/`fix` atom is closed apart from its own
    binders), and its soundness lemma.
  - `VIRC/IR.lean`: the block IR syntax.
  - `VIRC/IRSem.lean`: its small-step semantics over L2's `Store`.
  - `VIRC/Lower.lean`: the compiler function, L2 → IR.
  - `VIRC/Sim.lean`: the match relation and the step lemmas.
  - `VIRC/S1.lean`: the stage theorem `VIRC.s1_refines`.
  - `Audit.lean` and `AuditControl.lean`: `#print axioms`, with a `sorryAx` control.

## The shape of the IR (stated now so that the simulation is not shaped by its proof)
- **A block IR with an explicit frame stack.** Each code position of the source term is a labelled block. A register file holds
  L2 VALUES, read by de Bruijn index from an environment list, so S1 changes control and leaves representation alone. Values
  become words at S2, as the plan says. A `letE τ e₁ e₂` whose `e₁` is not a `ret` pushes a frame (τ, the block of `e₂`, the
  environment). `app` with a closed function value is a CALL to that function's block, and in tail position it is a JUMP with
  no frame. `ite`/`case` are conditional branches. `letOp` is one IR instruction over the same `opStep`.
- **A function value is a label.** Under C2, every `lam`/`fix` atom is closed apart from its own binders, so it needs no
  environment. `fix`'s self-reference is the label itself.
- **The theorem's form (K2: one ∀-program theorem):** for every term e with `Fragment.ok e = true`, and every store σ:
  - each `Steps₂ (e, σ) (ret a, σ')` is matched by an IR run of `lower e` from σ to a return of `⟨a⟩` with σ';
  - each faulting run is matched by an IR run that stops at the IR's one FAULT state;
  - a divergent source run is matched by an IR run with no bound (stated as: every source step is matched by ≥ 1 IR step, with
    the same store).
  L2 is deterministic, so the converse is a corollary and is stated beside it.

## K1's population (S1's builds)
Every `saltbuild EXIT=` line in `compiler/logs/s1-*.log` counts, whether the run was a build, an audit or a mutant run. The count
runs from the first S1 file to the first `EXIT=0` audit that prints `s1_refines` with standard axioms. After that, logs are
named `s2-*`. A run outside that naming is a finding against this arm.

## K3's whitelist (the driver theorem; written now, used at S3)
The constants in the driver theorem's statement (`#print` of its type, every `Name` collected by a harness script) must lie in
`VIRC.*`, `VIRL1.*`, `VIRL2.*`, `X86.*`, or Lean core / Std / Mathlib. **Any constant under `VIRL3.*`, `VIRL4.*`, `VIRP.*`,
`VIRDeflate.*`, `Router.*` or `X86Compose.*` FALSIFIES K3**, and so does any constant whose name contains `router`, `inflate`
or `deflate` (case-insensitive).

## Added 2026-11-11, after S1's forward theorem and before the file exists (the rule above: an added file is declared first)
- `VIRC/Converse.lean`: ⟶₂ is deterministic (through `stepFn₂` completeness; L2 is imported, not edited). Then the converse
  corollary: every IR run of `lowerT e` that FINISHES is matched by a ⟶₂ run that finishes with the related value and the same
  store. It counts in S1's logs as `s1c-*`, reported beside K1's 9 and never folded into it, because K1's declared window
  closed at `s1-audit-001`.

