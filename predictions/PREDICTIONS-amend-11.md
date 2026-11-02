# PREDICTIONS amendment 11 — the VIR program (council 2026-11-02 §C), pinned before either arm builds

**Written 2026-11-02 by the 10th vir head, BEFORE either arm's first file of the VIR program.** At the commit that adds this
file: `lean/` and `compose/` hold no de Bruijn term type, no typing relation, no step relation over a store, no `Part`
denotation and no `VIRP` library (`git ls-files lean compose | grep -iE 'bruijn|denot|typing|VIRP'` = 0). On the MetaPRL
side, mojave's last post before this file was its BOOTED at 11:46 (relit by the council); vir asked at 11:47 (the bus) that no bar-type
or VIR-program theory be committed before this sha. If mojave posts a sha that predates this file, the next amendment says so.
P1–P5, Q1–Q5, T1–T5, B1–B4 and amendments 1–10 are UNTOUCHED. This is a NEW object of measurement (a deep embedding with a
semantics and a metatheory), not a re-score of the old ones.

## The program being measured (the Captain's six steps, the helm's rulings, minute 2026-11-02 §C)
1 VIR terms · 2 grammar, display forms, wf rules · 3 a small-step operational semantics, DEFINED (never primitive) and proved
sound against the denotation · 4 the static semantics (a type system: tokens linear, buffers affine) · 5 well-typed programs
are safe (progress + preservation) · 6 the denotation ⟦p⟧ : store → (store × exit label), PARTIAL, NO FUEL, over a typed,
region-separated store (buckets · ACL · buffers as disjoint fragments).
**FRAGMENT FIRST.** The fragment is the router's: operators `guard · read_u32 · advance · let_lin{dec_tokens} · return ·
drop`; atoms `int literal · variable · len · ≥ · = · ∧ · can_access · has_tokens · MAGIC`; programs I3's U (through I2's specs)
and A.3's F. Every prediction below is scored on the fragment through all six steps. A.2's other constructs (`let_atom`, binop,
relop beyond the fragment) come after, and the first of them is the open-vs-closed measurement (V3).

## Declarations (the Lean arm, fixed here before its first file)
- **D1. Binder encoding: UNSCOPED de Bruijn indices, extrinsic typing.** `Tm` is a plain inductive with `Nat` variables; a
  separate inductive `HasType Γ e τ` carries the types and the linear/affine context discipline. Substitution is defined
  (`Tm.shift`, `Tm.subst`, and `Tm.rename` if needed), and its lemmas are proved in the arm.
  *Why this and not the others:* it is the encoding Lean's metatheory practice reaches for when a step relation substitutes.
  Well-scoped `Tm : Nat → Type` would put indices in the term type and make the binder count partly a transport count
  (C1), mixing two measurements. Locally nameless adds cofinite quantification to every typing rule. PHOAS (the encoding of
  vir's earlier L-DEEP, `lean/VIR/Deep.lean`) has no substitution lemmas but pays a **well-formedness tax**: progress and
  preservation need a parametricity/`wf` relation between two instantiations, which Lean cannot derive. The tax would be
  hidden in that relation, so D1 makes the binder cost visible instead.
- **D2. Partiality: mathlib's `Part`** (⟦p⟧ : Store → Part (Store × Label); termination is `(⟦p⟧ s).Dom`, a theorem). If
  mathlib cannot be pinned into vir's lake project under the build law, an in-tree copy of `Part`'s definition (a structure
  with `Dom : Prop` and `get : Dom → α`, ≤ 15 lines, no axioms) is used and counted in the Lean FRAMEWORK column. `partial def`
  is never used (it is opaque to proof). There is no fuel parameter anywhere in the denotation.
- **D3. The store is typed and region-separated.** The I1 operators (`can_access`, `has_tokens`, `dec_tokens`) become DEFINED
  over the store's ACL and bucket regions. They are no longer uninterpreted fields. That is the mechanism behind V1.
- **D4. Library and logs.** The arm lives in a NEW lean_lib `VIRP` (VIR and VIRB counts stay put), every build through
  `lean/VIRB/logged-build.sh`-style unique log names in `lean/VIRP/logs/`, judged only by `saltbuild EXIT=N`,
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.

## Predictions (each FALSIFIED-if is scored by the harness from the artifacts; extractors are added, red first, before scoring)
- **V1 (VIR-specific primitives, 8 → 0).** Under B′ each arm had C4vir = 8 (`state`, `verr`, four operators, two codes).
  In the deep embedding, C4vir = 0 on BOTH arms: no `prim` in a VIR theory file (MetaPRL), and no structure field, `axiom` or
  `opaque` standing for a VIR operator or code (Lean). **FALSIFIED for an arm if** its C4vir ≥ 1.
- **V1b (the framework column, counted beside).** FRAMEWORK primitives = MetaPRL: the `prim` rules the VIR theories rest on
  outside the VIR files (reflection theories `Itt_hoas_*` as mojave's measurement (a) names them, plus the bar-type theory's
  rules); Lean: the axioms `#print axioms` reports across every VIRP theorem, plus the in-tree `Part` copy if D2's fallback is
  taken. Prediction: **MetaPRL's framework column is strictly larger than Lean's** (the bar types alone add ≥ 3 terms with
  wf/intro/elim rules, all primitive by the PER semantics; Lean's column is ≤ 3). **FALSIFIED if** MetaPRL ≤ Lean.
- **V2 (binder lemmas).** A BINDER LEMMA is a stated theorem/lemma/rule in an arm's VIR files whose statement mentions the
  arm's substitution, shift/renaming, free-variable or binding-depth operator. Lean's operator list is fixed by D1 (`shift`,
  `subst`, `rename`, and any `lift`/`weaken` defined in VIRP). MetaPRL's list is the binder operators of the reflection
  theories (`subst`, `bind`, `bdepth`, `var` and siblings) as declared in `Itt_hoas_*` at the MetaPRL sha the arm pins.
  **V2a:** Lean ≥ 3 (at least weakening, the substitution lemma for typing, and one shift/subst commutation).
  **V2b:** MetaPRL = 0 in the VIR files (HOAS substitution is the meta-language's; any lemma the arm needs about it should come
  from the framework). **V2c:** MetaPRL < Lean. **FALSIFIED** per clause. V2b is the clause measurement (b) bears on: if
  `lang`-induction does not carry progress and preservation and the arm builds its own step inductive with depth lemmas,
  V2b fails, and that is the finding.
- **V3 (open vs closed, a count).** After the fragment closes on both arms, each arm adds ONE construct, `let_atom` (with one
  binop), in its own commit. The count is how many of the four CENTRAL DEFINITIONS that commit edits (as opposed to adds
  beside them): the term syntax, the step relation, the typing relation, the denotation. Metatheory proofs and an assembly
  file's operator list are reported beside it, not counted. **Prediction: MetaPRL 0, Lean ≥ 3** (Lean's `Tm`, `Step`,
  `HasType` are closed inductives). **FALSIFIED if** MetaPRL ≥ 1 or Lean ≤ 2.
- **V4 (the backend theorem's hypotheses; paris's theorem, predicted here).** The router fragment's backend theorem (under a
  layout relation, ⟦p⟧ s ↓ = (s′, ℓ) ⇒ the lowered program reaches exit ℓ in a related state) has hypotheses ONLY about the
  layout relation and the related states: **0 per-program hypotheses**, and in particular no `hdisj`-shaped disjointness
  premise outside the relation (X-F1 becomes a property of the relation). **FALSIFIED if** any hypothesis mentions the
  program, a sender bound, or a region disjointness not derived from the layout relation.
- **V5 (exits agree).** On the five exit witnesses of `compose/Compose/Drops.lean` (+ the emit), the label ⟦F⟧ gives equals the
  exit the x86 run takes, label by label, in both arms' denotations. **FALSIFIED if** any of the five disagrees.
- **V6 (partiality is unused by the fragment).** The fragment has no recursion, so its termination theorem uses no fixpoint:
  0 applications of the bar types' fix-intro or fixpoint induction (MetaPRL) and 0 uses of `Part.fix` / `PFun.fix` (Lean).
  **FALSIFIED if** either arm needs one. (The bar types still appear, in ⟦·⟧'s codomain. Their cost on the fragment is the
  `halts`/Dom obligations, reported as C2-class counts without a direction.)
- **V7 (safety and soundness both close).** Both arms prove, for the fragment: progress, preservation, and the small-step
  semantics sound against ⟦·⟧ (a terminal step sequence from s ends in ⟦p⟧ s). No direction on size. **FALSIFIED for an arm
  if** it cannot state one of the three without a fuel argument or a primitive step rule.
- C1–C6 keep their amend-1..10 definitions on the new files and are reported without direction.

## What would show this amendment unfair
a VIR-program proof file on either arm with a commit time before this file's sha · the operator lists of V2 widened or
narrowed after a count is read · an arm that reads the other's VIR-program files · V3's construct chosen after either arm
has seen the other's extension · the MetaPRL framework count taken from anything but mojave's measurement (a) and the pinned
MetaPRL sha.
