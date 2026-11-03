# PREDICTIONS amendment 13 — layer L1, the typed pure core (OBJECT-L1), pinned before either arm builds

**Written 2026-11-02 ~17:4x PST by the 11th vir head, BEFORE either arm's first L1 file**, on the Captain's re-ordering of O95
(17:1x–17:3x: generic → practical, the pure core first, *"it is a *typed* language"*). At the commit that adds this file, the
vir tree has no `l1/` project and no L1 file (`git ls-files | grep -E '^l1/|VIRL1'` = 0). On the MetaPRL side, the arm's
last O95 post before this file is the 14:33 BANKING (row 359 part 1: numerals for the HOAS semantics). That work is ROUTER
work, under amend-11. If the MetaPRL arm posts an L1 sha that predates this file, the next amendment says so.

**What was known when this was written**, so that no prediction can claim to be blind to it: on the router fragment (amend-11,
RESULTS-5), the Lean arm measured V1 = 0, V2a = 6, V6 = 0 and V7 closed. The MetaPRL arm measured 43 rules and 0 prims for
steps 1–2, a 19-rule VIR-side variable family, a reflection framework of 23 prims and bar types of 24. Amendments 1–12 are
UNTOUCHED. L1 is a NEW object of measurement. The router's V-scores stay as recorded, and its open items (V1b/V2b/V2c, V3,
the MetaPRL steps 3–6) PAUSE unless L1 needs them.

## Declarations — the Lean arm (fixed here, before its first L1 file)
- **E1. Encoding: unscoped de Bruijn, extrinsic typing, as D1.** `Atom` and `Tm` are MUTUAL inductives (a λ/fix atom holds a
  `Tm`), both parameterised by a signature `Sig` (`B P O : Type` with arities and P's interpretation, OBJECT-L1 §1). L1
  instantiates `Sig₁` with `O = Empty`. `Ty Sig ::= base (b : Sig.B) | arrow Ty Ty`. Shift and substitution are defined once,
  for every `Sig`, over both categories. Every L1 binder lemma is proved for an ARBITRARY `Sig` and is never re-proved per
  instance. That is the operation-set parameter, paid once.
- **E2. Typing is a `Prop`-valued inductive pair** `HasTypeA Γ a τ`, `HasType Γ e τ`. The denotation (OBJECT-L1 §6) is on
  closed terms over one value domain, so it does not recurse on derivations, and typing never needs to live in `Type`.
  Intrinsically-typed terms were the other choice. They would move binder cost into dependent casts, which is the C1 /
  transport column, and D1's reason (keep the two measurements apart) holds unchanged.
- **E2′. THE DENOTATION'S FORM, AND WHO CHOSE IT (a conflict, declared).** OBJECT-L1 §6 was first drafted (in this same
  unpushed commit) with TYPED domains, `⟦τ₁→τ₂⟧ = ⟦τ₁⟧ → ⟦τ₂⟧⊥` as Lean functions. The author, who also builds the Lean arm,
  replaced it before the pin with ONE value domain and semantic types, because the typed reading is not well defined over
  mathlib's flat `Part` once fix returns a function (K5). That reading would need an ω-CPO structure per type and a non-flat
  lifting. The change makes the Lean arm CHEAPER. Its justification is that the uniform reading is CTT's own (bar types over
  PERs of terms) and the commissioned form (`⟦e⟧ : Env → Part Val`, the helm 17:32). A reader who thinks the typed-domain
  reading was the fairer object should count its cost as UNMEASURED on the Lean side, not as zero.
- **E3. Partiality: mathlib `Part`; fix = `Part.fix` (or mathlib's `OmegaCompletePartialOrder.fix`, the arm's call, declared
  in its stage page).** No fuel anywhere. `partial def` is never used. The continuity/monotonicity side condition is proved,
  not assumed.
- **E4. Where it lives:** a NEW lake project `l1/` (lib `VIRL1`), beside virp/ and x86compose/, with mathlib at salt's pin
  (packages APFS-cloned, manifest by edit, never a bare lake update). Every build goes through `l1/logged-build.sh NAME`
  (unique log names in `l1/logs/`) and is judged only by `saltbuild EXIT=N`. `#print axioms` must be ⊆ {propext,
  Classical.choice, Quot.sound}. virp/ and its counts are not touched.

## Declarations owed by the MetaPRL arm BEFORE its first L1 file (posted on the bus, quoted into RESULTS-6)
its encoding of OBJECT-L1 §1's signature (the language type over an operator list), its pinned MetaPRL sha, the files its
L1 theories live in, and its type of partial results (the bar type, as OBJECT-L1 §6 says). The counts below are read from
those files and that sha, so the arm names them first.

## Ruling: a REVIVED theory (the helm's question @[bus] 17:38, written into this file before its pin)
On the MetaPRL side, the language type over an operator list (`itt_hoas_lang`, Lang{sop}) and its λ examples are in
`theories/itt/reflection/obsolete/` at fb8e715. They were moved there 2006-02-13, are commented out of the build, and so are
present at the sha but not built. amend-12's word "existed at the pinned release" is sharpened here, for BOTH arms:
- **FRAMEWORK = present AND BUILT at the pinned release** (MetaPRL: built by the pinned sha's build of the theories the arm
  names, `THEORIES = all` included; Lean: in a library that mathlib or core builds at the pin, so `Archive/` and
  `Counterexamples/` do not count). A file that is present and unbuilt is not something the logic gives for free.
- **A revived theory is VIR-side, every rule of it, whether it builds verbatim or needs a port** to today's BTerm.
- **The arm MAY revive it** (reuse is the method's own practice, and building fresh would only cost more for the same
  measurement). Its rules are reported in a separate sub-column, **REVIVED**, inside the VIR-side figure, with the
  port's diff size beside it. So W2 and W3b show both the total and how much of it was old work brought back.
- Symmetric case, Lean: anything copied in from outside the built libraries is VIR-side and REVIVED in the same sense.

## Predictions (scored by the harness from the artifacts; each extractor is added red first, before scoring)
- **W1 (VIR-specific primitives = 0).** For L1, C4vir = 0 on both arms: no `prim` in a VIR L1 theory (MetaPRL), and no
  `axiom` / `opaque` / structure field standing for an L1 construct (Lean). P₁'s operators are DEFINED by their
  interpretation in the logic's integers and booleans. **FALSIFIED for an arm if** C4vir ≥ 1.
- **W1b (framework column).** As V1b: MetaPRL's framework primitives (the reflection theories, the bar types, the integer
  theory the arm's P₁ rests on) are strictly more than Lean's (the axioms `#print axioms` reports across `VIRL1`, ≤ 3).
  **FALSIFIED if** MetaPRL ≤ Lean.
- **W2 (binder lemmas, amend-12's placement rule).** The operator lists are V2's (Lean: `shift`, `subst`, `rename`, and any
  `lift`/`weaken` that `VIRL1` DEFINES; MetaPRL: the reflection theories' binder operators at the pinned sha).
  **W2a: Lean ≥ 6** (two syntactic categories, three binder shapes: λ, fix's two, both lets). **W2c: MetaPRL < Lean.**
  W2b (the MetaPRL count itself) is reported without a threshold, because the router fragment's 19-rule family is known.
  **FALSIFIED** per clause.
- **W3 (THE OPERATION-SET PARAMETER: the open-vs-closed count, restated).** The extension test is: after L1 closes, each arm
  adds, in ONE commit each and without reading the other's, (i) a new PURE OPERATOR (`max : (int,int) → int`), and (ii) a new
  TYPE FORMER with an argument (`τ₁ × τ₂` with pair and projections). The count is how many of the four central definitions
  (term syntax · step relation · typing relation · denotation) each commit EDITS (as opposed to instantiates or adds beside),
  read by `count.py --arm v3`. **Prediction: (i) costs 0 edits on BOTH arms** (Σ is a parameter in both). That is the
  router's V3 asymmetry VANISHING for operators, because the parameter was designed in. **(ii) costs Lean ≥ 3 and MetaPRL
  0**: `Ty`, `Tm` and `HasType` are closed inductives in Lean, and a type former is not in the parameter. **FALSIFIED if** (i)
  is ≥ 1 on either arm, or (ii) is Lean ≤ 2 or MetaPRL ≥ 1.
- **W3b (the parameter's own cost, EXPLORATORY, no direction).** Per arm: the definitions and lemmas whose statement mentions
  the signature parameter beyond the six steps' own, and the hypotheses an L1 theorem carries about Σ (Lean: none beyond the
  arities' well-formedness; MetaPRL: whatever the operator-list language type's gap needs). Reported beside W3.
- **W4 (the backend).** Not in L1. Scored at L3.
- **W5 (the acceptance programs agree).** On `inputs/L1-programs.md` K1–K5, both arms' denotations give 120, ¬Dom, 42, 7 and
  55, and each terminating program has a ⟶* trace to its value. **FALSIFIED if** any value disagrees, or an arm cannot state
  K2's ¬Dom without fuel.
- **W6 (partiality is now USED; it was 0 on the router).** Each arm's denotation (OBJECT-L1 §6's lfp Φ) uses its logic's fixpoint (Lean:
  `Part.fix` / ω-CPO `fix`, ≥ 1 use; MetaPRL: the bar types' fix rule, ≥ 1 use), and K2's ¬Dom uses LEASTNESS (fixpoint
  induction) at least once on each arm. **FALSIFIED if** an arm denotes fix without its logic's fixpoint, or proves ¬Dom(K2)
  without leastness.
- **W6b (the fixpoint side condition, EXPLORATORY, no direction).** Lean's continuity / monotonicity lemmas for the
  functional Φ, against MetaPRL's admissibility obligations for the bar type its denotation is taken in: counted per arm (lemmas,
  and C5 proof size).
- **W7 (the six steps close).** Both arms prove, for L1: typing uniqueness, weakening, the substitution lemma, progress,
  preservation, determinism, and soundness of ⟶ against ⟦·⟧ (OBJECT-L1 §§4–6), with no fuel argument and no primitive step
  rule. **FALSIFIED for an arm if** one of them cannot be stated that way. Adequacy (§6 step 6b) is scored when built, and its
  absence does not falsify W7.
- **W8 (conservative extension, scored AT L2).** Both arms prove OBJECT-L1 §8's three clauses without editing an L1
  definition (the edit count reads the L2 commits' diffs of the L1 files, which must be 0). **FALSIFIED for an arm if** that
  count is ≥ 1. Predicted to HOLD on both arms for clauses 1 and 3. Clause 2 (steps correspond) is the one predicted to cost:
  Lean's L1 step relation has no store, so L2 relates the two step relations by a lemma rather than by reuse.
- C1–C6 keep their amend-1..12 definitions on the L1 files and are reported without direction.

## What would show this amendment unfair
an L1 proof file on either arm with a commit time before this file's sha · OBJECT-L1 or `inputs/L1-programs.md` edited after
the pin · W2's operator lists or W3's extension constructs changed after a count is read · an arm that reads the other's L1
files · a MetaPRL count taken from files or a sha the arm did not name first · the two arms given different goal-state
affordances.
