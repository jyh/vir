# OBJECT-L4 — layer L4, concurrency (locks) (H1(a) H2(a) H3(a) H4(a) H5(a))

**Drafted 2026-11-03 by the 17th vir head (H1–H4) and 2026-11-04 by the 18th (H5, in the programs draft); PINNED 2026-11-06 by
the 25th, BEFORE either arm's first L4 file**, on the Captain's word at the 11-06 council (minute §E 8: *"yes"* to (b), "vir PINS
THE L4 OBJECT now (H1–H5)"): every fork at its stated default, H1 (a) structured `par` · H2 (a) a non-linear lock handle with the
region invariant in the LOGIC · H3 (a) small-step interleaving ⟶₄, no denotation · H4 (a) the router run by two threads plus
three small programs · H5 (a) the VALUE claims (N1's 2, N4's run_tokens₄) as configuration invariants on ⟶₄, the safety claims
in the logic. H5 is stated in `inputs/L4-programs.md` §1, which this pin makes part of the object.
The text from §0 down is the draft byte for byte, except one sentence, which named the predictions file before it had a number:
in the draft's preamble *"Predictions (an amend-20)"*; amend-20 went to SLang on 11-05, so they are amend-21. §1 keeps the forks'
arms as the record of what was ruled; the ruled arm is (a) in each. **Nothing in this file is edited after its pin.** An erratum
goes in `errata/ERRATA-L4.md`. Both arms receive these bytes and nothing else from each other. Predictions:
`predictions/PREDICTIONS-amend-21.md`, in this file's commit.
**Declared at the pin, against §4 below:** §4 names *"a fork ruled before both arms' L3 closes"* as a way this could be unfair.
It applies: the Lean L3 arm is built and public (RESULTS-8), the MetaPRL arm has posted its L3 DECLARATIONS (ae4c349b2,
2026-11-05 16:13, 0 `virl3_` files at it) and has not begun L3's proofs (its L2's Y5 runs to the 11-08 cap). L3 adds no language,
and its MetaPRL declarations precede this pin, so what the pin could hint is L3's PROOFS only. The measurement that would show
it: a `virl3_` file after this sha naming `par`, a lock, or an interleaving. The ruling is his and is recorded, not routed round.

The draft's own preamble, kept as its record:

**Drafted 2026-11-03 ~19:3x PST by the 17th vir head, for a later sitting. NOT PINNED; no arm builds L4 from it.** The layer plan
is the Captain's (OBJECT-L1 "The layers"): *"L4 concurrency (locks)"*, with ONE conservative-extension theorem over L3 (= L2,
since L3 adds no language). The pin is his word; each fork below carries a recommendation and a default. Predictions (amend-21)
are written AFTER the pin and BEFORE either arm's first L4 file, as amend-16 and amend-18 were. It is drafted NOW because both
arms are mid-L3 and the forks below are the ones L2 and L3 deferred to L4 by name.

## 0. What L4 inherits, and the two triggers already on record
- L2's linear capabilities, regions, the semantic triple with a frame rule for every program, the index-fault reading
  (errata L2-E1/E2), and L3's finding that ONE capability out of a term is a real limit (R-a), not a convenience.
- **Two reopening triggers were written down for L4, and L4 is where either would fire:** OBJECT-L3 G2(b) (*"a ⊢₃ that returns a TUPLE of
  capabilities … its trigger is L4 (locks want several capabilities in flight)"*) and OBJECT-L2's L1′ (*"its one reopening
  trigger is L4 wanting capabilities in function types"*). A lock's acquire hands back the regions its invariant owns; a
  thread is a function that holds capabilities. ⇒ L4 is the first layer that EXTENDS ⊢, and its conservative-extension theorem
  is the first that is not the identity. **The recommendations below are chosen so that NEITHER trigger fires** (H1(a) keeps
  threads as `par` branches, not functions; H2(a) keeps one region per lock); the arms that would fire them are named.

## 1. The forks
- **H1 — the concurrency form.** (a) STRUCTURED parallel composition `par e₁ e₂` (both run, interleaved; the result is the pair
  of results; the capabilities split as Δ = Δ₁ ⊎ Δ₂ and come back joined), with CSL's parallel rule
  `{P₁} e₁ {Q₁} ∧ {P₂} e₂ {Q₂} ⇒ {P₁ ∗ P₂} par e₁ e₂ {Q₁ ∗ Q₂}`; (b) `fork e` (an unstructured thread, no join, its
  capabilities given up for good); (c) both. **Rec (a)**: it keeps ⊢'s capability accounting LOCAL (what goes into a `par`
  comes out of it), so linearity stays checkable without a global thread pool, and it is the smallest form under which a lock
  is NEEDED (two threads touching one region). (b) is L5's business if I/O needs daemons. Default (a).
- **H2 — locks and how their resources flow.** (a) a lock is a NON-linear handle `lock` (duplicable, so both sides of a `par`
  can hold it), created by `newlock(c)` which CONSUMES the capability c and its region's invariant; `acquire ℓ` returns that
  capability (linear again) and `release ℓ c` consumes it back; the invariant is a PREDICATE ON THE REGION'S CONTENTS fixed at
  `newlock` (CSL's resource invariant), stated in the logic, never in a type; (b) the same, with the invariant in the TYPE
  (`lock[I]`), which is L1′ (types indexed by assertions); (c) lock-free atomics only (`cas` on a cell), no locks. **Rec (a)**:
  it extends ⊢ only by rules of shapes §4 already has (`par`'s split of Δ; `newlock` / `release` consuming a capability like
  `free`; `acquire` returning one like `alloc`) and needs no L1′;
  the invariant lives where L2's triple already lives. G2(b)'s tuple-returning ⊢ is NOT pulled by (a), because each lock
  guards one region. Default (a).
- **H3 — the meaning.** L2's ⟦·⟧₂ is ONE least fixed point of a FUNCTION (`Part.fix`); interleaving makes a program a
  RELATION. (a) small-step interleaving semantics ⟶₄ with a scheduler-free nondeterministic step, the triple defined from ⟶₄
  (L2's semantic triple, quantified over every interleaving), and NO denotation at L4 — declared, with the conservative-
  extension theorem stated on ⟶ (a `par`-free, lock-free program steps under ⟶₄ exactly as under ⟶₂); (b) a set-valued
  meaning ⟦e⟧₄ ⊆ Val × Store as a least fixed point in a powerdomain, adequacy owed both ways; (c) resumptions / traces.
  **Rec (a)**: it measures what the two logics pay for CONCURRENT SEPARATION LOGIC itself, which is L4's object; (b) and (c) are
  semantics research and would dominate both arms' cost with something the paper does not claim. Default (a).
- **H4 — the acceptance program.** (a) the L3 router run by TWO threads `par (F frame₁) (F frame₂)` over ONE world whose
  bucket region sits behind a lock (the wire and out cells split per thread), and run_tokens restated: over any interleaving the
  emits by sender s are at most s's initial tokens; plus three small programs (a lock protecting a counter incremented twice →
  2; a `par` whose sides share a region WITHOUT a lock → ILL-TYPED; a release of a capability whose contents break the invariant
  → no triple). (b) the small programs only. **Rec (a)**: it carries the campaign's one program through every layer, and the
  interleaved run_tokens is the theorem a concurrent router owes. Default (a).

## 2. What the rows would be (G-style, at the recommendations; written fully at the pin)
the typing of `par`, `newlock`, `acquire`, `release` (⊢₄ = ⊢₂ plus four rules; Δ splits across `par`); the parallel rule and
the three lock rules, proved from ⟶₄ (no rule taken as an axiom); the frame rule still for every program; semantic typing up to
index faults (errata L2-E1/E2 carried up) AND no data race (a configuration where two threads access one cell outside a lock is
excluded by typing); the conservative-extension theorem on ⟶; the acceptance programs of H4.

## 3. What L4 does not contain
`fork` (H1(b)), atomics (H2(c)), a denotation (H3), weak memory, deadlock freedom (a deadlocked program satisfies every partial-
correctness triple — stated, so no reader counts it as missing), I/O, the x86 lowering of threads.

## 4. What would show this draft unfair or premature
a fork ruled before both arms' L3 closes, if either arm's L3 work then reads it as a hint · a prediction written after an arm's
first L4 file · a rec chosen because one arm already has the machinery (the Lean arm has `Part.fix` and would prefer H3(b) for
reuse; the MetaPRL arm's `bar` types would prefer H3(b) too — H3(a) is recommended against both arms' convenience, on the
object).
