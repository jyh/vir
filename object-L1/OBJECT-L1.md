# OBJECT-L1 — the VIR pure core (layer L1), the object both arms mechanise

**Written 2026-11-02 ~17:4x PST by the 11th vir head, BEFORE either arm's first L1 file**, on the Captain's re-ordering of O95
the same afternoon (generic → practical; his words: *"Let's try to get the pure core done asap … Note that it is a *typed*
language"*). It is the frozen object for layer L1, as `object/` is for the router: **nothing in this file is edited after its
pin.** An erratum goes in `errata/ERRATA-L1.md`. Both arms receive these bytes and nothing else from each other.

The router record (object/, RESULTS-1…5, virp/, x86compose/) STANDS unchanged. It becomes L3's acceptance target: the router
re-expressed as a program in L2. Nothing in L1 mentions buffers, tokens, regions or the store.

## The layers (the plan he took; only L1 is fixed here)
L1 pure core → L2 imperative core (store, regions, `let_lin`, `drop`, region ops, separation logic, a general frame rule) →
L3 the router as an L2 program (re-derive U = F, `run_tokens`, the frame property) → L4 concurrency (locks) → L5 stdlib (I/O
as traces). Each layer k+1 comes with ONE conservative-extension theorem over layer k (§8).

## 1. The signature Σ (the operation-set parameter)
The language is parameterised by a signature Σ = (B, P, O):
- **B** — a set of BASE TYPES. L1: `B₁ = {int, bool}`.
- **P** — PURE OPERATORS. Each `p ∈ P` has an arity `ar(p) = (β₁, …, βₖ) → β` over base types and a TOTAL interpretation
  `⟦p⟧ : ⟦β₁⟧ × … × ⟦βₖ⟧ → ⟦β⟧`. L1's `P₁`:

  | p | arity | ⟦p⟧ |
  |---|---|---|
  | `add` `sub` `mul` | (int, int) → int | + − × on ℤ |
  | `lt` `le` `eq` | (int, int) → bool | < ≤ = on ℤ |
  | `and` `or` | (bool, bool) → bool | ∧ ∨ |
  | `not` | (bool) → bool | ¬ |

  `int` is the mathematical integers ℤ (unbounded). A bit width belongs to the lowering, never to L1. Division and remainder
  are NOT in P₁: they are partial on ℤ, and an atom is total by definition.
- **O** — EFFECT OPERATORS, each with an arity `(τ₁, …, τₖ) → τ`. **L1: `O₁ = ∅`.** The binding form that uses them (§2,
  `let x:τ ← o(a⃗) in e`) is fixed NOW, in L1's grammar, so that every later layer's operations reuse L1's binders and L1's
  binder lemmas. Its typing rule is in §4. In L1 it has no instances, so its step and denotation clauses are vacuous.

## 2. Syntax (step 1: the terms)
```
types        τ ::= β                                   (β ∈ B)
                 | τ₁ → τ₂
atoms        a ::= x                                   variable
                 | n                                   integer literal, n ∈ ℤ
                 | true | false
                 | p(a₁, …, aₖ)                         pure operator, p ∈ P, k = |ar(p)|
                 | λ(x:τ). e                           function
                 | fix f(x:τ₁):τ₂. e                    recursive function: f and x are bound in e
expressions  e ::= ret a                               return a value
                 | let x:τ = e₁ in e₂                   sequencing: x is bound in e₂
                 | let x:τ ← o(a₁, …, aₖ) in e          effect operation, o ∈ O: x is bound in e  (no instance in L1)
                 | a₁ a₂                               application
                 | if a then e₁ else e₂
values       v ::= n | true | false | λ(x:τ). e | fix f(x:τ₁):τ₂. e          (closed)
```
- **TYPED, BY ITS SYNTAX.** Every binder carries its type: λ's parameter, fix's parameter and result, and both `let`s. The type
  system (§4) is a relation over this syntax. Types are not inferred, and no binder is untyped (A.2's binders were untyped
  HOAS binders; L1's are not).
- **ANF.** Every operand of an operator, application, `if` or effect operation is an ATOM. The only form that sequences a
  computation is `let x:τ = e₁ in e₂`. Atoms are pure and total. Evaluating an atom never diverges and never fails.
- **Products are NOT in L1** (declared). Several arguments are passed by currying. A product type former is added later only if
  L3 needs one, and V3 (amend-13) measures what adding it costs.
- **Binding.** λ binds x in e. fix binds f and x in e (two binders). Both `let`s bind x in their body. Terms are identified up
  to α-equivalence. Substitution `e[v/x]` is capture-avoiding. A value is closed, so substituting it never captures.
- **Tail position is syntactic.** The tail positions of e are: e itself if e is an application or `ret`; the body of either
  `let`; both branches of an `if`; the body of a λ or fix. An application in tail position is a TAIL CALL. Nothing in the
  semantics allocates a stack frame for it, and the lowering is required not to either (a statement for L3's backend, not for
  L1).
- **Direct style.** The semantics is NOT given by a CPS translation. The stack lives in the lowering. The small-step relation's
  only context is `let x:τ = □ in e₂` (§3).

## 3. Grammar well-formedness and the dynamic semantics (steps 2–3)
**Well-formedness (step 2).** A term is well-formed in a scope X (a finite set of variables) when its free variables are in X
and every operator has its arity's number of arguments. A PROGRAM is a closed, well-formed expression. Display forms present
the concrete syntax above. A rendering of the five programs of `inputs/L1-programs.md` in each arm's display form is part of
step 2.

**Atom evaluation** `⟨a⟩` (on closed atoms, by structural recursion; it is a partial function on raw syntax and TOTAL on well-typed atoms, which is a
lemma owed in step 5): `⟨n⟩ = n`, `⟨true⟩ = true`,
`⟨false⟩ = false`, `⟨p(a⃗)⟩ = ⟦p⟧(⟨a₁⟩, …, ⟨aₖ⟩)` (defined when each argument is a value of the right base type), and a λ or fix
atom is its own value.

**Small-step, call-by-value (step 3), `e ⟶ e′` on closed expressions, DEFINED as an inductive relation (never primitive):**
```
[let-ret]   let x:τ = ret a in e₂             ⟶  e₂[⟨a⟩/x]
[let-step]  let x:τ = e₁ in e₂                ⟶  let x:τ = e₁′ in e₂            if e₁ ⟶ e₁′
[app-λ]     a₁ a₂                             ⟶  e[⟨a₂⟩/x]                      if ⟨a₁⟩ = λ(x:τ). e
[app-fix]   a₁ a₂                             ⟶  e[⟨a₁⟩/f, ⟨a₂⟩/x]              if ⟨a₁⟩ = fix f(x:τ₁):τ₂. e
[if-t]      if a then e₁ else e₂              ⟶  e₁                            if ⟨a⟩ = true
[if-f]      if a then e₁ else e₂              ⟶  e₂                            if ⟨a⟩ = false
```
A TERMINAL expression is `ret a`. ⟶* is the reflexive-transitive closure. [app-fix] substitutes the fix value itself for f,
which is how recursion unrolls. `let x ← o(…)` has no rule in L1, because O₁ = ∅.

## 4. The static semantics (step 4)
Contexts are finite maps Γ = x₁:τ₁, …, xₙ:τₙ. They are ordinary: L1 has no linear or affine discipline, which arrives with
L2's `let_lin`. The judgements are `Γ ⊢ a : τ` and `Γ ⊢ e : τ`.
```
Γ ⊢ x : Γ(x)        Γ ⊢ n : int        Γ ⊢ true : bool        Γ ⊢ false : bool
Γ ⊢ aᵢ : βᵢ (each i),  ar(p) = (β₁,…,βₖ) → β          ⟹  Γ ⊢ p(a₁,…,aₖ) : β
Γ, x:τ₁ ⊢ e : τ₂                                       ⟹  Γ ⊢ λ(x:τ₁). e : τ₁ → τ₂
Γ, f:τ₁→τ₂, x:τ₁ ⊢ e : τ₂                              ⟹  Γ ⊢ fix f(x:τ₁):τ₂. e : τ₁ → τ₂
Γ ⊢ a : τ                                              ⟹  Γ ⊢ ret a : τ
Γ ⊢ e₁ : τ₁,  Γ, x:τ₁ ⊢ e₂ : τ₂                        ⟹  Γ ⊢ let x:τ₁ = e₁ in e₂ : τ₂
Γ ⊢ aᵢ : τᵢ (each i),  ar(o) = (τ₁,…,τₖ) → τ,  Γ, x:τ ⊢ e : τ′   ⟹  Γ ⊢ let x:τ ← o(a₁,…,aₖ) in e : τ′
Γ ⊢ a₁ : τ₁ → τ₂,  Γ ⊢ a₂ : τ₁                         ⟹  Γ ⊢ a₁ a₂ : τ₂
Γ ⊢ a : bool,  Γ ⊢ e₁ : τ,  Γ ⊢ e₂ : τ                 ⟹  Γ ⊢ if a then e₁ else e₂ : τ
```
**Required theorems of step 4:** typing is syntax-directed and UNIQUE (Γ ⊢ e : τ and Γ ⊢ e : τ′ imply τ = τ′), WEAKENING, and
the SUBSTITUTION LEMMA (Γ, x:τ ⊢ e : τ′ and ⊢ v : τ imply Γ ⊢ e[v/x] : τ′), for atoms and for expressions.

## 5. Well-typed programs are safe (step 5)
For a closed `⊢ e : τ`:
- **PROGRESS:** e is terminal, or e ⟶ e′ for some e′.
- **PRESERVATION:** e ⟶ e′ implies ⊢ e′ : τ.
- **SAFETY:** e ⟶* e′ implies that e′ is terminal or steps. No well-typed program gets stuck. This includes every operator
  meeting arguments of the wrong base type, an `if` on a non-boolean, and an application of a non-function.
- **DETERMINISM:** e ⟶ e₁ and e ⟶ e₂ imply e₁ = e₂.

## 6. The denotation is the meaning (step 6)
Partial, with NO FUEL, over ONE value domain, with the types read as PREDICATES on it (semantic types):
```
Val   = ℤ ⊎ 𝔹 ⊎ Fun          Fun = the closed function values of §2 (λ and fix atoms), up to α
⟦e⟧ : Env → Val⊥             Env = finite maps from variables to Val;  ⟦e⟧ρ = ⟦e[ρ]⟧ for the closing substitution e[ρ]
⟦int⟧ = ℤ ⊆ Val    ⟦bool⟧ = 𝔹 ⊆ Val    ⟦τ₁ → τ₂⟧ = { f ∈ Fun | ∀ v ∈ ⟦τ₁⟧. apply(f, v) ∈ ⟦τ₂⟧⊥ }
X⊥ (for X ⊆ Val) = the partial results that, IF defined, lie in X
```
Here `Val⊥` is the logic's own type of partial results: Lean, mathlib's `Part Val`; MetaPRL, the bar type `bar(·)`.
Termination of e is a PROPOSITION (`Dom` / `halts`), proved and never computed by a clock.

**The definition, on closed expressions, is ONE LEAST FIXED POINT** `⟦·⟧ = lfp Φ`, taken in the logic's order of partial
results (pointwise by definedness), where Φ unfolds the language one level:
```
Φ(E)(ret a)                 = ⌊⟨a⟩⌋                       (the atom's value, §3)
Φ(E)(let x:τ = e₁ in e₂)    = E(e₁) >>= (v ↦ E(e₂[v/x]))  (strict bind)
Φ(E)(a₁ a₂)                 = E(e[⟨a₂⟩/x])               when ⟨a₁⟩ = λ(x:τ). e
                            = E(e[⟨a₁⟩/f, ⟨a₂⟩/x])        when ⟨a₁⟩ = fix f(x:τ₁):τ₂. e
Φ(E)(if a then e₁ else e₂)  = E(e₁) or E(e₂), selected by ⟨a⟩
(anything else)             = undefined
apply(f, v) = ⟦(f v)⟧       (so a function's meaning is what calling it means)
```
The fixpoint is a real one in the logic: Lean, `Part.fix` / mathlib's ω-CPO `fix`; MetaPRL, the bar types' fix rule under
admissibility. It is never a fuel-indexed approximation. **Required:** the UNFOLDING EQUATION `⟦·⟧ = Φ(⟦·⟧)`, with whatever
continuity or admissibility side condition the logic demands, and SEMANTIC TYPE SOUNDNESS: `⊢ e : τ` implies `⟦e⟧ ∈ ⟦τ⟧⊥`.

*Why one domain and not typed domains (`⟦τ₁→τ₂⟧ = ⟦τ₁⟧ → ⟦τ₂⟧⊥` as functions of the logic).* With fix at a result type that
is itself a function type (K5's `sum : int → int → int`), a typed reading needs each type to be an ω-CPO and the lifting to
respect the function order. The logic's flat `Part` does not, so its approximations would not form a chain. CTT's own reading
is the uniform one (the bar type is over PERs of TERMS), and so is the form in which this object was commissioned (`⟦e⟧ :
Env → Part Val`). The typed-domain reading is recorded as an option NOT taken (amend-13 says who chose it and why).

**SOUNDNESS of the small-step semantics against ⟦·⟧ (required).** For closed `⊢ e : τ`: e ⟶ e′ implies `⟦e⟧ = ⟦e′⟧`. Hence
e ⟶* ret a implies `⟦e⟧ = ⌊⟨a⟩⌋`.
**ADEQUACY (step 6b, built after L1 closes; L1's close does not wait on it).** For closed `⊢ e : τ`: if `⟦e⟧` is defined with
value c, then e ⟶* ret v with ⟨v⟩ = c. It is declared here so that a later proof of it cannot be called new scope.

## 7. The acceptance programs
`inputs/L1-programs.md` (K1–K5, written with this file and pinned at the same sha) is the fixed suite both arms run. Each arm
proves, per program: its typing, its denotation's value (or `¬Dom` for the divergent K2), and, for each terminating program, a
⟶* trace to that value. The traces follow from soundness plus progress, or are given directly.

## 8. The L1 → L2 conservative-extension statement (written here, PROVED AT L2)
Let L2 extend L1 by a signature Σ₂ ⊇ Σ₁ (B₁ ⊆ B₂, P₁ ⊆ P₂ with the same interpretations, O₂ ⊇ ∅) and a store σ. Let
`⟨e, σ⟩ ⟶₂ ⟨e′, σ′⟩` and `⟦·⟧₂ : Store → (Val × Store)⊥` on closed expressions be L2's semantics. For every closed L1 program `⊢₁ e : β` at a
base type:
1. `⊢₂ e : β` (the typing is preserved verbatim);
2. `e ⟶₁ e′` iff `⟨e, σ⟩ ⟶₂ ⟨e′, σ⟩`, for every σ (the steps correspond, and the store is untouched);
3. `⟦e⟧₂ σ = ⟦e⟧₁ >>= (c ↦ ⌊(c, σ)⌋)`, for every σ (the meaning is L1's, paired with the unchanged store).

**"Conservative" means all three, PROVED WITHOUT EDITING ANY L1 DEFINITION.** L2 may instantiate Σ and add rules, and may
not rewrite an L1 clause. An L2 that has to change an L1 definition to prove this has refuted the parameter design, and that is
recorded as a finding.

## 9. What L1 does not contain (so that no reader counts it as missing)
buffers, slices, tokens, the store, regions, linearity, `drop`, exit labels, the router, the backend, x86 and the lowering,
products, partial operators (division), and A.2's rewrite rules (their L1 analogues, β and constant folding as denotational
equalities, are welcome as additions beside the six steps and are not counted toward L1's close).
