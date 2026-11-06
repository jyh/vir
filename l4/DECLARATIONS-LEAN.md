# L4, the Lean arm's declarations (amend-21, "owed by each arm before its first L4 file")

Written 2026-11-06 by the 25th vir head, on branch l4-lean (cut from the pin, l4-pin e80bd25 and its two successors), ONE commit
after the pin and BEFORE any `.lean` file under `l4/`. **SEALED:** the bus carries only this file's commit sha and sha256 until the
MetaPRL arm has posted its own L4 declarations (FINDINGS V-F5's rule). Both are quoted into the L4 scoreboard.

## The L3-closed sha, and what L4's proofs may cite
- **Lean L3-closed sha: vir 7f82f94** (master, RESULTS-8's commit; the last commit touching `l3/VIRL3` is fa26526, and nothing under
  `l3/VIRL3` changes between them). L4's proofs cite only theorems and definitions of `VIRL1`, `VIRL2` and `VIRL3` present at that sha.
- **L1–L3 are IMPORTED, never edited (Q1).** Q1 reads `count.py --arm w8` over each of `l1/VIRL1`, `l2/VIRL2`, `l3/VIRL3` with
  BASE = 7f82f94 and EXT = this arm's L4-closed sha.

## The representation, and the one choice it forces (declared before any proof, so it is scored, not discovered)
- **`newlock`, `acquire`, `release` are OPS** of a new signature S₄: L2's BTy plus `lock`, L2's Op plus the three, with
  `oArgs`/`oRes` as inputs/L4-programs.md §2 types them. That is L1's own extension point (`ESig`), used as L2 used it.
- **`par e₁ e₂` CANNOT be an op.** L1's `Tm S` is a closed inductive, an op takes ATOMS only, and a λ-thunk cannot carry a capability
  (OBJECT-L3 R-b). So `par` needs a TERM FORMER, and a Lean inductive cannot be extended without editing it, which Q1 forbids.
  ⇒ **Declared: a fresh mutual syntax `Atom₄`/`Tm₄` in `l4/`**, L1's six expression formers plus `par`, over S₄, with a structural
  embedding `ι : Tm S₂ → Tm₄` that CE is stated through. Substitution and well-scopedness are re-stated for `Tm₄`. **This duplication is
  the Lean price of adding a term former, and it is COUNTED in C5, on its own reported line `L4.syntaxCopy`** (W3 (ii)'s analogue, one
  layer up).
- **Rejected, and why:** `par` only in a top-level let-chain (a wrapper over `Tm S₄`). It is cheaper, but it restricts where the
  object allows `par` (OBJECT-L4: `par e₁ e₂` is an expression), so it would be a deviation, not a representation.

## The meaning (H3 (a)) and the triple
- **Configuration** = `Tm₄ × Store₄`, where `Store₄` = L2's `Store` plus a lock table (id ↦ free | held). ⟶₄ is a RELATION:
  `par e₁ e₂` steps either side, and `par (ret v₁) (ret v₂)` steps to `ret (v₁, v₂)`. `acquire` on a held lock has NO step.
- **Blocked ≠ faulted.** `Faults₄ c` = not terminal, no step, and NOT every stuck thread waiting on a held lock. `Blocked₄` names the rest.
  Partial correctness excludes faults only (deadlock is outside, Q8).
- **The triple is defined from ⟶₄ as a THREAD-LOCAL SAFETY predicate** (Vafeiadis, *Concurrent Separation Logic and Operational
  Semantics*, MFPS 2011): `safe₄ n I e σ Q`, step-indexed, where `I` maps lock ids to their invariants (an `Assn` on the region) and
  `acquire`/`release` transfer ownership of the invariant's resource. `Triple₄ I P e Q := ∀ n σ, P σ → safe₄ n I e σ Q`.
  **Why not L2's `Triple` shape directly:** it quantifies over whole-program runs, so it does not compose under another thread's
  interference, and `par`'s rule would not be provable from it. **The object's reading** (L2's triple quantified over every interleaving)
  is the ADEQUACY theorem `triple₄_adequate`: a closed `Triple₄` gives, on every ⟶₄* run, no fault, and every terminal `ret` satisfies Q.
  That theorem is the row the scoreboard reads as the object's triple.

## The rows and their planned files (a renamed file is declared again before it is scored)
`VIRL4/Syntax.lean` (Atom₄, Tm₄, ι, subst) · `VIRL4/Store4.lean` · `VIRL4/Step4.lean` (⟶₄, Faults₄, Blocked₄) · `VIRL4/Typing4.lean` (⊢₄ =
⊢₂'s rules lifted plus four: `par` splits Δ by L2's `Split`, `newlock` consumes a cap, `acquire` returns one, `release` consumes one;
`lock` is unrestricted) · `VIRL4/Safe.lean` (safe₄, Triple₄, `triple₄_adequate`) · `VIRL4/Rules4.lean` (`par_rule`, `newlock_rule`,
`acquire_rule`, `release_rule`, `frame₄`, each proved from ⟶₄; Q3 compares `par_rule`'s C5 with L2's `frame`) · `VIRL4/NoRace.lean`
(Q6: a ⊢₄-typed configuration never has two threads' enabled load/store at one cell outside a held lock) · `VIRL4/CE.lean` (Q7, both
directions on ⟶ through ι) · `VIRL4/Programs.lean` (N1–N4: typing, the refusals N2 and N3, the triples N1-S and N4-S) ·
`VIRL4/Values.lean` (H5 (a): N1-V and N4-V as invariants of the configurations ⟶₄*-reachable from the initial one) ·
`VIRL4/Deadlock.lean` (Q8).

## Where L4 lives
A SEPARATE lake project `l4/` (lib `VIRL4`), requiring `l3` by PATH (which requires `l2`, then `l1`), with mathlib at salt's pin
(packages APFS-cloned from `l3/`, manifest written by edit, never a bare lake update). Every build goes through `l4/logged-build.sh`
(saltbuild, one log per run, `l4/logs/`), and is judged by its `saltbuild EXIT=` line alone. The tactic rule of 11-06 binds: past
~100 tactic applications in one proof, stop and systematize. Time spent building tactics is a separate ledger line.

## ADDENDUM 1 (2026-11-06, the same head, after Syntax/Step4/CE were built and BEFORE any typing or triple file): erratum L4-E1
Restating ⊢₂ for L4 showed that OBJECT-L4 contradicts itself: H1 (a)'s "pair of results … come back joined" against R-a, with N4 untypable
as written. vir wrote errata/ERRATA-L4.md L4-E1 (vir 8e0d3ad, branch errata-l4-e1). Its reading changes ONE thing above: `par` is
`par τ₁ τ₂ e₁ e₂ e`, `let x₁:τ₁, x₂:τ₂ ⇐ par e₁ e₂ in e`, binding the two results (x₁ = #1, x₂ = #0), not a pair-valued expression.
Syntax.lean and Step4.lean were changed to match (build-009 EXIT=0, CE unchanged; audit-002). Everything else above stands.

## ADDENDUM 2 (2026-11-06, the 26th vir head, BEFORE `VIRL4/Safe.lean` exists): what `I` is keyed by, and the shared resource
Declared above: *"`I` maps lock ids to their invariants"*. Written out, that keying cannot be stated thread-locally: `newlock`'s id is the
lock table's LENGTH at the step, and another thread's `newlock` changes it under interleaving, so a `newlock` rule keyed by id would
need the id before the step that fixes it. ⇒ **`I : Int → Assn` is keyed by the BASE of the region a lock guards** (H2 (a): one region
per lock; the base is the consumed capability's own, and a lock's base never changes: `acquire`/`release` keep it). Nothing else above
changes. The pieces `Safe.lean` defines, named here before any proof:
- **`Shared I L σS`**: the resource of the FREE locks of table `L` — for each free lock with base p, a disjoint fragment owning exactly
  region p (L2's `OwnsRegion`) and satisfying `I p`; held locks contribute nothing. (Owning the region IN the invariant is what makes a
  release onto a free lock impossible for a thread that owns the region, which `release_rule` will use.)
- **`Ext L L'`**: the environment's lock-table moves — bases form a prefix (`newlock` appends; `acquire`/`release` keep every base).
- **`Assn₄ := List LockSt → Assn`**: assertions see the lock table (a release needs "ℓ's base is p"), and the fragment.
- **`safe₄ I n e L σ Q`**: at n + 1, a `ret a` evaluates and satisfies Q at EVERY `Ext`-extension of L; and from every admissible global
  state (an `Ext`-extension of L, a `Shared` part, any disjoint frame, the whole L2 store WF) the configuration does not fault (`Faults₄`)
  and every ⟶₄ step lands in an admissible state with the frame untouched and the thread `safe₄` at n.

## ADDENDUM 3 (2026-11-06, the 26th vir head, BEFORE `VIRL4/NoRace.lean` exists): Q6's typed configuration, and its scope
- **A typed configuration is `RT₄ [] [] Ω e τ` with the store owning exactly Ω's regions** (L2's `OwnAll`). `RT₄` is L2's runtime
  typing `RT` restated for `Tm₄`: ⊢₄'s rules plus the runtime operand forms (a capability constant ⟨p⟩ at `load`/`store`/`free`/
  `newlock`/`release` with p ∈ Ω, `ret ⟨p⟩` owning [p]); `Ω` splits across `let` and THREE WAYS across `par` (e₁ · e₂ · the body), as Δ
  does. Its atom typing is mutual with it (`RTA₄`: ⊢₄'s atom rules, λ/fix bodies typed by `RT₄` with Ω = [], plus a lock constant
  ⟨ℓ⟩ : lock), because a lock handle is a non-linear value that substitution can place inside a λ.
- **The race:** `Race e p` = some `par` reachable through evaluation contexts (a `let` head, either `par` side) whose two sides each have
  an ENABLED access (a `load`/`store` at the head, through ⟨p⟩). **Q6 as built: `RT₄ [] [] Ω e τ → OwnAll Ω σ → ¬ Race e p`**, by region
  base. A cell-level race between two DIFFERENT bases is excluded by the store's well-formedness (regions are disjoint) and is not
  restated. "Outside a held lock" needs no clause: a thread inside a critical section owns the region, so the other side cannot hold ⟨p⟩.
- **Declared scope, so no reader takes it for more:** this is Q6 FOR A TYPED CONFIGURATION, the prediction's own words. That every
  ⟶₄*-reachable configuration of a ⊢₄-typed program is RT₄-typed (PRESERVATION through ⟶₄, with acquire adding a base to Ω and release
  removing one) is the stronger reading and is OWED, a separate row (STATUS-vir 164's second half). It is not claimed by this file.

## ADDENDUM 4 (2026-11-06, the 26th vir head, after N4-T and BEFORE any N4-S proof): N4's file, and N4-S's statement
- **N4's rows live in `VIRL4/Router4.lean`**, not `Programs.lean` as planned above: F₄ and N4 are written with names (`NT₄`, L3's `NA`
  reused through ι) and compiled to `Tm₄`, as L3 wrote F. N4-T is there (F₄_typed, N4_typed).
- **N4-S, as this arm states it** (inputs §3: "each keeps ℓb's invariant and gives its own world L3's postcondition"). L3's post-state
  `postF` decrements the bucket INSIDE the world (cell K + sender); at L4 the buckets are the separate region b behind ℓb, so the world's
  post-state cannot mention the bucket and whether F₄ emits depends on the token t read inside the critical section. ⇒ **the world post is
  `∃ t, RegionAt p 83 (postF₄ f p t)`**, where `postF₄` is `postF` with the bucket write removed and `0 < t` in place of `0 < f(bkt)`
  (CODE/PAY written as L3 writes them). The invariant is **`I_b q σ := ∃ g, (∀ s ∈ [0,4), 0 ≤ g (q + s)) ∧ RegionAt q 4 g σ`** for every
  base (only b is ever under a lock). Each side's triple: `{RegionAt p 83 f ∧ ℓb's base is q} F₄[⟨p⟩, ℓb] {v. v = ⟨p⟩ ∧ ∃ t, …}` with
  L3's layout facts (sender, topic < 4) as hypotheses, as R4 takes them. **The relation between t and the emits is N4-V's**, on ⟶₄.
