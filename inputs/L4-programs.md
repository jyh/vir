# L4 inputs — the programs N1–N4 and CE (OBJECT-L4, H1–H5 ruled (a))

**Drafted 2026-11-04 by the 18th vir head; PINNED 2026-11-06 by the 25th with `object-L4/OBJECT-L4.md` and
`predictions/PREDICTIONS-amend-21.md`, in one commit, BEFORE either arm's first L4 file.** Sections §1–§3 and §5 below are the
draft (the file 2026-11-04-vir-L4-PROGRAMS-DRAFT.md in the seat record) byte for byte, except that §5's section number is now §4; the draft's §4
(the predictions) is `predictions/PREDICTIONS-amend-21.md`. H5 was ruled (a) at the pin (OBJECT-L4's status paragraph).

## 1. H5, the fork this draft found: the acceptance values need facts that no region invariant can state
Under H2(a), a lock's invariant is a predicate on the contents of the ONE region it guards. Both of H4's headline facts relate
cells OUTSIDE that region:
- **N1 (the counter):** two threads each increment a locked cell once, and the claim is that the cell ends at **2**. With the
  invariant `I(v) := v ∈ ℤ`, the parallel rule gives each side only "the cell holds some int". The textbook remedy is auxiliary
  state (each thread's contribution as a ghost cell, Owicki–Gries), and CSL with region invariants alone cannot prove 2.
- **N4 (the router, run_tokens over interleavings):** "emits by sender s ≤ s's initial tokens" relates the bucket region (the
  lock's) to the threads' own out cells (not the lock's). That is the same shape.

Options:
- **(a) VALUES ON ⟶₄, SAFETY IN THE LOGIC.** Each value claim is a CONFIGURATION INVARIANT proved by induction on ⟶₄*
  (N1: cell + pending increments = 2; N4: Σ emits(s) + bucket(s) = tokens₀(s)). The triples prove what region invariants CAN
  state: no data race, a bucket never negative, the invariant re-established at every release. No new logic.
- **(b) GHOST STATE.** Add auxiliary cells to the logic (Owicki–Gries style: ghost writes erased by an erasure theorem) and prove
  both values as triples. The logic grows by one construct and one erasure theorem per arm.
- **(c) DROP THE VALUE CLAIMS.** Keep only the safety rows.

**Rec (a).** It measures concurrent separation logic as H2(a) defines it, puts the counting where an inductive invariant over
configurations is the standard tool, and asks neither arm for machinery the object does not name. (b) is the natural L4′ if
the paper wants ghost state measured; its trigger is a claim that cannot be stated as a configuration invariant. (c) loses
the campaign's one program from the layer. **Default (a).**

## 2. Syntax added (OBJECT-L1 §2 concrete syntax, L2's effect binder)
`par e₁ e₂` · `let ℓ:lock ← newlock(c) in e` · `let c:cap ← acquire(ℓ) in e` · `let u:unit ← release(ℓ, c) in e`.
`lock` is a NON-linear type (duplicable into both sides of a `par`); `cap` stays linear. Each lock's invariant is written
beside its `newlock` as `inv(v₀ … vₖ₋₁)`, a predicate on the k cells of c's region. It is DATA for the logic, never part
of the term: erasing it changes no step.

## 3. The programs (N1–N4, at H1–H5 (a))
- **N1 counter.** `let c:cap ← alloc(1) in let c1:cap ← store(c, 0, 0) in let ℓ:lock ← newlock(c1) [inv(v) := v ∈ ℤ] in
  let p ← par (INC ℓ) (INC ℓ) in let c2:cap ← acquire(ℓ) in let x:int ← load(c2, 0) in ret x`, where `INC ℓ` :=
  `let d:cap ← acquire(ℓ) in let y:int ← load(d, 0) in let d1:cap ← store(d, 0, add(y, 1)) in release(ℓ, d1)`.
  Rows: N1-T typed · N1-V **every terminating run returns 2** (on ⟶₄, H5(a)) · N1-S the triple `{emp} N1 {v. v ∈ ℤ}`.
- **N2 race.** As N1 with `newlock` removed and both sides given `c1` directly: **ILL-TYPED** (Δ cannot split one capability
  into two `par` sides). Row: the refutation of `⊢₄`.
- **N3 broken invariant.** A `release(ℓ, d1)` whose cell holds −1 under `inv(v) := v ≥ 0`: **NO TRIPLE**. Row: the triple
  `{emp} N3 {_. True}` is refuted, its counterexample being the release's precondition. (It is TYPED: ⊢₄ does not read
  invariants.)
- **N4 two routers.** One `world` as L3's, except that the bucket cells K … K+NS−1 move into a separate region `b`
  behind ONE lock `ℓb` [inv(v₀…v₃) := every vᵢ ≥ 0]. The wire, ACL, LEN/CODE/PAY cells are split into TWO per-thread copies
  w₁, w₂ (each its own 83-cell region; the ACL is duplicated, not shared). `F₄` is L3's F with its two bucket accesses
  bracketed by `acquire(ℓb)` … `release(ℓb, ·)`. The program is `par (F₄[w₁]) (F₄[w₂])`.
  Rows: N4-T typed · N4-S each side's triple keeps `ℓb`'s invariant and its own region's L3 postcondition · N4-V
  **run_tokens₄**: on every run, for each sender s, the emits naming s across both threads number at most s's initial
  tokens (a configuration invariant on ⟶₄, H5(a)).
- **CE (the conservative extension, on ⟶):** a program with no `par`, `newlock`, `acquire` or `release` steps under ⟶₄ exactly
  as under ⟶₂ (both directions), and its ⊢₄ typing is its ⊢₂ typing.

## 4. What would show this draft unfair
an H5 ruled after an arm's first L4 file · N4's split of the world chosen because one arm already has per-thread stores (the
Lean arm's L2 store is a finite map and splits cheaply, MetaPRL's is a list, so the split is recommended from the object,
not from either arm) · a Q-row whose direction was set after either arm priced its L4.
