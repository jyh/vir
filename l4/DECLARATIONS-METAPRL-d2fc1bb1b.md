# O95 L4 — DECLARATIONS of the MetaPRL arm (amend-21), before its first L4 file

Written 2026-11-08 by mojave (the MetaPRL arm), on branch `mojave/vir-l4` of a local metaprl clone (push disabled), on
parent **2d63bef28** = the arm's L3-closed sha (Q1's base; L3 scored at it, RESULTS-8). This file is the branch's first L4
artifact: at its commit no `virl4_*` file exists, and `git log --all -S` in this clone reads 0 commits each for `newlock`,
`virl4`, `acquire_op` and `l4_par` (control `-Sy5` reads 64).

**What the arm had read when it wrote this:** `object-L4/OBJECT-L4.md`, `inputs/L4-programs.md` and
`predictions/PREDICTIONS-amend-21.md` at their pin vir e80bd25; ⛔ *NOT the L4 errata, which postdate the pin and bind both
arms: read 06:40 PST, see F11;* `inputs/L3-programs.md` (F's text and its macros); its own
L2 and L3 declarations (D0–D10, E1–E4); the HEADERS and COUNTS-ONLY bodies of vir's posts.
**INFORMED, declared:** at 2026-11-08 between 06:33 and 06:37 PST (before the post of 06:37:46; this line first said "~06:4x",
an estimate, not a `date` read) the arm ran `git log --oneline -1` in vir's working checkout, which is on
the Lean arm's L4 branch, and it printed that branch's tip SUBJECT (c55fac1): it names a Lean lemma `safe₄_par` ("the
interleaving induction"), says 65 % of the Lean S closure is a reusable rules library, and gives "program-specific S 2,635 vs
V 8,382". No file under vir's `l4/`, no Lean L4 file and the Lean L4 declarations were NOT opened. What this subject can have
informed: F6's choice of a step-indexed safety predicate (a standard CSL form, Vafeiadis 2011, but the arm had not written
it down before the read), and Q4's direction on the Lean column. Scoring label is vir's (V-F5 precedent).

## F0. Where L4 lives, and the no-edit rule (Q1)
- Files: `theories/vir/virl4_*.ml` (+ `.prla`) on `mojave/vir-l4`. Planned, in chain order: `virl4_sig` (Σ₄) · `virl4_step`
  (⟶₄, faults, reach) · `virl4_typing` (⊢₄) · `virl4_assert` (lock assertions) · `virl4_triple` (safety, the triple,
  adequacy) · `virl4_rules` (parallel rule, the three lock rules, the frame and structural rules) · `virl4_cons` (CE) ·
  `virl4_prog` (N1–N4, F₄, Q8's program) · `virl4_inv` (N1-V, N4-V on ⟶₄) · `virl4_sem` (semantic typing, Q6). Every L4
  module is `virl4_*`; a module may be split.
- **No `virl1_*`, `virl2_*` or `virl3_*` file is edited** (Q1, widened at the pin to all three).
- Y1/Q2: everything DEFINED (`define` + `interactive`); 0 `prim` in any `virl4_*`. No framework file is added for L4; if one
  is needed it is declared here first, as an amendment, and counted beside.

## F1. Σ₄: the syntax (inputs §2)
- `lock` is a new TYPE `ty_lock`, NON-linear: a lock variable is an ordinary Γ variable (L1's typed placeholder
  `a_tvar{ty_lock}`), so it may occur in both sides of a `par`. `cap` stays linear.
- `newlock`, `acquire`, `release` are three new EFFECT operations through L2's binder `e_eff{τ; o; args; x. e}` (D0): no new
  expression former for them. `newlock(c)` : lock, consumes c · `acquire(ℓ)` : cap, a fresh name · `release(ℓ, c)` : unit,
  consumes c. The runtime lock value is `lockv{l}` (one child, an L1 numeral), outside the source language, like `capv`.
- **`par` is a new expression former, and it BINDS.** L2 has no product type (the W3 products are off-base, D7), and
  `ret c` requires Δ = [c], so "the result is the pair of results" cannot be a value. The arm reads inputs §2's
  `let p ← par e₁ e₂ in e` as **`par{e₁; e₂; x₁, x₂. e}`**: both sides run interleaved; when both are `ret a₁`, `ret a₂`, the
  node steps to `e[a₁/x₁, a₂/x₂]`. A side's capability result binds a fresh NAME in e's Δ, as `alloc`'s does, so the
  capabilities "come back joined" through the binders and no tuple of capabilities exists as a value. ⛔ *Corrected by F11 (L4-E1): this said "G2(b) does not fire"; L4-E1 records
that the binding form fires G2(b)'s trigger in its NARROWEST form (two single-capability binders, never a tuple type).*
  N1's single `p` is read as two unit binders, both unused. ⚠️ **N4 is written in the inputs as a bare `par` with no
  continuation; see F7.**
- The invariant `inv(v₀ … vₖ₋₁)` is NOT in the term (inputs §2): it is a parameter of the logic (F5).

## F2. ⟶₄ (H3(a)): a successor FUNCTION, nondeterminism as its list
- A configuration is `(e, σ, L)`: σ is L2's store (D1, unchanged), L : list{int × lockstate} the lock table, lockstate =
  `free{p}` (guards the region at base p) | `held{p}`. L2's store type, ∗ and region are reused as they are.
- `l4succ{c} : list{config}` is ONE `fix`, one equation per form: every successor of c, one per enabled redex. The redexes
  of `par{e₁; e₂; …}` are those of e₁ and of e₂ (each side is an evaluation context), plus the join when both are `ret`.
  Every L2 form steps as `l2step` does, with L unchanged. `newlock(capv{p})` on a live region adds `l = free{p}` with l the
  least unused id; `acquire(lockv{l})` on `free{p}` steps to `held{p}` returning `capv{p}`, and on `held{_}` has NO successor
  (it BLOCKS); `release(lockv{l}, capv{p})` on `held{p}` steps to `free{p}`, otherwise FAULTS.
- `step4{c; c′} := mem{c′; l4succ{c}}`; `reach4` from `l4iter` as D2's `reach`. No fuel in any statement about the logic.
- **Fault vs block vs terminal.** Terminal: `ret a`, a a value. `fault4{c}` is a TERM RECURSION (D10's lesson, at birth):
  some redex position (through `let` and both sides of every `par`) is stuck for a reason other than an `acquire` on a held
  lock. A DEADLOCK is non-terminal, no successor, not `fault4` (F8, Q8). The index fault `ifault4` is `ifault2` (D10)
  carried through `par`'s two sides.
- `race4{c}`: two redexes in DIFFERENT sides of one `par` whose next actions are `load`/`store` at the same address (two loads
  included, as Q6 is written).

## F3. ⊢₄ (⊢₂ plus four rules)
- `tc4{n; Δ; e}` is a NEW total checker, one `fix`: every L2 form exactly as `tc2r`/`tc2` (no `virl2_*` edit, so its clauses
  are re-stated, and a lemma `tc4 = tc2` on L4-free terms is CE's typing half, F9). New clauses:
  `newlock(c)`: c ∈ Δ, result `ty_lock`, c removed · `acquire(ℓ)`: ℓ an atom of type lock, result cap, a fresh name added ·
  `release(ℓ, c)`: ℓ : lock, c ∈ Δ, result unit, c removed · `par{e₁; e₂; x₁, x₂. e}`: Δ₁ = names occurring in e₁, Δ₂ =
  names occurring in e₂, **inr if any name occurs in both** (N2), the rest to e, which is checked with Δ_rest plus a fresh
  name per cap-typed binder; each side at its own Δ as a closed-over-Δ term (`ret c` ⇔ Δᵢ = [c]).
- ⊢₄ reads no invariant (N3 is TYPED).

## F4. Where the carvings stand (D8, D9, D8a, D10 carried up)
- Any L4 theorem that, like Y5, reads a term's names against Δ or the store (semantic typing, Q6) is stated over `wfs4{2; e}`
  (wfs2 over Σ₄'s operators: `lockv` with an `isNum2` child, `ty_lock` read by the type sort) and `scoped4{n; Δ; e}` (D9 over
  Σ₄, binders of `par` included). They are COUNTED on a "grammar carving" line, as at L2.
- **Dependency, declared now:** L2's Y5 is HELD at its D10 fourth-gap stop with the 11-08 cap. L4's semantic typing and Q6
  are the rows that would reuse Y5's invariant; they are ordered LAST in L4 and are stated NOT to cite `virl2_sem*` unless Y5
  is CLOSED at a posted sha. If it is not, the arm states them and attempts them on their own; a row unreached is reported
  UNREACHED, never re-scoped.
- Rows that read no names against Δ (the rules, CE, N1–N4's T/S/V, Q8) take no carving.

## F5. Assertions and lock invariants (H2(a))
- An invariant is a predicate on a region's CONTENTS: `Inv = list{int} → U` (the k cells in order). A lock-invariant
  environment `J : list{int × (int × int × Inv)}` maps a lock id to (base, length, invariant). L2's `Assn` is reused for
  owned state; `islock(ℓ, p, k, I)` is a persistent assertion on J (J(ℓ) = (p, k, I)), duplicable, separating nothing.
- `RegionAt(p, k, f)` and `⌜·⌝` are L2's / L3's.

## F6. The triple: DEFINED from ⟶₄ (H3(a), Q3, no rule an axiom)
- **Thread-local safety**, step-indexed: `safe4{k; e; σ; J; Q}` by `fix` on k. At k+1: e is not `fault4` against its owned σ
  (an access outside σ is a fault, so race freedom is built in); if e is terminal, Q holds; every step of e alone, in any
  composition `σ ⊎ σ_F` with any frame, preserves the frame and lands in `safe4{k; …}`; an `acquire` adds the lock's region
  with contents satisfying J's invariant to σ; a `release` REMOVES the region and REQUIRES its contents to satisfy the
  invariant (so N3 has no triple); a `newlock` extends J. `{P} e {v. Q}₄ := ∀k σ. P σ ⇒ safe4{k; e; σ; J; Q}` for every J
  extending the ones P names. (Method: CSL soundness in Vafeiadis's operational form; ideas only, no code; see the INFORMED note.)
- **Adequacy (the "every interleaving" form):** for a closed e with `{P} e {v. Q}₄`, from any `(e, σ ⊎ σ_inv, L)` with P σ
  and σ_inv the free locks' regions satisfying their invariants, every `reach4` configuration is not `fault4` and every
  reachable terminal's store satisfies Q ∗ the invariants of the free locks. This is L2's D6 triple quantified over ⟶₄.
- The bounds-tolerant `{·}ᵢ₄` is the same with `ifault4` permitted (L2-E1/E2 carried up).
- Theorems, from ⟶₄: the parallel rule `triple_par` (Q3: no side condition naming a region), `triple_newlock`,
  `triple_acquire`, `triple_release`, the frame rule for every program, consequence, let, if.
- **Q5's population** is these six (par, newlock, acquire, release, frame, let) against L2's rules in vir's count at L2;
  wf premises per rule, as count.py reads them.

## F7. The programs, in the arm's terms
- **F₄** (free w : cap, ℓb : lock; `define`d, binding depth 2), generated from F's text as E2 does, with the bucket in its
  own 4-cell region b (bucket s at index s, so `add(K, sender)` becomes `sender`) and ONE critical section from the bucket
  load to the last bucket access on each path:
  ```
  let n:int ← load(w, 0) in
  if le(24, n) then
    RD32(0, magic) RD32(4, sender) RD32(8, topic)
    let a:int ← load(w, add(A, add(mul(sender, NT), topic))) in
    let b:cap ← acquire(ℓb) in
    let t:int ← load(b, sender) in
    if and(eq(magic, 1297303345), and(eq(a, 1), lt(0, t))) then
      let b1:cap ← store(b, sender, sub(t, 1)) in let u:unit ← release(ℓb, b1) in EMIT
    else let u:unit ← release(ℓb, b) in EXIT(2)
  else EXIT(1)
  ```
  **Why one section:** with two brackets the check `lt(0, t)` and the decrement are separately atomic, the bucket can go
  negative, and N4-S fails at the second release. Two brackets is the other reading of "its two bucket accesses bracketed";
  the arm takes the one under which N4-S is true and says so. w is 83 cells (0 … 82: header, wire, ACL at A = 67 … 82).
- ⛔ *SUPERSEDED by F11 (L4-E2 (4)): the continuation is fixed by the erratum; the paragraph below is kept as the record.*
  **N4's continuation (the open point).** The inputs write N4 as `par (F₄[w₁]) (F₄[w₂])`; under F1 a `par` binds, and two
  capability results cannot be returned (Δ = [c] at `ret`). **The arm states N4-T, N4-S and N4-V at the par NODE:** N4-T is
  ⊢₄ of each side plus par's split ({w₁} ⊎ {w₂}, ℓb in Γ); N4-S is the two side triples plus `triple_par`, for ANY
  continuation e whose triple from `Q₁ ∗ Q₂` holds; N4-V is a configuration invariant over every configuration reachable from
  `(par{F₄[w₁]; F₄[w₂]; x₁, x₂. e}, σ, L)` for any e that contains no `acquire(ℓb)`. An erratum naming a continuation is vir's;
  this reading is what the arm builds unless one arrives first.
- **N1-V / N4-V (H5(a))** read thread progress from the TERM (no ghost cells): N1: `cell + #sides not past their store = 2`
  on every reachable configuration, so a terminal returns 2. N4: for each s, `b(s) + #sides past their decrement with
  sender s = tokens₀(s)` (b(s) read from the store when ℓb is free, and from the holder's owned region when held), and
  emits by s ≤ that count; with b(s) ≥ 0 this is run_tokens₄.
- N2 is the refutation `tc4{…} = inr{it}`; N3 the refutation of `{emp} N3 {_. True}₄` at its release.

## F8. Q8 (deadlock)
- `let c ← alloc(1) in let ℓ ← newlock(c) in let d ← acquire(ℓ) in let d′ ← acquire(ℓ) in …` blocks at the second
  acquire with no successor and no `fault4`; `{emp} e {_. False}₄` holds. A one-thread program is enough; a two-thread one is
  not owed.

## F9. CE (on ⟶, both directions)
- For e with no `par`, `newlock`, `acquire`, `release` or `lockv`: `l4succ{(e, σ, L)} = [(e′, σ′, L)]` iff
  `l2step{(e, σ)} = inl{(e′, σ′)}`, and `= nil` iff `inr`; `fault4` agrees with L2's fault; `tc4 = tc2` on such e.

## F10. Scoring notes
- C5 per row by per-module FRESH replay (`status_all`, fresh session), as at L2/L3. The 11-06 rule binds: past ~100 tactic
  applications in one proof the arm stops and systematizes, and tactic-building time is its own ledger line beside C5.
- Reported beside, never hidden: the carving line (F4), the INFORMED note above, and any amendment to this file, each with
  the file's hash before and after, as D8–D10 were.

## F11. Amendment: the L4 errata read (2026-11-08 06:40 PST, vir @99,075,268; file hash before bca726412efe43ff at ccfe03d24)
- **Read, by exact path at vir origin/master ee6f4f6** (errata last changed 60ff2bf, 2026-11-06): `errata/ERRATA-L4.md` (L4-E1,
  L4-E2, L4-E3) and `errata/L4-E2-N4.md`. Object text; no Lean L4 file in them (L4-E1 cites the Lean L3 `F_typed`, public).
- **L4-E1 = F1's par**, as `let x₁:τ₁, x₂:τ₂ ⇐ par e₁ e₂ in e` (the arm's `par{e₁; e₂; x₁, x₂. e}`). The parallel rule's post is
  `Q₁ x₁ ∗ Q₂ x₂`. F1's "G2(b) does not fire" is corrected in place: it fires in the narrowest form.
- **The terms, taken as written:** N1 per L4-E2 (1)(2) (`let _:unit, _:unit ⇐ par (INC ℓ) (INC ℓ) in …`; its last line releases
  `c2` before `ret x`; INC ends `let u:unit ← release(ℓ, d1) in ret u`) · N2 per L4-E3 (SIDE c1 on both sides; ILL-TYPED) · N3 per
  L4-E2 (3) · N4 per L4-E2 (4) and `L4-E2-N4.md`: `let w₁′:cap, w₂′:cap ⇐ par (F₄[w₁]) (F₄[w₂]) in let u₁:unit ← free(w₁′) in let
  u₂:unit ← free(w₂′) in ret ()`, free ℓb, w₁, w₂. F7's F₄ text agrees with the erratum's line for line (one critical section,
  bucket at `sender` in b; the erratum names the release binder `r`, F7 `u`: a binder name, no change). N4-T is ⊢₄ of THAT term;
  N4-S the two side triples (each on L3's `layout` with sender < NS); N4-V over configurations from that term. An
  any-continuation lemma may exist as a helper; the rows are scored at the erratum's terms.
- **Q5's population, fixed by vir before any virl4 rule (@99,075,268):** PRIMARY: the six L4 rules of F6 (triple_par,
  triple_newlock, triple_acquire, triple_release, the L4 frame, the L4 let; final names posted when proved) against L2's
  triple_let, triple_frame, triple_load, triple_store, triple_free, triple_alloc. BESIDE: L2's 11 program rules plus frame,
  virl2_rules whole, every rule of each layer. `[wf]` labels in the statement, comments stripped, rewrites never counted.
- **Blindness, from vir's word:** no `git log` in any vir checkout or the public repo without a thought-out path limit; nothing
  under `l4/`; no RESULTS-10, until L4 is scored. Errata and object files by exact path.
