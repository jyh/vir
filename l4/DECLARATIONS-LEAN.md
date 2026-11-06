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
