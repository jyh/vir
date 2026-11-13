# L5, the Lean arm's declarations (amend-24, "owed by each arm before its first L5 file")

Written 2026-11-13 by the 71st vir head, on branch l5-lean (cut from l5-pin 86402f8: the OBJECT-L5 pin a35589c, amend-24 17ef02f,
erratum L5-E1 86402f8), ONE commit after them and BEFORE any `.lean` file under `l5/`. **SEALED:** the bus carries only this file's
commit sha and sha256 until the MetaPRL arm has posted its own L5 declarations (FINDINGS V-F5's rule, as at L3 and L4). Both are
quoted into the L5 scoreboard.

## The L4-closed sha, and what L5's proofs may cite
- **Lean L4-closed sha: vir 4017931** (RESULTS-10; `git log 4017931..caf23c0 -- l4/VIRL4` reads 0 commits). L5's proofs cite only
  definitions and theorems of `VIRL1`, `VIRL2` and `VIRL3` present at caf23c0, and, for LV8 alone, the DEFLATE and compiler theorems
  amend-24 names (`safety`, `deflate_driver`, `router_refines`) at caf23c0.
- **L5 extends L2, not L4** (OBJECT-L5 J1 (a): *"one conservative-extension theorem over L2"*; L3 adds no language). `par` and the
  locks are not in L5; a library routine called under `par` is not an L5 row.
- **L1–L4 are IMPORTED, never edited (LV1).** LV1 reads `count.py --arm w8` over each of `l1/VIRL1`, `l2/VIRL2`, `l3/VIRL3`,
  `l4/VIRL4` with BASE = 4017931 and EXT = this arm's L5-closed sha.

## The representation, and the choice it forces (declared before any proof, so it is scored, not discovered)
- **L1′ is a NEW type and judgement with an embedding of ⊢₂, never an edit of L2 (LV1's "new, not in place").** L1's `Ty B` and
  `Tm S` are closed inductives; the annotated arrow `τ₁ →[k] τ₂` (erratum L5-E1) is a type former and `ret a [d₁ … d_k]` and the
  lending call are term formers, so none of them fits L1's extension point (`ESig` adds base types and ops only).
  ⇒ **Declared: fresh mutual syntax `Ty₅`, `Atom₅`/`Tm₅` in `l5/`**: L1's formers over S₂ with `arr` carrying `k : Nat`, plus
  `retK (a) (ds : List Nat)` and `callK (τ₂) (a₁ a₂) (cs : List Nat) (e)` (`let x:τ₂, c₁′ … c_k′ ⇐ a₁ a₂ [c₁ … c_k] in e`; x = #k, cᵢ′
  = #(k−i)), with structural embeddings `ιT : Ty₂ → Ty₅` (k = 0 on every arrow) and `ι : Tm₂ → Tm₅`. Substitution, well-scopedness
  and the runtime typing are re-stated for `Tm₅`. **This duplication is the Lean price of a type former, and it is COUNTED in C5 on
  its own reported line `L5.syntaxCopy`**, as `L4.syntaxCopy` was.
- **Δ keeps L2's form**, a mask `List Bool` over Γ (`HasType₂ Γ Δ e τ`); a lent capability is a position. The arrow carries a COUNT
  k, never names or sizes: which region a capability is, and its size, are facts of the logic (L5-E1 (5)).
- **Rejected, and why:** encoding a lending call as k nested L2 `store`-shaped ops. It would type, but it is not a function: the
  callee could not be a λ/fix value passed as an atom, and J1 (a) asks for capabilities in FUNCTION TYPES.

## ⊢₅, the meaning, and the triple
- **⊢₅ = ⊢₂'s rules over `Tm₅` plus three:** `lam`/`fix` at `τ₁ →[k] τ₂` check the body with k fresh `cap` variables in Γ and Δ = exactly
  those (the self variable of `fix` is cap-free); `retK a ds` needs Δ = {ds} exactly and a : τ with `hasCap τ = false`; `callK` needs
  the cᵢ DISTINCT members of Δ, removes them, binds the cᵢ′, and checks e with the rest of Δ plus the cᵢ′. Everything else, including
  `ret`'s Δ = ∅, is L2's.
- **⟶₅ is L2's substitution step over `Tm₅`, plus:** a call steps by substituting the argument and the k capability VALUES ⟨pᵢ⟩ into
  the body, under a return frame; `retK v [⟨q₁⟩ … ⟨q_k⟩]` in that frame steps to e with x := v, cᵢ′ := ⟨qᵢ⟩. No fuel, no step index:
  `fix` is L1's unfolding, as at L2.
- **Semantic typing is proved as L2's Y5 was, SYNTACTICALLY:** a runtime typing `RT₅` (L2's `RT` with return frames) preserved along
  ⟶₅*, plus progress, giving `TripleIF` with index faults only (errata L2-E1/E2 carried up). LV4's "fix case" is read on this proof:
  the per-constructor cases of preservation and progress, C5 per case.
- **The triple is L2's semantic `Triple`/`TripleIF` from ⟶₅**, so a routine's spec is a triple on a `callK`, with each lent region
  as `RegionAt p n f` before and `RegionAt p n f′` after (same p, same n: L5-E1 (5)).
- **CE (LV3):** `ι` commutes with ⟶ in both directions (`Step₂ c c' ↔ Step₅ (ι c) (ι c')`) and `HasType₂ Γ Δ e τ → HasType₅ (ιT Γ) Δ
  (ι e) (ιT τ)`, with `Faults` preserved both ways.

## The routines (J3 (a)), their names and their triples, before their proofs
Each is a closed `fix` value of an annotated arrow; all regions hold `Int` (J2 (a)); bounds are premises in the LOGIC.
- `copyR : (int × int × int) →[2] unit`, (s, d, len): pre `RegionAt ps ns f ∗ RegionAt pd nd g`, `0 ≤ s`, `0 ≤ d`, `s + len ≤ ns`,
  `d + len ≤ nd`, `0 ≤ len`; post the same regions with `g′ i = f (s + (i − d))` for d ≤ i < d + len, `g′ i = g i` otherwise, f unchanged.
  (DEFLATE's back-reference copy is the SAME-REGION case: a separate `copyWithinR : (int × int × int) →[1] unit`, forward byte order,
  overlap allowed, as RFC 1951 requires; whether it collapses into copyR is LV10's to measure, not this file's to decide.)
- `fillR : (int × int × int) →[1] unit`, (d, len, v): `g′ i = v` on [d, d + len), g elsewhere.
- `cmpR : (int × int × int) →[2] bool`, (a, b, len): result = `∀ i < len, f (a+i) = g (b+i)`, both regions unchanged.
- `scanR : (int × int × int) →[1] int`, (from, to, v): the least i ∈ [from, to) with `f i = v`, else `to`; region unchanged.
- `bitR : (int × int) →[1] (int × int)`, (pos_bit, k): Appendix S's `bits(k)` at pos_bit over a byte region: (value, pos_bit + k), the
  region unchanged; pre `pos_bit + k ≤ 8·n`, `0 ≤ k ≤ 16`. **No premise on the contents (LV7)**: a cell outside [0, 256) is read by
  the same arithmetic as at L2 (DEFLATE's `bitAt` over Int) and the post says what it returns.
- **Acceptance (LV8, LV9):** `l5/` re-expresses DEFLATE's step program and the L3 router over these, and proves `safety`'s statement,
  `deflate_driver`'s L2 statement and the router's L3 theorem for the re-expressed terms by citing only the routines' triples.

## Where L5 lives
A SEPARATE lake project `l5/` (lib `VIRL5`), requiring `l3` by PATH (which requires `l2`, then `l1`), and `deflate` by PATH for LV8,
mathlib at salt's pin (packages APFS-cloned from `l4/`, manifest written by edit, never a bare lake update). Every build goes
through `l5/logged-build.sh` (saltbuild, one log per run, `l5/logs/`, the replay filter of k5/LOGS-FILTER.md from the first build),
judged by its `saltbuild EXIT=` line alone. The tactic rule of 11-06 binds: past ~100 tactic applications in one proof, stop and
systematize; tactic-building time is a separate ledger line.

## Planned files (a renamed file is declared again before it is scored)
`VIRL5/Syntax.lean` (Ty₅, Atom₅, Tm₅, ιT, ι, subst) · `VIRL5/Typing5.lean` (⊢₅) · `VIRL5/Step5.lean` (⟶₅, Faults₅) · `VIRL5/CE.lean`
(LV3) · `VIRL5/Runtime5.lean`, `Preservation5.lean`, `Progress5.lean`, `Y5L5.lean` (semantic typing; LV4 per case) ·
`VIRL5/Routines.lean` (the six terms and their typings) · `VIRL5/Specs.lean` (their triples; LV7) · `VIRL5/Deflate5.lean`,
`VIRL5/Router5.lean` (LV8, LV9) · `Audit.lean` (`#print axioms` over every theorem; LV2).

## ADDENDUM 1 (2026-11-13, the same head, BEFORE any `.lean` file under `l5/`): three representation facts the text above left loose
Writing `Syntax.lean` against L1's substitution showed three places where the text above cannot be implemented as written. Each is a
representation choice inside L5-E1, not a change of it; nothing in amend-24 moves.
1. **The capability lists are ATOMS, not indices.** `ds`/`cs` are `List Atom₅`: `.var n` at typing time, `⟨p⟩` (`.const (.cap p)`)
   after substitution, exactly as L2's op operands are (`load(.var n, a)`). Index lists could not be substituted.
2. **The judgement carries the count:** `HasType₅ Γ Δ e τ k` reads "e returns a τ and hands back k capabilities". `ret` and L2's
   `retCap` are k = 0; `retK a ds` is k = |ds| with Δ = exactly the ds (distinct); `letE`'s bound term is k = 0; `ite`/`case` give
   both branches the same (τ, k).
3. **The lending call is TWO formers, not one:** `appK a₁ a₂ cs` (a TAIL call that lends cs = exactly its Δ and returns the callee's
   (τ₂, k)) and `letK τ j e₁ e₂` (`let x:τ, c₁′ … c_j′ ⇐ e₁ in e₂`; e₁ at (τ, j) with Δ₁, e₂ with Δ₂ plus the j new capabilities; x =
   #j, cᵢ′ = #(j−i)). The `callK τ a₁ a₂ cs e` named above is the derived form `letK τ |cs| (appK a₁ a₂ cs) e`. ⟶₅ then needs NO
   return frame: `letK τ j (retK v qs) e₂` steps to e₂ with x := v and the cᵢ′ := qᵢ, and `letK` steps under its first term as `letE`
   does. L2's `app` stays a former (k = 0, Δ = ∅), so ι is the identity on every L2 former.

## ADDENDUM 2 (2026-11-13, the same head, after Step5/Preservation5 built and BEFORE Progress5 exists): ⟶₅ was missing one rule
Porting L2's progress showed a typable configuration with no step: `letK τ 0 (ret a) e₂`. Its head is typed at (τ, 0) by `ret` (k = 0),
which `letK` accepts at j = 0, but `letKRet` fires only on a `retK`. So ⟶₅ gains **`letKRet0`: `letK τ 0 (ret a) e₂` steps to
e₂ with x := ⟨a⟩**, the j = 0 reading of `letKRet` (no capability comes back). It is a gap in the Lean arm's step relation, not in the
object or L5-E1, and it is recorded here before the progress theorem that found it is written. Files changed: Step5 (the rule), CE (its
impossibility on ι's image, like the other three), Preservation5 (its case, `letKRet` with no constants). No amend-24 row moves.

## ADDENDUM 3 (2026-11-13, the same head, BEFORE Progress5 is committed; its first build l5-023 found it): the mirror-image gap
`letE τ (retK a []) e₂` is typable too: a `retK` with the empty list is at (τ, 0), which `letE`'s head accepts, but `letRet` fires
only on `ret`. So ⟶₅ gains **`letRetK0`: `letE τ (retK a []) e₂` steps to e₂ with x := ⟨a⟩** (`retK a []` is `ret a`). The same
files change as for Addendum 2. Two gaps of one class in one hour: the step relation was written from the term formers, not from
the typing rules' (τ, k) pairs, and progress is the theorem that reads it the second way.
