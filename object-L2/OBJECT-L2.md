# OBJECT-L2 — layer L2, the imperative core, the object both arms mechanise (F1(b) F2 F3(ii) F4(a) F5 F6 F7)

**Drafted 2026-11-02 ~19:0x PST by the 12th vir head; PINNED 2026-11-03 by the 15th, BEFORE either arm's first L2 file**, on the
Captain's ruling at the 11-03 council (ask 1, his words: *"Ok, good, and yes we simply proceed with (ii)"*, as the
sitting's minute records them). F3 is ruled (ii) and F8 is ruled bounds-by-LOGIC. L1′ (sizes carried by types, the
dependent reading) is NOT commissioned; its one reopening trigger is L4 wanting capabilities in function types. The pin
precondition held: the MetaPRL arm posted "L1 closed" (2026-11-03 06:11, at be5312958; replayed 672/672 at 06:49).
The text below is the 11-02 draft byte for byte except this status paragraph, the title line, and two phrases in §5 and §6
(the draft's own name for itself, now "This object takes"). **Nothing in this file is edited after its pin.** An erratum goes
in `errata/ERRATA-L2.md`. Both arms receive these bytes and nothing else from each other.

## 0. The rule L2 lives under (OBJECT-L1 §8)
L2 = L1 at a larger signature Σ₂ ⊇ Σ₁, plus NEW relations beside L1's: `⊢₂` (typing with a linear context), `⟶₂` (steps over a
configuration ⟨e, σ⟩), `⟦·⟧₂` (meaning with a store), and a program logic. **No L1 definition is edited.** In particular
L1's grammar is reused unchanged: every L2 operation is an instance of L1's effect binder `let x:τ ← o(a⃗) in e`.

## 1. Σ₂
- **B₂ = {int, bool, unit, cap}.** `cap` is the one LINEAR base type. A value of type `cap` is a region capability.
- **Constants:** L1's, plus `()` : unit, plus the runtime-only capabilities `⟨p⟩` : cap for p ∈ ℤ (the region's base
  address). A source program contains no `⟨p⟩`.
- **P₂ = P₁.** No pure operator takes or returns `cap` (an address is never computed by arithmetic).
- **O₂**, the region operations (F2):

  | o | arity | effect |
  |---|---|---|
  | `alloc` | (int) → cap | n > 0 fresh contiguous cells at a fresh base p, each 0; returns ⟨p⟩ |
  | `load` | (cap, int) → int | reads cell p + i, 0 ≤ i < n. **Does NOT consume the cap** (F4(a)) |
  | `store` | (cap, int, int) → cap | writes cell p + i. **Consumes the cap and returns it** (rebinding) |
  | `free` | (cap) → unit | releases the region. **Consumes the cap** (this is `drop`) |

## 2. Stores and faults
A store is σ = (H, R): H : ℤ ⇀ ℤ the cells, R : ℤ ⇀ ℕ the live regions (base ↦ length), with dom H = ⋃ {[p, p+n) | R(p) = n}.
Regions are pairwise disjoint. A `load`/`store` outside [p, p+R(p)), or on a p ∉ dom R, has NO step: it is a FAULT (stuck).

## 3. ⟶₂ on ⟨e, σ⟩ (defined, never primitive; L1-E2 applies)
L1's six rules lifted with σ unchanged, plus one rule per O₂ operation (`let x:τ ← o(a⃗) in e ⟶₂ e[v/x]` with the store updated
as §1's table says). `alloc` picks the least fresh base above every live region (a deterministic choice, so DETERMINISM survives).

## 4. ⊢₂, the static semantics with a linear context (F3(ii))
Judgements `Γ ; Δ ⊢₂ e : τ`. Γ is L1's ordinary context. Δ is a LINEAR context of `cap` variables: each is used EXACTLY once.
- Atoms never mention a Δ variable, except as an operand of an O₂ operation.
- `let x:cap ← alloc(a) in e`: e is checked with Δ, x. `load(c, a)` requires c ∈ Δ and leaves Δ unchanged (non-consuming).
  `let c′:cap ← store(c, a₁, a₂) in e` removes c and adds c′. `let _:unit ← free(c) in e` removes c.
- `let x:τ = e₁ in e₂` SPLITS Δ between e₁ and e₂. `if` gives both branches the same Δ. `ret a` with τ ≠ cap requires Δ = ∅
  (linear, not affine: no leak). `ret c` with Δ = {c} returns the capability.
- **No capability crosses a function boundary in L2** (declared): `cap` does not occur in a λ or fix parameter or result type,
  and a λ/fix body is checked with Δ = ∅. L3's router threads its token sequentially and does not need more. Lifting this is
  L4's business (locks), not L2's.
- L1's typing embeds: `Γ ⊢₁ e : τ` implies `Γ ; ∅ ⊢₂ e : τ` (OBJECT-L1 §8 clause 1).

## 5. The program logic (F5) and its soundness (F6)
Assertions over H: `emp`, `p ↦ v`, `P ∗ Q`, pure facts, ∃. `region(p, n)` = ∗_{0≤i<n} (p+i ↦ _) together with R(p) = n.
- Triples `{P} e {v. Q}` (partial correctness + NO FAULT): from any σ ⊨ P ∗ R_frame, e never faults, and if it reaches
  `ret a` then σ′ ⊨ Q[⟨a⟩/v] ∗ R_frame.
- **THE FRAME RULE, for EVERY L2 program e:** `{P} e {v. Q}` implies `{P ∗ R} e {v. Q ∗ R}` for every R. NO side condition
  names a region e does not touch. It is proved from ⟶₂ (locality of the four operations + L1's steps leaving σ alone).
- Small axioms for the four operations, and the structural rules (consequence, let, if, app via the callee's triple).
- **SEMANTIC TYPING (the meaning of linearity, council §C):** a capability variable c bound to ⟨p⟩ denotes `region(p, n)`.
  If `Γ ; Δ ⊢₂ e : τ` then `{∗_{c∈Δ} region(c)} e {v. ⌜v ∈ ⟦τ⟧⌝ ∗ (region(v) if τ = cap)}`. **So a well-typed program does not
  fault EXCEPT OUT OF BOUNDS, and does not leak** (no use after free, no use of an unallocated base, no lost region), and
  its frame is untouched by the frame rule. This retires the hdisj form. **A bounds fault is excluded only by a TRIPLE**
  (the index facts are logic, not types), and that is what M3 exhibits.
  *(This bullet first read "a well-typed program does not fault", which M3 below refutes. Corrected in the draft.)*
- **F8, the fork this exposes:** bounds by TYPING would need `cap` to carry its length (`cap(n)`): an INDEXED type, which is
  F3's option (iii) again (it edits L1's `Ty` in Lean). This object takes bounds-by-logic.

## 6. The meaning (F7)
`⟦e⟧₂ : Store → (Val × Store)⊥` as ONE least fixed point Φ₂ (OBJECT-L1 §6's form with a store), with its unfolding,
soundness and adequacy against ⟶₂, and FAULT denoting ⊥ ... **or** a distinguished `fault` result. This object takes `fault` ∉
Val: a fault is ⊥, and NO-FAULT is the logic's statement (§5), not the denotation's.

## 7. The L1 → L2 conservative-extension theorem (OBJECT-L1 §8), proved here
Clauses 1–3 for every closed L1 program at a base type, with no L1 definition edited (W8, scored from the diffs of l1/VIRL1).

## 8. Acceptance programs (inputs/L2-programs.md, written with the pin)
M1 alloc, store, load, free (value round-trip) · M2 two regions, a write to one leaves the other (the frame rule's instance) ·
M3 an out-of-bounds load: WELL-TYPED and it FAULTS (linearity does not check bounds; no triple holds for it), which shows
exactly what the type system does NOT give · M4 a leak (missing `free`: ILL-TYPED) · M5 an L1 program
(K5) read in L2: same value, store untouched (§7).
