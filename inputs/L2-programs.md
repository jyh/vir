# L2 acceptance programs M1–M5 (OBJECT-L2 §8)

Drafted 2026-11-02 by vir (12th head); PINNED 2026-11-03 by the 15th with `object-L2/OBJECT-L2.md`, in the same commit,
BEFORE either arm's first L2 file; both arms receive the same bytes. F8 is ruled bounds-by-logic (council 11-03 ask 1), so the
M3 note below stands as written. Concrete syntax is OBJECT-L1 §2's, with every O₂ operation written as L1's effect binder
`let x:τ ← o(a⃗) in e`. σ₀ = (∅, ∅), the empty store. Each arm proves, per row: the typing (or its refutation), the
denotation from the stated store, a ⟶₂* trace to it (or to the stuck configuration), and the triple named.

| id | what it exercises | program | type | meaning | triple |
|---|---|---|---|---|---|
| M1 | alloc · store · load · free, value round-trip | `let c:cap ← alloc(4) in let c1:cap ← store(c,2,7) in let v:int ← load(c1,2) in let u:unit ← free(c1) in ret v` | int | ⟦M1⟧₂ σ₀ = (7, σ₀) | `{emp} M1 {v. ⌜v = 7⌝}` |
| M2 | two regions; a write to one leaves the other (the FRAME RULE's instance) | `let a:cap ← alloc(2) in let b:cap ← alloc(2) in let a1:cap ← store(a,0,5) in let b1:cap ← store(b,0,9) in let x:int ← load(a1,0) in let u1:unit ← free(a1) in let u2:unit ← free(b1) in ret x` | int | ⟦M2⟧₂ σ₀ = (5, σ₀) | `{emp} M2 {v. ⌜v = 5⌝}`, whose `store(b,0,9)` step is DERIVED by the frame rule from the small axiom with `R = a ↦ 5 ∗ a+1 ↦ 0` |
| M3 | an out-of-bounds load: WELL-TYPED, and it FAULTS | `let c:cap ← alloc(2) in let v:int ← load(c,2) in let u:unit ← free(c) in ret v` | int | ⟦M3⟧₂ σ₀ = ⊥ (§6: a fault is ⊥) | NONE: `¬ {emp} M3 {v. True}` |
| M4 | a leak: missing `free` | `let c:cap ← alloc(1) in ret 0` | ILL-TYPED | ⟦M4⟧₂ σ₀ = (0, σ₁) with σ₁'s R ≠ ∅ | `{emp} M4 {v. ⌜v = 0⌝ ∗ region(_,1)}` holds; `{emp} M4 {v. ⌜v = 0⌝}` does NOT |
| M5 | an L1 program read in L2 (OBJECT-L2 §7): K5 verbatim | K5 of `inputs/L1-programs.md`, byte-identical | int (Γ ; ∅ ⊢₂) | for EVERY σ: ⟦K5⟧₂ σ = (55, σ) | `{P} K5 {v. ⌜v = 55⌝ ∗ P}` for every P |

Notes, fixed here so that neither arm decides them:
- `alloc` picks the least fresh base above every live region (OBJECT-L2 §3). From σ₀ in M2, a ↦ base 0 and b ↦ base 2. No
  row's meaning depends on the base: the arms state meanings up to the final store, which is σ₀ wherever every region is freed.
- M3 faults at `load(c,2)`: the region has length 2, so index 2 is out of bounds. Its typing goes through, because
  linearity does not check bounds (OBJECT-L2 §5, the F8 fork; bounds-by-logic). M3 is the row that shows what the type
  system does NOT give. If F8 is ruled the other way (an indexed `cap(n)`), M3 becomes ILL-TYPED and this note changes at the pin.
- M4 does not fault. It is rejected ONLY by ⊢₂ (`ret 0` with Δ = {c}), and its meaning is defined. The triple pair shows
  the leak is visible to the logic as a region left in the postcondition.
- M5 is the conservative-extension row: the same bytes as K5, so the L1 → L2 theorem (§7) is exercised on a program that
  uses fix, currying and a tail call. Its store is untouched for EVERY σ, which is the frame clause in its strongest form.
- Binders `u`, `u1`, `u2` of type unit are ordinary names: L1's grammar has no `_`.
