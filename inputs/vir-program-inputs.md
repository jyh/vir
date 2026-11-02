# VIR program inputs: the SEMANTIC reading of linearity (O95, council 2026-11-02 §C point 4; STATUS-vir row 80). The same bytes for both arms

The council ruled that "linear types denote resource predicates over owned store fragments under a separation algebra built in
both arms; soundness = the frame rule; this retires the hdisj trap." It did not say what the algebra's carrier or the frame
theorem's statement is. This file supplies both. It is an INPUT, so both arms receive these bytes. It was written by vir
2026-11-02, **before either arm's first file of the separation model**. The Lean arm's syntactic typing (virp, stage 1)
exists. It does not depend on this file.

## S1. Locations and fragments
```
Loc  ::= wire(i)  (i : nat)          -- one byte of the frame buffer
       | bucket(p) (p : int)         -- sender p's token cell
Frag  = Loc ⇀ int                    -- a PARTIAL map: the locations a fragment owns, with their contents
h1 # h2  ⇔  dom h1 ∩ dom h2 = ∅       -- disjointness
h1 ⊎ h2  =  the union (defined when h1 # h2)      emp = the empty map
```
The ACL is NOT in Loc. It is read-only in the fragment, so it is a shared, unowned argument (a persistent region). An arm
that owns it instead must say so beside its counts.

## S2. The algebra's laws (each a theorem in each arm, never an axiom)
`h ⊎ emp = h` · `h1 ⊎ h2 = h2 ⊎ h1` · `(h1 ⊎ h2) ⊎ h3 = h1 ⊎ (h2 ⊎ h3)` (under the # side conditions) · `h1 # (h2 ⊎ h3) ⇔ h1 # h2 ∧ h1 # h3`.

## S3. What a type owns (the resource predicates)
- `tok` at sender p, after the guard has read `has_tokens(st, p)`: owns `{bucket(p)}`, the ONE cell `dec_tokens` writes.
- `slice` at offset o of a frame of length n: owns `{wire(i) | o ≤ i < n}` read-only. Affine, so it may be dropped.
- `int`, `bool`: own nothing.

## S4. THE FRAME THEOREM (the statement both arms prove, for the router's F)
For every store σ, every sender p = `read_u32(b0, 4)` and every fragment `h_f` with `h_f # ({bucket(p)} ∪ wire(0..n))`:
if ⟦F⟧ σ = (σ', ℓ), then every location in `dom h_f` holds the same value in σ' as in σ. **No disjointness premise names a
region the program does not touch.** The x86 form of this is the hdisj trap: a hypothesis excluding the whole bucket array,
narrowed at spike d7e992c to "the current sender's cell". S4 is the abstract statement of that narrowed form, as a property
of the meaning.

## S5. Counted, per arm (no direction predicted: this file was written after amend-11, so S-counts are EXPLORATORY)
the algebra's own lemmas (S2) · the lemmas bridging the arm's store to Frag · the frame theorem's proof size (C5) · whether
the arm's logic supplies S2 from a library (Lean: mathlib's partial-map / `Finmap` or a hand-built map; MetaPRL: its own).
A library lemma at the pinned release is FRAMEWORK under amend-12.
