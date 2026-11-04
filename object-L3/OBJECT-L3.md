# OBJECT-L3 — layer L3, the router as an L2 program (G1(a) G2(a) G3(a) G4(a))

**Drafted 2026-11-03 by the 16th vir head; PINNED 2026-11-03 by the 17th, BEFORE either arm's first L3 file**, on the
Captain's ruling at the 11-03 afternoon council (ask 1, his words: *"yes, pin them"*, as the sitting's minute records them):
every fork at its recommendation, G1 (a) one cell per byte · G2 (a) ONE region `world` · G3 (a) bounds by the logic, A.3's term
unchanged · G4 (a) the inequality by one witness frame AND the equality for `U_tx`. The layer plan is the Captain's (11-02,
OBJECT-L1 "The layers"): *"L3 the router as an L2 program (re-derive U = F, `run_tokens`, the frame property)"*.
The text below is the draft byte for byte except this status paragraph, the title line, and §2's and §3's references to the
draft (its own name for itself, and the programs file's draft name, now `inputs/L3-programs.md`). §2 keeps the forks' arms as the
record of what was ruled; the ruled arm is (a) in each. **Nothing in this file is edited after its pin.** An erratum goes in
`errata/ERRATA-L3.md`. Both arms receive these bytes and nothing else from each other. Predictions: `predictions/PREDICTIONS-amend-18.md`,
in this file's commit.

## 0. The rule L3 lives under
**L3 adds NO language.** Σ₃ = Σ₂, ⊢₃ = ⊢₂, ⟶₃ = ⟶₂, ⟦·⟧₃ = ⟦·⟧₂, and the logic is OBJECT-L2 §5's. L3 is PROGRAMS and
THEOREMS ABOUT THEM. Its conservative-extension theorem (OBJECT-L1 §8's form) is therefore the identity, and is not counted.
What L3 measures is how much of the VIR program's router (virp/, program 1) survives being written in the general language,
and what it costs to re-derive there what was proved in the special one.

## 1. What OBJECT-L2 forces on the router (stated so neither arm discovers it alone)
- **(R-a) ONE capability out.** §4: `ret a` with τ ≠ cap needs Δ = ∅, and `ret c` returns ONE capability. A product cannot
  carry a capability (atoms never mention one). So a router holding wire, ACL and bucket regions cannot give all three back.
- **(R-b) No capability crosses a function boundary**, and a λ/fix body is checked with Δ = ∅. So no L2 `fix` can loop over
  frames while holding the bucket region: the n-call property is a theorem of the LOGIC, never an L2 loop.
- **(R-c) No partial or uninterpreted operator.** P₂ = P₁ (no division, no `can_access` primitive). The ACL and the buckets
  must be STORE contents, read by `load`.

## 2. The forks (each: arms, recommendation, the default; ALL RULED (a) at the pin)
- **G1 — wire layout.** (a) one cell per BYTE, `read_u32(b, o)` = `b[o] + 256·b[o+1] + 65536·b[o+2] + 16777216·b[o+3]`
  (little-endian, four loads, P₁'s add/mul), each cell asserted in [0, 256) by the precondition; (b) one cell per 32-bit word.
  **Rec (a)**: it is the x86 layout and paris's `le32_toNat` crux, so L3 → A.4 stays one composition. Default (a).
- **G2 — regions under (R-a).** (a) ONE region `world` = [wire n bytes | ACL | buckets | out cells]; Δ = {world}; every exit
  writes its code (and the payload offset) to the out cells and does `ret world`. Typeable in L2 as it stands. The frame
  property inside the router becomes a statement about the contents function (`Function.update` at the touched cells);
  the frame RULE frames the caller's OTHER regions. (b) three regions, with a NEW ⊢₃ beside ⊢₂ that returns a TUPLE of
  capabilities: a real extension, contradicting §0, with a conservative-extension theorem owed. (c) three regions, the router
  written as a closed driver that allocates and frees them per call: no state survives a call, so `run_tokens` cannot be
  stated. **Rec (a)**: it is the literal reading ("an L2 program") and it MEASURES (R-a) instead of routing around it; (b)'s
  trigger is L4 (locks want several capabilities in flight). Default (a).
- **G3 — the ACL and bucket index.** A.3's `can_access(sender, topic)` and `has_tokens(st, sender)` index by u32 values.
  (a) bounds by LOGIC (F8's ruling at L2, carried up): ACL cell at `acl + sender·NT + topic`, bucket cell at `bk + sender`,
  NS, NT parameters; the router TERM is A.3's, with no added guard; the triple's precondition bounds sender < NS, topic < NT;
  an out-of-range frame is WELL-TYPED and INDEX-FAULTS (Y5 permits it; no triple holds for it). (b) add a range guard to the
  term, a recorded deviation from A.3. **Rec (a)**: faithful to A.3's bytes, and it is the M3 lesson at program scale.
  Default (a).
- **G4 — U = F, and what a drop means.** virp's U (I3) decrements the bucket BEFORE the ACL check, and virp's `U_eq_F` holds
  because its `drop` ABORTS (the state is discarded). In L2 an exit KEEPS its stores, so on a frame with tokens and no ACL
  bit, U's bucket is decremented and F's is not: **⟦U⟧₂ ≠ ⟦F⟧₂.** (a) prove the inequality (one witness frame) AND the
  equality for `U_tx`, U with that one exit undoing its decrement (a written-out rollback); (b) reorder U so the ACL check
  precedes the decrement (no longer I3's U); (c) add an aborting `drop` to L3 (an extension, contradicting §0). **Rec (a)**:
  it measures exactly what "drops abort" bought in the special language, and it is cheap to state. Default (a).

## 3. The statements L3 proves (both arms; G1–G3 at their recommendations)
U and F (terms: `inputs/L3-programs.md`) are written as L2 terms over Γ ; Δ = world : cap, transcribing virp's U (I3, I2's specs composed) and A.3's F
operation for operation (a `read_u32` is four loads; `dec_tokens` is load, sub, store).
1. **Typing.** Both U and F are ⊢₂-typed at `cap` (the returned world).
2. **U = F, under G4(a).** `⟦U⟧₂ ≠ ⟦F⟧₂` (one witness) and `⟦U_tx⟧₂ σ = ⟦F⟧₂ σ` for every σ (virp's `U_eq_F` is the
   special language's form, where drops abort).
3. **The router triple.** `{RegionAt(world, N, f) ∗ ⌜layout(f)⌝} F {v. v = world ∗ RegionAt(world, N, f′)}` with f′ = f
   updated at bucket(sender) (decremented) iff the frame is emitted, and at the out cells; `layout` = bytes in range, the
   ACL and bucket cells where G1/G3 put them, sender < NS ∧ topic < NT.
4. **The frame property** (vir-program-inputs S4, re-stated): f′ agrees with f off {bucket(sender)} ∪ out; and by OBJECT-L2
   §5's frame rule, the triple holds beside ANY frame R the caller owns, with no premise naming it.
5. **run_tokens** (virp's Trace): over n frames, by sequencing n instances of (3) in the LOGIC (R-b), the emits by sender p
   are at most p's initial tokens.
6. **The two refusals.** R7: a variant whose drop branch ends `ret 0` without returning `world` is ILL-TYPED (the leak, M4 at
   program scale). R8: F on a frame with sender ≥ NS is typed and INDEX-FAULTS (no triple; M3 at program scale).

## 4. What L3 does not contain
the x86 lowering (A.4 is paris's; L3 → A.4 composition is a later act), concurrency and locks (L4), I/O (L5), any new
operator, type or rule, and any edit to an L1 or L2 definition.
