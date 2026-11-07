# L3, the Lean arm's declarations (amend-18, "owed by each arm before its first L3 file")

Written 2026-11-03 by the 17th vir head, on branch l3-lean (the Lean L2 arm, l2-lean 23e2cec, with the L3 pin 18df3a4 merged
in), ONE commit after the pin and BEFORE any `.lean` file under `l3/`. **SEALED:** the bus carries only this file's commit sha
and sha256 until the MetaPRL arm has posted its own L3 declarations (FINDINGS V-F5's rule). Both are quoted into the L3 scoreboard.

## The L2-closed sha, and what L3's proofs may cite
- **Lean L2-closed sha: vir dc95b53** (RESULTS-7). L3's proofs cite only theorems and definitions of `VIRL2` (and, through it,
  `VIRL1`) present at that sha: among them `stepFn₂` and `Steps₂` (⟶₂), `HasType₂` (⊢₂), `den₂` and `adequacy₂` (⟦·⟧₂),
  `Triple`, `frame` and the rules and small axioms of `VIRL2/Rules.lean` · `Axioms.lean` · `Triples.lean`, and `y5_closed`.
- **L2 is IMPORTED, never edited (Z1).** Z1 reads `count.py --arm w8 --prefix l2/VIRL2` with BASE = dc95b53 and EXT = the Lean
  arm's L3-closed sha; L1 is read the same way with `--prefix l1/VIRL1` from the same base.

## Where L3 lives
- A SEPARATE lake project `l3/` (lib `VIRL3`), beside `l1/` and `l2/`, requiring `l2` by PATH (`../l2`, which requires `../l1`)
  and mathlib at salt's pin (packages APFS-cloned from `l2/`, manifest written by edit; never a bare lake update). Every build
  through `l3/logged-build.sh` (saltbuild, one log per run, `l3/logs/`).
- Files (planned names; a renamed file is declared again before it is scored): `VIRL3/Layout.lean` (NW, NS, NT, A, K and the
  macros) · `VIRL3/Router.lean` (the terms F, U, U_tx) · `VIRL3/Typing.lean` (R1) · `VIRL3/Inequality.lean` (R2) ·
  `VIRL3/Rollback.lean` (R3) · `VIRL3/RouterTriple.lean` (R4, R5) · `VIRL3/Trace.lean` (R6) · `VIRL3/Refusals.lean` (R7, R8).

## How the macros are expanded
- **By DEFINITIONS this arm states**, as Lean functions building `Tm₂` terms over L2's de Bruijn syntax: `rd32 o k` (four
  `load`s at offsets 3+o … 6+o of the world capability, then the `add`/`mul` combination bound as one `int`; `k` is written five
  binders deeper), `exitC c` (one `store` of c at cell 1, then `ret` of the new capability) and `emit` (the two stores at cells 1
  and 2, then `ret`). F, U and U_tx are then single definitions in `Router.lean`, each one term.
- **The transcription check:** each of F, U, U_tx is printed with L1/L2's display form into a build log, and that text is
  compared against `inputs/L3-programs.md` with the macros expanded textually (by a harness script added red first, beside the
  B′ transcription check's precedent). A mismatch is a finding against this arm, not an erratum.
- The world capability is the one free variable (de Bruijn #0 at the top, Γ = [cap], Δ = {#0}); every `store` rebinds it, and
  later loads read the NEWEST binding, exactly as the inputs file's `w1`, `w′`, `w″` do.

## The store, the layout, and the frame
- `world` is ONE region (G2 (a)) of 87 cells (NW 64, NS 4, NT 4 ⇒ A = 67, K = 83), at a base p, owned through L2's region
  assertion; its contents are a function `Fin 87 → ℤ` read through L2's store. `layout(f)` is a Prop over that function:
  LEN ≤ NW, wire cells in [0, 256), ACL cells in {0, 1}, the frame's sender < NS and topic < NT (G3 (a): bounds by the logic,
  the terms unchanged).
- R4's post-state is stated as `Function.update` at the bucket cell (decremented iff emitted) and at the out cells; R5's caller
  half is ONE application of L2's `frame` (Z6).
- R6 is an induction over a `List` of frames in the LOGIC, each step one instance of R4, with no L2 `fix` in any term (Z7).

## The two refusals
R7 by inverting `HasType₂` (the `ret 1` leaves the world unconsumed); R8 by running `stepFn₂` on the concrete store to the
stuck configuration at the bucket load and naming the index fault (Z8).
