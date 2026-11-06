# O95 L3 — DECLARATIONS of the MetaPRL arm (amend-18), before its first L3 file

Written 2026-11-05 by mojave (the MetaPRL arm), on branch `mojave/vir-l2` of a local metaprl clone (push disabled), on
parent **265c1b8e1** (L2 part 77; Y5 OPEN, its cap 2026-11-08 by the Captain's word of 11-05). This file is the branch's
first L3 artifact: at its commit no `virl3_*` file exists, and `git log --all -S'U_tx'` and `-S'RD32'` in this clone read
0 commits each (control `-S'tc2r_rsub0'` reads 2).

**What the arm had read when it wrote this:** `object-L3/OBJECT-L3.md`, `inputs/L3-programs.md` and
`predictions/PREDICTIONS-amend-18.md` at their pin vir 18df3a4; `errata/ERRATA-L3.md` row L3-E1 (vir fcaae75), which
describes the two frames that falsify R3 as written and names the Lean arm's file and lemma names for them; the HEADERS
and COUNTS-ONLY bodies of vir's L3 posts. It has NOT read any file under vir's `l3/`, any Lean L3 file, any L3 branch,
or the Lean arm's L3 declarations.

## E1. Where the L3 terms and proofs live
- Files: `theories/vir/virl3_*.ml` (+ `.prla`) on `mojave/vir-l2`. Planned: `virl3_prog` (the numerals, the layout,
  the terms F, U, U_tx, F7 and the store σ8 of R8) · `virl3_typ` (R1, R7) · `virl3_eq` (R2, R3) · `virl3_tri` (R4, R5,
  R8) · `virl3_run` (R6). A module may be split; every L3 module is `virl3_*`.
- **No `virl2_*` or `virl1_*` file is edited by L3** (Z1 is read as the `virl2_*` theories at the L2-closed sha, E3,
  against the same theories at the L3-closed sha). L3 adds no operator, type, rule or `prim`.
- **The free variable w.** Each of F, U, U_tx, F7 is a `define`d L2Src term of binding depth 1, `bind{w. body}`, with no
  other free variable. The judgment `(w:cap) ; {w} ⊢₂ F : cap` is `tc2{1; 0 :: nil; subst{F; a_cvar{0}}} = inl{ty_cap}`
  (the checker's own reading of a capability binder, DECLARATIONS-L2 D3), and F RUNS as `subst{F; capv{p}}` on a store
  whose region at base p is `world`.
- **The numerals are the pin's:** NW = 64, NS = 4, NT = 4, A = 67, K = 83, 87 cells, as L1 numerals; `1297303345` the
  magic. `add(A, add(mul(sender, NT), topic))` etc. are written with P₁'s `add`/`mul` exactly as the inputs file writes them.

## E2. How RD32, EXIT and EMIT are expanded
- **TEXTUALLY, before any proof reads a term**, as the inputs file says they are notation. No macro is a definition in
  any theory: the `define` of F (U, U_tx, F7) IS the expanded term. The expansion is done by a generator script kept in
  the arm's tool tree (not in the theory), which reads the inputs file's term text and its three macro clauses and emits
  the term; fresh names per `RD32` use are its binder names (`magic0..magic3`, `sender0..`, `topic0..`).
- `EMIT[w1/w]` and `EXIT(2)[w1/w]` are expanded with w1 in place of w, as written. **U_tx** is U with its post-decrement
  `EXIT(2)[w1/w]` replaced by `let w2:cap ← store(w1, add(K, sender), t) in EXIT(2)[w2/w]` (R3's row: the decrement
  undone, then the exit). **F7** (R7) is F with `EXIT(1)` replaced by `ret 1`.
- A read-back check is owed with the module: the generated term, printed back in the inputs file's concrete syntax, is
  compared with the inputs file's text after expansion; its result is reported with R1.

## E3. Which L2 rules the L3 proofs may cite (the L2-closed sha)
- **Only the L2 program logic and its meaning:** `virl2_sig`, `virl2_store`, `virl2_stok`, `virl2_step`,
  `virl2_typing`, `virl2_assert`, `virl2_tot`, `virl2_triple`, `virl2_rules`, `virl2_den`, `virl2_adeq`. The triple is
  DEFINED semantically from ⟶₂ (DECLARATIONS-L2 D6), so R4–R6 and R8 are proved from the step, not from type soundness.
- **No L3 proof cites `virl2_sem*` (Y5) or `virl2_cons*`/`virl2_adq1`**, whether or not Y5 closes before the first L3
  file. L3's scores are then independent of Y5's cap.
- **The L2-closed sha** is the sha of this branch at which every cited module replays complete (fresh load), named with
  its counts in a post BEFORE the first `virl3_*` file is committed. It is not this file's parent: the declarations name
  the set; the sha is posted when L3 starts.

## E4. The statements, in this arm's forms (R1–R8 of the inputs file; L3-E1's reading for R3)
- **R1:** `tc2{1; 0 :: nil; subst{X; a_cvar{0}}} = inl{ty_cap}` for X = F and X = U.
- **R2:** one concrete store σ (one frame with tokens and no ACL bit, `layout` holding) with
  `den2{subst{U; capv{p}}; σ} ≠ den2{subst{F; capv{p}}; σ}`, by evaluation (`l2iter` to the two terminals) and adequacy.
- **R3:** for every `store_ok` σ in which p is a live 87-cell region whose contents satisfy `layout`:
  `den2{subst{U_tx; capv{p}}; σ} = den2{subst{F; capv{p}}; σ}`.
- **R4:** the triple of OBJECT-L3 §3.3 in D6's form: `RegionAt(p, 87, f) ∗ ⌜layout(f)⌝` before, `v = capv{p} ∗
  RegionAt(p, 87, f′)` after, with f′ given as an update of f at `K + sender` (iff emitted) and the out cells 1, 2.
- **R5:** f′ agrees with f off `{K + sender, 1, 2}`; and the triple beside any frame R by `virl2_rules`' frame rule.
- **R6:** by induction on a list of n frames, each written into cells 0 and 3…66 between calls (ACL cells untouched), the
  emits by sender s number at most f(K + s): n instances of R4 sequenced in the logic, no L2 loop (R-b).
- **R7:** `tc2{1; 0 :: nil; subst{F7; a_cvar{0}}} = inr{it}` (ill-typed: the world is not returned).
- **R8:** a store σ8 (magic correct, sender = NS): R1's typing holds, and from `(subst{F; capv{p}}, σ8)` ⟶₂* reaches a
  configuration with no step that is not terminal (an index fault at the bucket load); hence no R4 instance holds at σ8.
