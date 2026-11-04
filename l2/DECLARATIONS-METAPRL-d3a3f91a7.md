# O95 L2 — DECLARATIONS of the MetaPRL arm (amend-16), before its first L2 file

Written 2026-11-03 by mojave (the MetaPRL arm), on branch `mojave/vir-l2` of a local metaprl clone (push disabled), at
base **ec912bd80** = the L1-closed tree (be5312958's theories + the census file; replays 672/672). This file is the
branch's FIRST commit; no `virl2_*` file exists at it.

**What the arm had read when it wrote this:** OBJECT-L2, `inputs/L2-programs.md` and PREDICTIONS-amend-16 at vir dec0cdd;
ERRATA-L2 rows L2-E1 and L2-E2 (vir master 622e3d9); the HEADERS and COUNTS-ONLY bodies of vir's L2 posts. It has NOT read
`l2/DECLARATIONS-LEAN.md`, any `l2/` file, or the `l2-lean` branch.

## D0. Where L2 lives, and the no-edit rule (W8 / Y2)
- Files: `theories/vir/virl2_*.ml` (+ their `.prla`), on `mojave/vir-l2`. Planned modules, in chain order:
  `virl2_sig` (Σ₂, the L2 language) · `virl2_store` (stores, the four operations on a store) · `virl2_step` (⟶₂, ⟶₂*,
  faults) · `virl2_typing` (Δ, its split, ⊢₂) · `virl2_den` (⟦·⟧₂) · `virl2_assert` (assertions, ∗, region) ·
  `virl2_triple` (triples, the frame rule, small axioms, structural rules) · `virl2_sem` (semantic typing, Y5) ·
  `virl2_cons` (§7, the conservative extension) · `virl2_prog` (M1–M5). A module may be split; the names above are the
  prefix, and every L2 module is `virl2_*`.
- **No `virl1_*` file is edited.** Y2 is read as: the `virl1_*` theories at ec912bd80 vs at the arm's L2-closed sha.
- **Σ₂ is a new SIGNATURE value, not an edit of L1's.** L1 is already parameterised by a signature `s = (B, P, O)`
  (lists of operator codes) with `L1Lang{s} = Lang{SubOp{sig_ops{s}}}` (`virl1_sig`). L2 defines
  `sig2 = ((int_op :: bool_op :: unit_op :: cap_op :: nil), (P₁'s list), (alloc_op :: load_op :: store_op :: free_op :: nil))`.
  An L2 operation is L1's effect binder `e_eff{τ; o; args; x. e}` with `o ∈ O₂`; no new expression former.
- The constants `()` (`unit_val_op`) and the runtime capability `⟨p⟩` (`capv_op`, one child: an L1 numeral for p) are
  operators OUTSIDE `sig_ops{sig2}`: `L2Src = Lang{SubOp{append{sig_ops{sig2}; unit_val_op :: nil}}}` is the source
  language (no `⟨p⟩`), and `L2Run = Lang{SubOp{append{sig_ops{sig2}; unit_val_op :: capv_op :: nil}}}` the configurations'
  language. Both are `L2` definitions; L1Lang{sig2} ⊆ L2Src ⊆ L2Run.
- Y1: everything below is DEFINED (`define` + `interactive`); no `prim` in any `virl2_*` theory. Partiality reuses the
  bar-type theories the L1 arm already uses (itt_bar, itt_bar_strict, itt_bar_bset), which are counted where L1 counted them.

## D1. The store's representation (H, R)
- `σ = (H, R)` with **H : list{int × int}** (address, value) and **R : list{int × int}** (base, length): FINITE ASSOCIATION
  LISTS. Lookups `hget{H; a}`, `rget{R; p}` return `int + unit` (inl = present). Two stores are EQUAL when their lookups
  agree at every address (`st_eq`, pointwise); the list order carries no meaning.
- `store_ok{σ}`: keys distinct in each list; every region has length > 0; regions pairwise disjoint; and
  dom H = ⋃ {[p, p+n) | R(p) = n} (OBJECT-L2 §2), stated by lookups.
- Disjoint union `σ₁ ⊎ σ₂` is a RELATION `st_union{σ; σ₁; σ₂}` defined pointwise on lookups (each address/base is in at
  most one side, and σ's lookup is the side's). It is used by ∗ (D5) and by the frame (D6). A PARTIAL store (a piece that
  need not satisfy dom H = ⋃ R) has the same type.
- The four operations are functions on a store returning `(result × store) + unit` (inr = FAULT): `st_alloc{n; σ}`
  (n ≤ 0 ⇒ inr, per L2-E2's reading; else base p = the least integer ≥ every live region's end, i.e. max(p+n) over R, or 0
  when R is empty; n zero cells) · `st_load{p; i; σ}` · `st_store{p; i; v; σ}` · `st_free{p; σ}` (removes the region and
  its cells). Out of [p, p+R(p)) or p ∉ dom R ⇒ inr.

## D2. ⟶₂ (OBJECT-L2 §3)
- A configuration is a pair `(e, σ)`, e ∈ L2Run. ⟶₂ is a **total function** `l2step{c} : config + unit` (inr = no step),
  one `fix`, in the style of `l1step` (one equation per form). It lifts L1's six rules with σ unchanged (reusing L1's
  `aeval`, `app_val`, `subst`; its own congruence recursion, because e₁ in `let` may be an effect), plus one clause per O₂
  operation through D1's functions; `let x ← o(a⃗) in e ⟶₂ (e[v/x], σ′)`.
- Terminal = `ret a` with a evaluating to a value. A FAULT is a non-terminal configuration with no step.
- ⟶₂* is DEFINED from the step function: `l2iter{n; c}` (n steps, stopping at a terminal) and
  `reach{c; c′} = ∃ n:nat. l2iter{n; c} = inl{c′}`. The triple (D6) quantifies over `reach`; no fuel appears in any
  statement about the program logic or semantic typing.
- Determinism is a property of the function (one equation per form).

## D3. Δ and its split; ⊢₂ (OBJECT-L2 §4)
- L1's checker types an open term by SUBSTITUTING each bound variable with a typed placeholder atom (`a_tvar{τ}`). L2 does
  the same for ordinary variables, and substitutes a **capability variable** by a NAMED placeholder `a_cvar{k}` (k : nat,
  fresh by a counter threaded through the checker).
- **Δ is a list of capability names (list{nat}) with distinct elements**; order carries no meaning (membership only).
- **The split** is the relation `dsplit{Δ; Δ₁; Δ₂}`: Δ₁ and Δ₂ are disjoint and their union is Δ (membership, pointwise).
  ⊢₂ uses ONE particular split at `let`: Δ₁ = the names of Δ that OCCUR in e₁ (`cfree`), Δ₂ = the rest. The declared
  theorem owed (Y7): this is the ONLY split under which both halves can type (a name in Δ₁ not occurring in e₁ cannot be
  used exactly once; a name occurring in e₁ must be in Δ₁). So the relation and the checker's choice agree.
- **⊢₂ is a DEFINED total checker** `tc2{n; Δ; e} : (type) + unit` (inl τ = `Γ ; Δ ⊢₂ e : τ` with Γ carried by
  placeholders, as in L1), one `fix`, one equation per form; ⊢₂ the judgement is `tc2{…} = inl{τ}`. Its clauses are
  §4's, literally: atoms mention a capability placeholder only as an O₂ operand; `alloc` extends Δ with a fresh name;
  `load` requires c ∈ Δ and leaves Δ; `store` replaces c by a fresh c′; `free` removes c; `let` splits as above; `if`
  gives both branches Δ; `ret a` at τ ≠ cap requires Δ = nil; `ret c` requires Δ = [c]; λ / fix bodies are checked at
  Δ = nil and `cap` may not occur in their parameter or result types. Types: L1's plus `ty_unit`, `ty_cap`; type equality
  is its own `ty_eq2` (L1's `ty_eq` is not edited).
- §4's last bullet (`Γ ⊢₁ e : τ` ⇒ `Γ ; ∅ ⊢₂ e : τ`) is a theorem relating `tc` and `tc2`, proved in `virl2_cons`.

## D4. ⟦·⟧₂ (OBJECT-L2 §6, Y8)
- `den2{e} : Store → bar{Val × Store}`: ONE least fixed point Φ₂ by the same mechanism `den` used in L1 (the bar type's
  `fix`; M-F5), store-passing; FAULT denotes ⊥ (`fault ∉ Val`). Unfolding, soundness and adequacy against ⟶₂ are
  theorems. Its admissibility side condition is reported beside L1's W6b figure.

## D5. The assertion logic (OBJECT-L2 §5)
- **Shallow:** an assertion is a predicate on a (partial) store, `Assn = Store → U`. `emp` (both lists empty, up to
  `st_eq`), `p ↦ v` (H = {p ↦ v}, R empty), `P ∗ Q` (∃ σ₁ σ₂. `st_union{σ; σ₁; σ₂}` ∧ P σ₁ ∧ Q σ₂), pure `⌜φ⌝` (φ ∧ emp),
  ∃ over a type. `region(p, n)` = (∗_{0≤i<n} (p+i ↦ _)) ∗ (the R-piece {p ↦ n}), so the R(p) = n fact is a separable
  resource carried by the region, and `free` consumes it.

## D6. The triple: DEFINED SEMANTICALLY from ⟶₂ (not an inductive proof system)
- `{P} e {v. Q}` := for every frame σF and every σ with `P σ` and `σ ⊎ σF` store_ok, every configuration reachable
  (D2's `reach`) from (e, σ ⊎ σF) is NOT a fault, and every reachable terminal (ret a, σ′) has σ′ = σ₁′ ⊎ σF with
  `Q[aeval a / v] σ₁′`. (OBJECT-L2 §5's "from any σ ⊨ P ∗ R_frame", with the frame as a store.)
- The frame rule, the four small axioms and the structural rules (consequence, let, if, app via the callee's triple) are
  THEOREMS about this definition. The frame rule is proved from ⟶₂ by one locality lemma per O₂ operation plus L1's
  steps leaving σ alone (Y4), and its proof uses no ⊢₂ (Y3).
- **The bounds-tolerant triple of L2-E1 + L2-E2** is a second definition `{P} e {v. Q}ᵢ`, identical except that a reachable
  configuration stuck at an INDEX FAULT is permitted: a `load`/`store` on a LIVE region with index ∉ [0, R(p)), or an
  `alloc` whose size is ≤ 0. Semantic typing (Y5) is stated with it:
  `tc2{n; Δ; e} = inl{τ}` ⇒ `{∗_{c∈Δ} region(c)} e {v. ⌜v ∈ ⟦τ⟧⌝ ∗ (region(v) if τ = cap)}ᵢ`, for closed e under the
  capability substitution, with no bounds premise inside ⊢₂.

## D7. Scoring notes the arm declares now
- C1–C6 and Y1–Y8 are taken from the `virl2_*` theories at the sha the arm names when it posts L2 CLOSED; counts are by
  per-module REPLAY (`status_all` in a fresh session per module), never by stored status.
- The arm's W3 work (products, sums) is on other branches and is NOT in L2's base.
