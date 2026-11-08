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
- **AMENDMENT 2026-11-03 (after the fifth non-author pass, read at 5203f3300; the text above is left as declared):** the
  Y1 sentence's second half is false at that pin. L2's partiality ADDS `theories/vir/itt_bar_list.ml` (prims `adm_heap`
  and `bar_spread`; the census of `prim` under theories/vir reads 33 = 31 + 2), and those 2 are counted in L2's prim figure,
  reported beside L1's W6b figure. `itt_bar_bset` is NOT in L2's ancestry. Y1's letter (no `prim` in any `virl2_*`
  theory) still holds, so a Y1 score read from the `virl2_*` theories alone does not show the 2; this note is where they are.
- **AMENDMENT 2026-11-04 (after the sixth non-author pass, wf_86201b85-bbf, read at 37b871ec8; the text above is left as
  declared):** L2's ADEQUACY adds a THIRD framework prim, `adm_res_set` in `theories/vir/itt_bar_res.ml` (posted before it
  was written; the sixth pass ruled it SOUND); the census of `prim` under theories/vir reads **34 = 33 + 1**. L2's framework
  prims are adm_heap, bar_spread and adm_res_set; adm_res_set's text names no VIR term (vir's content test, ruled 00:53), and it
  was written FOR L2's adequacy, so it is printed beside L2's figure. `itt_bar_bset` is still NOT in L2's ancestry at this pin
  (CONS clause 3's direction (ii) would put it there: priced before that clause is written).

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
  **AMENDMENT 2026-11-04 (the sixth pass's note):** the code's terminal is ANY `ret` node (`is_terminal`, virl1_step); whether
  its argument evaluates to a value is `retv`'s inl/inr, read by the triple and by adequacy. The sentence above drifts from it.
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
- **AMENDMENT 2026-11-03 (after the fifth non-author pass; the text above is left as declared):** D4 is realised as
  `den2{e; s} ∈ bar{BTerm{0} × Store}`, ONE fix over CONFIGURATIONS (`den2c` at `x: (BTerm{0} × Store) → bar{BTerm{0} × Store}`,
  uncurried); D4's `den2{e}` is `λs. den2{e; s}`. The codomain is `BTerm{0}`, WEAKER than D4's `Val` (L1 made the same
  choice for `den`); `Val × Store` is OWED, reachable by adm_prod of adm_bterm_sub and adm_store once the module extends
  itt_bar_bset. The let clause is STRICT (forced with `bar_spread`), as OBJECT-L1 §6's strict bind; app / if / eff are
  l2step's own clause terms (a fault denotes ⊥). The two prims carry den2's TYPING only: of the module's 21 rules at the
  pin, 16 rest on them (14 on adm_heap through the intro resource, 5 on bar_spread, 3 on both) and the 21 are withheld
  together. ADEQUACY's halting direction is UNPRICED: it needs adm of a predicate subset coupled across BTerm{0} × Store,
  which no rule at the pin gives, so expect a third admissibility rule or an encoding (posted as a design question first).
- **AMENDMENT 2026-11-04 (ADEQUACY proved, local mojave/vir-l2 11a8e8737; the text above is left as declared):** the third
  admissibility rule is `adm_res_set` (D0's 11-04 amendment). `virl2_adeq` (37 rules, 0 prims, FRESH) proves `den2_adequate`:
  `c ∈ BTerm{0} × Store`, `halts{den2c{c}}` ⊢ `squash{adq{c; den2c{c}}}`, where `adq{c; r}` = ∃ c₁. reach{c; c₁} ∧ c₁ terminal ∧
  `retv{fst c₁} = inl{fst r}` in BTerm + unit ∧ `snd c₁ = snd r` in Store. It is SQUASHED because set elimination yields only
  a squashed predicate (no Markov rule is in the ancestry). By fixpoint induction at `adqT = c → bar{adqS{c}}`, admissible by
  adm_fun, adm_bar and adm_res_set; the let clause by bar_spread and run determinism (reach_det). It is the FIRST theorem of
  this arm that equates values AS TERMS (L1 N1's 11-04 amendment carries the limit).

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
- **AMENDMENT 2026-11-03 (declared on the bus at 16:22 for the scorer; the text above is left as declared):** the frame
  rule `triple_frame` is proved WITHOUT per-operation locality lemmas. The triple quantifies over every frame, so the
  proof needs only associativity of the store union both ways; locality is paid per operation inside the four small
  axioms, each proved at an arbitrary frame. Whether that meets Y4 is the scorer's reading.
- **Y3, WHAT THE CLAIM RESTS ON (declared 2026-11-04 for the scorer, on vir's 00:19 (4)):** the refiner's own DEPENDENCY SET of
  `triple_frame` (MetaPRL `check ()`, i.e. `Refine.compute_dependencies` over the checked primitive proof: every rule,
  rewrite and definition the proof uses, however it was invoked — by name, by autoT/resolution, by a resource) contains
  NO member of `virl2_typing`: 290 members (81 rules · 181 definitions · 25 rewrites · 3 conditional rewrites), 0 from
  `virl2_typing`. LIVE CONTROL, same session and parser: 3 rules outside `virl2_typing` (virl2_tot `ty_unit0_wf`,
  `ty_cap0_wf`, `a_cvar0_wf`) DO carry `virl2_typing` members, so the axis can fire. Read over 188 rules of
  virl2_assert · virl2_tot · virl2_triple · virl2_rules · virl2_den, every one printing a dependency list (tools
  vir-arm-tools l2/y3/). ⚠️ LIMIT, beside it: the set is of NAMED objects, so it cannot see a typing fact re-proved
  outside `virl2_typing` under another name (that is vir's statement axis); and module ancestry gives no separation
  (virl2_typing is an ancestor of virl2_rules through virl2_assert).
- **The bounds-tolerant triple of L2-E1 + L2-E2** is a second definition `{P} e {v. Q}ᵢ`, identical except that a reachable
  configuration stuck at an INDEX FAULT is permitted: a `load`/`store` on a LIVE region with index ∉ [0, R(p)), or an
  `alloc` whose size is ≤ 0. Semantic typing (Y5) is stated with it:
  `tc2{n; Δ; e} = inl{τ}` ⇒ `{∗_{c∈Δ} region(c)} e {v. ⌜v ∈ ⟦τ⟧⌝ ∗ (region(v) if τ = cap)}ᵢ`, for closed e under the
  capability substitution, with no bounds premise inside ⊢₂.

## D7. Scoring notes the arm declares now
- C1–C6 and Y1–Y8 are taken from the `virl2_*` theories at the sha the arm names when it posts L2 CLOSED; counts are by
  per-module REPLAY (`status_all` in a fresh session per module), never by stored status.
- The arm's W3 work (products, sums) is on other branches and is NOT in L2's base.
- **CONS clause 3, the AGREEMENT (amended 2026-11-04 02:14 PST, local, uncounted until L2 CLOSED).** For a closed typed L1 program e
  (e ∈ L1Lang{sig1}, bdepth 0, tyok, tc{btrue; e} = inl{τ}) and any s ∈ Store, den and den2 agree in both directions:
  (i) `cons3_i` (virl2_cons): halts{den2{e; s}} ⇒ den{e} = fst{den2{e; s}} in bar{BTerm{0}} and snd{den2{e; s}} = s;
  (ii) `cons3_ii` (virl2_adq1): halts{den{e}} ⇒ den2{e; s} = (den{e}, s) in bar{BTerm{0} * Store}.
  (ii) rests on L1 adequacy (`den_adequate`, virl2_adq1, by fixpoint induction at adqT1).
- **REPRESENTATION DEVIATION (cons).** OBJECT-L2's clause states co-halting: ⟦e⟧₁ halts iff ⟦e⟧₂ halts at s. Here each
  direction is ONE equality in a bar type, with no separate halts conjunct. In (ii) the conclusion is a bar equality whose
  right side is a pair. Halting is part of that equality's PER, but no rule here moves halts{·} across it:
  `bar_halts` needs valuetype{T}, and BTerm{0} * Store has none (no valuetype rule for a set type or a list). Adding one
  would be a new framework prim, and none is added.
- **Trusted base these two rest on**, beyond L1's: itt_bar_res `adm_res_set` (den2_adequate, pass 6 SOUND),
  Itt_bar_bset `adm_bterm_sub` (ONE use, adm_adqS1; counted beside Y1 per vir's ruling), itt_bar_strict `bar_wdt`
  (the L1 let clause, as in virl1_dent).

## D8. Y5's domain: the grammar carving wfs2 (declared 2026-11-05, vir's ruling (A) @97,423,855; file hash before d8e336313f96c125 at 5b1bd7a7f)
- **The gap.** A HOAS `BTerm` is larger than OBJECT-L2 §2's grammar: a name (`a_cvar{k}` / `capv{p}`) can sit where the
  grammar has none — a numeral's child (`num_b0{a_cvar{0}}`), a type's children, a prim's or an eff's operator node.
  `tc2` / `tc2r` never read those positions (an `is_num_op` atom is `int`, its children unread), but `occ2` walks every
  child and `tc2r`'s let split (`lfilt2` / `lfiltn2`) reads `occ2`, so such a name counts as a USE.
- **Why it matters (M-F9).** On such a term route (A)'s invariant is not preserved: when the allocated region equals the
  stray name, the let split sends the region to a `ret` of a non-name, and `tc2r` reads `inr`. RUN: DRIVEN for the STEPPED term (`cex_step`, a scratch lemma never exported or committed: `tc2r{btrue; 7; [0]; let y: int = ret num_b0{a_cvar 0} in free capv 0; ret ()} ~ inr`, complete proof, 2026-11-05 19:1x PST; script vir-arm-tools l2/sem/mf9/cex_step.mp sha256/16 1172e19200b00724, transcript mf9/cex_step-run.raw 677b633fe5b03568). HAND-WORKED, not driven: that the pre-step source term types `inl ty_unit` at counter 5, dl nil, and that alloc steps it to the stepped term at region 0 (the brute-force drive of the source side timed out at 900 s).
- **The carving.** `wfs2{k; t}` (virl2_sem): L1's `wfs` (virl1_induct) over L2's operators — the constant `unit`, and
  `a_cvar` / `capv` each with an `isNum2` child; types read by `is_tyterm2`. Y5 WILL BE stated for `wfs2{2; e} = btrue`, and
  `inv2` will carry `wfs2{2; e}`. At this entry ONLY the definitions and their well-formedness are proved (`isNum2`,
  `wfs2`, their var/mk rewrites and wf rules); preservation by `l2step` is OWED.
- **Departures from L1's `wfs`, each a weakening:** (1) `isNum2` is a copy of L1's `isNum`, which `virl1_induct` does
  not export (its interface declares nothing, and no `virl1_*` file is edited); (2) a prim's and an eff's operator node
  is required to have NO CHILDREN (`beq_int{length{s}; 0}`) instead of L1's `opmem{p; sig_p{…}}` + arity; operator
  membership is checked by `tc2r` itself, so `wfs2` asks only what typing does not. ⛔ *Corrected by D8a (M-F11): this
  line read "membership and arity are checked by `tc2r` itself", which is false for the argument list's LENGTH; the
  arity now lives in wfs2's sorts 3-5.*
- **Scoring (vir's, fixed before any wfs2 proof):** wfs2, its preservation and its use in `tc2r_names`'s motive are
  COUNTED in Y5's C5 and reported as their own line, "grammar carving" (the L2 analogue of amend-19's stage S).
- **Open, not owed:** Y5 over raw `BTerm` (arm B). Y5 probably holds there too; no route is priced.

## D9. Y5's domain: the scoping carving scoped (declared 2026-11-05, vir's ruling (A') @97,501,252; file hash before 41035d70dee6ac8e at 9065db501)
- **The gap (M-F10).** D3 says a capability variable becomes `a_cvar{k}`, "fresh by a counter threaded through the
  checker". Neither `tc2` nor `tc2r` CHECKS that freshness: a let-cap names its new capability by the counter n, so a
  LITERAL `a_cvar{n}` already in the body is captured as that name.
- **Why it matters.** `let x : cap = alloc 1 (y. ret y) in ret a_cvar{5}`, at counter 5 with Δ = [], TYPES (the let-cap
  names its capability 5, and the literal is read as its use) and RUNS to `ret a_cvar{5}`, a placeholder rather than a
  region (the allocated region leaks). So Y5 ITSELF is false on such a term, not only the invariant. HAND-WORKED, not
  driven: by vir's ruling the drive of M-F10 waits until Y5 closes or the 11-08 cap passes (stepped half first, by
  `cex_step`'s method, at a committed tools sha).
- **The carving.** `scoped{n; dl; e}` (virl2_sem) := every name k with `occ2{k; e}` is in `dl`, and every name in `dl`
  is below n. In the object (OBJECT-L2 §4) Δ is a linear context of capability VARIABLES, so a literal name outside Δ is
  an unbound variable and the term is outside Y5's domain; `scoped` reads that scoping in the arm's placeholder encoding
  and does not narrow the theorem (vir: Lean has it by construction, a capability being a de Bruijn Γ entry). Y5 WILL
  BE stated with `scoped{n; Δ; e}` as a hypothesis beside `wfs2{2; e}`, and `inv2` will carry it. At this entry ONLY
  the definition and its well-formedness (`scoped_wf`) are proved; preservation by `l2step` is OWED.
- **Scoring (vir's, @97,501,252):** `scoped` and its preservation are COUNTED in Y5's C5 and in the "grammar carving"
  line, reported on their OWN sub-line (scoping) so the scoping cost reads apart from the grammar cost. At scoring
  RESULTS-7 quotes this file's hash before and after D9, as for D8.
- **Carried to vir's row 149, new (C):** a sorted language with scoped capability names removes BOTH D8 and D9.

## D8a. Amendment to D8: a prim's argument list has the object's arity (declared 2026-11-05, M-F11, rec (A'') proceeded on; file hash before d8c0eedca3f1d203 at abbebbd36)
- **The gap (M-F11).** `tc2r` and `aeval` read at most TWO prim arguments and never the list's tail, so in
  `cons(a1, cons(a2, T))` T is never typed and never evaluated. D8's `wfs2{1; _}` admits an argument list of any length,
  so a literal name in T was in the D8 + D9 domain. D8's departure (2) said *"operator membership and arity are checked by
  tc2r itself"*. That is FALSE for the argument list's LENGTH, and this amendment corrects it.
- **Why it matters (HAND-WORKED, not driven).** `let x:int = (eff unit free [a_cvar 3] (y. ret 0)) in ret prim(add, [0, 0,
  a_cvar 3])` at counter 4 with dl = [3] types int, and it is wfs2 and scoped. After the free and the let step,
  `ret prim(add, [0, 0, a_cvar 3])` with dl' = [] is NOT scoped, and its name 3 is freed. So no invariant that ties term
  names to dl or to the store is preserved. Y5's conclusion holds on this run (ret 0, int, dl []), so the gap is at the
  level of the invariant, like M-F9.
- **The carving.** OBJECT-L1 §2: *"every operator has its arity's number of arguments"*. `wfs2`'s prim branch now reads
  its argument list at sort 3: sort 3 := cons(atom, sort 4); sort 4 := nil | cons(atom, sort 5); sort 5 := nil. That is one
  or two atoms. A binary operator given one argument stays inside the carving, and tc2r types it inr, so it adds no unread
  position. wfs2's rewrites and wf and its bind and substl lemmas are re-proved over the five sorts. No other proof read
  wfs2's prim branch.
- **Scoring:** counted on the grammar-carving line with D8 (vir's ruling on the fork is owed; I proceeded on (A'')).

## D10. The index fault has the let congruence (declared 2026-11-07, vir's ruling (a) @98,653,117; file hash before 46ecd53af3eb5556 at 517d086da)
- **The gap (mojave against its own arm, @98,646,216).** D6's bounds-tolerant triple permits a reachable configuration
  "stuck at an INDEX FAULT". The arm's `is_ifault` (virl2_triple) read only the HEAD node, so it was bfalse at every
  `let`. `l2step`'s let arm steps a non-ret bound term and maps its `inr` to `inr`, so `let x = (load c[i]; v. ret v) in b`,
  with c live and i out of range, is a reachable fault that `is_ifault` did not permit. The arm's `triple_i` was
  therefore stronger than D6, and Y5 was false against it.
- **Why D6 already covers it (vir):** OBJECT-L2 §2 defines a fault as a configuration with no step; a let whose head is
  stuck at an out-of-bounds load/store, or at `alloc(n ≤ 0)` (L2-E2), has no step, and the fault it is stuck at is that
  index fault. The head-only definition was narrower than the object.
- **The change (virl2_triple, wt 517d086da; file virl2_triple.ml 3252107c67682b12 → 72d288d2b9a8bb04).** `ifault2{e; sg}`
  is the term recursion: an eff node's index fault exactly as before, a `let` node's is its bound term's, anything else
  bfalse. `is_ifault{c} := spread{c; e, sg. ifault2{e; sg}}`. New rules: `ifault2_wf` (bterm induction), `is_ifault0_wf`
  (re-proved; statement unchanged), `is_ifault_let` (is_ifault of a let = is_ifault of its bound term). No rule proved
  before this entry reads `is_ifault` except `is_ifault0_wf`'s users (virl2_rules), whose statement is unchanged.
- **Red backwards.** At the mutant wt 6d015121d (branch mojave/vir-l2-d10-mutant, never merged: the OLD definition, the
  same lemmas), `is_ifault_let`'s script leaves `bfalse = <e1's head-only test> in bool` open, which is false at an
  index-faulting e1. That is "shown unprovable with what was run", not a refutation by instance (tools l2/tri/MUTANT-D10.txt).
- **Provenance.** Source: OBJECT-L2 §2 with L2-E1/E2. Corroborated by the public Lean definition (IndexFault.letE,
  l2/VIRL2/Runtime.lean:59), which the finding cites; vir records it in FINDINGS beside Y5.
- **Scoring (vir's):** `is_ifault`, `ifault2`, `ifault2_wf`, `is_ifault0_wf` as re-proved and `is_ifault_let` are COUNTED
  in Y5's C5 (part of triple_i's statement). RESULTS-7 quotes this file's hash before and after D10, as for D8 and D9.
