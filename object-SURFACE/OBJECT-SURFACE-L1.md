# OBJECT-SURFACE-L1 — L1's induction and safety theorems stated in SURFACE syntax (MetaPRL arm)

**Written 2026-11-15 by the 81st vir head and PINNED at this file's commit, on the Captain's word in the 11-15 walkthrough** (vir's
pane, after the 11-15 council; his words: *"we want the surface syntax like M, but embedded in ITT using the reflection library.
And then in principle the rules of M would be derivable. We don't know if it could be done in practice. The key is l1_induction,
can we state it using surface syntax, or are there irritating side conditions?"*, then, to the target below, *"yes let's do
that"*). **Nothing in this file is edited after its pin.** An erratum goes in `errata/ERRATA-SURFACE.md`. Predictions:
`predictions/PREDICTIONS-amend-25.md`, in this file's commit.

**This object is INFORMED, and says so.** It was written by the party that scores the MetaPRL arm, after reading that arm's
statements at its L5-closed tree (mojave/vir-l5 at 2d9a6c7f0): `l1_induction` (virl1_induct.ml:321), `l1s_induction`
(vir_l1slang.ml:217), `preservation` / `progress` / `safety` / `determinism` (virl1_pres.ml:429–600), and the surface syntax
`virl1_syntax.ml`. It was also written after reading the 2003 compiler (metaprl `theories/experimental/compile`: M's syntax
`declare`d, 237 `prim_rw`, 0 `interactive_rw`, no `Itt_*` theory extended). There is no Lean arm: Lean's syntax type is its
representation, so the question this object asks does not arise there.

## 0. The finding that prompted it
The MetaPRL arm defines a surface syntax over the reflected terms (`a_prim{'p; 'args} <--> mk_term{prim_op; mk_term{'p; nil} ::
'args :: nil}`, `a_lam{'ty; x.'e['x]} <--> mk_term{lam_op; 'ty :: bind{x.'e['x]} :: nil}`, …). Its public L1 theorems do not use
it. The induction rules state every case as `mk_bterm{'d; op; subterms}` with `bdepth` premises (and, in `l1_induction`,
the recognisers `wfs`, `is_tyterm`, `isNum`). The safety theorems quantify over `'e in L1Lang{sig1}` with `bdepth{'e} = 0`
and the computed `tyok{'e} = btrue`. So the measured MetaPRL costs at L1 (W2: 216 binder rules) and L2 (P2's well-formedness)
may partly measure this interface, not the logic. This object asks whether the surface interface can be DERIVED.

## 1. The target: L1 induction in surface syntax
Sorts are TYPES, as `l1s_induction` already has them: `L1Ty = L1SLang{0}`, `L1Num = L1SLang{1}`, `L1Atom = L1SLang{2}`,
`L1Exp = L1SLang{3}`, `L1Eff = L1SLang{4}`, `L1Op1 = L1SLang{5}`, `L1Op2 = L1SLang{6}`, `L1Args = L1SLang{10}` (the arm may
name them differently and declares the mapping). The motives `Pt`, `Pa`, `Pe` range over CLOSED terms of their sort.
One premise per surface form, in `virl1_syntax.ml`'s names:
```
[wf]     <H>; t: L1Ty   >- 'Pt['t] Type        (and Pa over L1Atom, Pe over L1Exp)
[T1]     <H> >- 'Pt[ty_int]          <H> >- 'Pt[ty_bool]
[T2]     <H>; t1: L1Ty; t2: L1Ty; 'Pt['t1]; 'Pt['t2] >- 'Pt[ty_arrow{'t1; 't2}]
[A2]     <H> >- 'Pa[num_z]   ·   <H>; n: L1Num >- 'Pa[num_b0{'n}]  (and num_b1, num_neg)   ·   'Pa[a_true]   ·   'Pa[a_false]
[A3]     <H>; p: L1Op1; a1: L1Atom; 'Pa['a1] >- 'Pa[a_prim1{'p; 'a1}]
         <H>; p: L1Op2; a1: L1Atom; a2: L1Atom; 'Pa['a1]; 'Pa['a2] >- 'Pa[a_prim2{'p; 'a1; 'a2}]
[A4]     <H>; ty: L1Ty; e: L1Atom -> L1Exp; a_lam{'ty; x.'e 'x} in L1Atom; 'Pt['ty];
              all x: L1Atom. ('Pa['x] => 'Pe['e 'x])
              >- 'Pa[a_lam{'ty; x.'e 'x}]
[A5]     <H>; ty1: L1Ty; ty2: L1Ty; e: L1Atom -> L1Atom -> L1Exp; a_fix{'ty1; 'ty2; f, x.'e 'f 'x} in L1Atom;
              'Pt['ty1]; 'Pt['ty2]; all f: L1Atom. all x: L1Atom. ('Pa['f] => 'Pa['x] => 'Pe['e 'f 'x])
              >- 'Pa[a_fix{'ty1; 'ty2; f, x.'e 'f 'x}]
[E1]     <H>; a: L1Atom; 'Pa['a] >- 'Pe[e_ret{'a}]
[E2]     <H>; ty: L1Ty; e1: L1Exp; e2: L1Atom -> L1Exp; e_let{'ty; 'e1; x.'e2 'x} in L1Exp;
              'Pt['ty]; 'Pe['e1]; all x: L1Atom. ('Pa['x] => 'Pe['e2 'x])
              >- 'Pe[e_let{'ty; 'e1; x.'e2 'x}]
[E3]     <H>; ty: L1Ty; o: L1Eff; args: L1Args; e: L1Atom -> L1Exp; e_eff{'ty; 'o; 'args; x.'e 'x} in L1Exp;
              'Pt['ty]; all_list{l1args{'args}; a. 'Pa['a]}; all x: L1Atom. ('Pa['x] => 'Pe['e 'x])
              >- 'Pe[e_eff{'ty; 'o; 'args; x.'e 'x}]
[E4]     <H>; a1: L1Atom; a2: L1Atom; 'Pa['a1]; 'Pa['a2] >- 'Pe[e_app{'a1; 'a2}]
[E5]     <H>; a: L1Atom; e1: L1Exp; e2: L1Exp; 'Pa['a]; 'Pe['e1]; 'Pe['e2] >- 'Pe[e_if{'a; 'e1; 'e2}]
conclusion:  <H> >- (all t: L1Ty. Pt) & (all t: L1Atom. Pa) & (all t: L1Exp. Pe)      (squashed, as l1s_induction's)
```
Read against the bterm rules:
- **No variable case.** A variable occurs only under its binder, and the binder's premise assumes `Pa` of it.
- **No depth, no `mk_bterm`, no recogniser** in any premise or the conclusion.
- **One membership hypothesis per binder** (`a_lam{…} in L1Atom` and its three siblings). It excludes EXOTIC bodies: a CTT
  function `e : L1Atom -> L1Exp` may inspect its argument, and `bind` of such a function is not a term. It is the surface
  replacement for the two `bdepth` premises.
- **The motive must tolerate `Pa[x]` as an assumption** for whatever is substituted (the usual price of HOAS induction; Lean pays
  the mirror image, a `var n` case over de Bruijn indices).

The expected derivation (a sketch; the arm chooses its own): by `l1s_induction`, prove the strengthened statement *for every open
term t of depth d and every substitution s of d closed atoms, each satisfying `Pa`, the motive holds of t[s]*. The variable case
is the assumption on s; a binder case extends s and is discharged by the surface premise. The reflection library supplies
`reduce_subst` (`subst{bind{x.'bt['x]}; 't} <--> 'bt['t]`, reflection/core/itt_hoas_base.ml:96) and `bind_eta`
(`bind{x. subst{'bt; 'x}} <--> 'bt` for `bdepth{'bt} > 0`, reflection/experimental/itt_hoas_bterm.ml:325).

## 2. The target: L1 safety in surface syntax
A typing judgement whose rules are stated on the surface forms (`Γ ⊢ e : τ` with Γ a list of surface types, or the arm's own form),
with ONE lemma tying it to the existing `tyok` (so nothing proved is thrown away). Then, over closed `e: L1Exp`, `τ: L1Ty`:
`preservation`, `progress`, `safety`, `determinism`, each statement free of `mk_bterm`, `bdepth`, `BTerm`, `L1Lang` and `tyok`.
They may be derived from the existing theorems through that lemma (preferred) or re-proved (declared).

## 3. The probe: one M-style rule, derived
One rewrite in the 2003 compiler's style, on surface syntax, PROVED: the atom-let inlining
`e_let{'ty; e_ret{'a}; x.'e2 'x}` ≡ `'e2 'a` as an equality of meanings (the arm's `den`, virl1_den.ml:45), for well-typed closed instances, stated with no
`mk_bterm`/`bdepth`. This is M's `LetAtom{'a; v.'e}` inlining, as an `interactive` theorem instead of a `prim_rw`.

## 4. What this object does not contain
L2–L5 (the same question repeats there, and is not asked until L1 answers it), any compiler, any edit to an L1 definition or rule,
any Lean work.

## 5. Size, as an ESTIMATE (not a measurement)
§1 is one derived rule plus a substitution-closed strengthening; §2 is one typing relation, one bridge lemma and four restatements;
§3 is one theorem. Basis: RESULTS-9 I5 (l1_induction's S stage 50,664 tokens, U 19,130), RESULTS-11 (l1s_induction's L1 stage
5,728). The arm prices it before its first file.

## 6. What would show this object wrong or unfair
the surface rule needing a premise this file does not list (that is a FINDING and the main result, not a failure) · a prediction
written after the arm's first surface file · an edit to an L1 rule or definition · a new primitive.
