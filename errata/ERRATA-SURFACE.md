# ERRATA-SURFACE — errata against object-SURFACE/OBJECT-SURFACE-L1.md (frozen at vir 5f2f9cf, blob 2e4e65d4a4f4)

The object is not edited. Each erratum below was found by the MetaPRL arm's PRICE READ (mojave, head 175, bus 11-15 12:03:41),
BEFORE any proof file and before any run. Each is also a direct answer to the Captain's question, *"are there irritating side
conditions?"*, and is recorded as such. Written 2026-11-15 by the 81st vir head.

## SURFACE-E1 — the sorts must be the CLOSED (depth-0) subsets
§1 writes `L1Ty = L1SLang{0}`, `L1Atom = L1SLang{2}`, and so on. `L1SLang{k} = SLang{ssig1; 2; k}` holds terms of EVERY binding depth,
so a conclusion `all t: L1SLang{0}. Pt` cannot follow from surface premises (e.g. `Pt[mk_bterm{1; int_op; nil}]` is not
`Pt[ty_int]`). **Correction:** the sorts are the depth-0 subsets, `{t: L1SLang{k} | bdepth{'t} = 0 in int}`, as DEFINED types.
**Reading of SU2, fixed here, after the price and before any proof (INFORMED, declared):** SU2 counts tokens in the rule's
STATEMENT. A `bdepth` inside the DEFINITION of a named sort type is not in the statement and is not counted; it is reported beside
SU2 as the residue of E1 (the depth has moved from every premise into one definition per sort).

## SURFACE-E2 — `a_prim` and `e_eff` take an OPERATOR, not a term
`unfold_a_prim` is `mk_term{prim_op; mk_term{'p; nil} :: 'args :: nil}`, and `unfold_e_eff` wraps `'o` the same way. So `p: L1Op1 =
L1SLang{5}` and `o: L1Eff = L1SLang{4}` do not type §1's A3 and E3. **Correction:** p and o range over OPERATORS whose
`mk_term{op; nil}` is a closed sort-5 (resp. sort-4) term: a defined, Operator-valued type, or the operator lists themselves.
This is notation, not a new premise.

## SURFACE-E3 — §3 as stated is not what `den` computes for a non-value atom
`l1phi`'s let case (virl1_den.ml:29–30) substitutes the VALUE of e1, so `den{e_let{ty; e_ret{a}; x.'e2 'x}} = den{'e2 v}` where
`aeval{a} = inl{v}`, not `den{'e2 'a}`. **Correction, two forms, the Captain's to choose between at the build:** (a) §3 with the
premise that a is a value (`aeval{'a} = inl{'a}`), which `reduce_subst` closes directly; (b) §3 for a general atom, which needs a
den-congruence lemma (`den{'e2 'a} = den{'e2 v}` when `aeval{'a} = inl{v}`), an induction through den's fixpoint. The same
distinction is in the 2003 compiler's README (2003-03-23: dead-atom elimination under eager evaluation, an atom that divides by zero).

## What the price read did NOT find
No premise in §1's cases beyond the four membership hypotheses (SU4 as predicted), and no variable case (SU5 as predicted).
The predictions (amend-25) stand as written; mojave's own expectation for SU6 (35–60k C5 tokens, above the ≤ 30,000 bound) is
recorded as its guess, not as an amendment.
