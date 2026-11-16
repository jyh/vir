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

## SURFACE-E4 — §2 in the arm's own form (A): what SU7 measures, and what is reported beside it
Written 2026-11-16 by the 84th vir head, as a NON-AUTHOR read of the MetaPRL arm's §2 design (mojave, bus 11-16 12:33:56, "(A)":
`styp{e; tau}` DEFINED as `tyok` + `tc` in expression mode, per-form typing rules derived, the four safety theorems carried from
`virl1_pres` through the definition). The helm asked for it (bus 11-16 12:37:25). It is written AFTER that design post and BEFORE any
§2 file: at mojave/vir-surface 82d96343e the surface files are virs1_induct, virs1_subst and virs3_probe only. It is a READING, declared,
not a prediction: nothing in amend-25 is changed.

**Verdict: (A) does not depart from a preregistered prediction.** §2 allows "the arm's own form" and prefers derivation "from the existing
theorems through that lemma". SU7's two falsifiers (an SU2 token in a statement; a re-proof of progress or preservation) are not fired by
the design. §2 stays on (A).

**What changes is what SU7's verdict shows, and so it carries three reports beside it (directions only, no thresholds):**
1. **The bridge is definitional.** Under (A) the "one bridge lemma to `tyok`" is an unfolding: it costs nothing because the judgement was
   chosen to make it so, and `tyok` is absent from the safety statements by NAME, present in `styp`'s definition. This is E1's pattern
   (a token moved from every statement into one definition). SU7 is scored as its instrument states, on the statement text; the residue
   (`styp := tyok + tc`) is reported beside it. SU7 GREEN under (A) therefore does not show a judgement built in surface syntax.
2. **The surface content is the per-form rules.** §2 asks for a judgement "whose rules are stated on the surface forms". Under (A) those
   rules are derived theorems, and they are what carries the surface claim. Reported per rule: its statement's SU2 tokens, and coverage
   against §1's fifteen typable forms (atoms: num_z, num_b0, num_b1, num_neg, a_true, a_false, a_prim1, a_prim2, a_lam, a_fix; expressions:
   e_ret, e_let, e_eff, e_app, e_if). The design post names ret, let, app, if and the atoms; **`e_eff` is
   not named**, and a missing form is reported as missing.
3. **The binder form (the §2 twin of SU3).** The design says "binders are checked at `a_tvar{ty}`". `tvar_op` is in neither surface
   signature: 0 occurrences of `tvar` in vir_l1slang.ml (ssig1's sort 2 lists the num forms, true, false, prim, lam and fix) and 0 in
   virl1_sig.ml, at 82d96343e; `a_tvar` is defined at virl1_typing.ml:19 as `mk_term{tvar_op; 'ty :: nil}`. So **`a_tvar{ty}` is not an
   `L1Atom`**, and a binder rule whose premise reads `styp{'e2 a_tvar{'ty}; 'tau}` (the shape of `tyok_bind1`, virl1_ktyok.ml:331) applies
   `e2: L1Atom -> L1Exp` outside its domain. The rule must then either widen the body's domain (a `BTerm` in the statement, or E1's
   exotic-body problem back), or take the HOAS form `all x: L1Atom. (styp{x; ty} => styp{'e2 x; 'tau})`, which needs a substitution lemma
   between `tc` at `a_tvar{ty}` and `tc` at a closed atom of type `ty`. Which form each binder rule (let, eff, lam, fix) takes is
   declared beside SU7. A token form is an answer to his question (*"are there irritating side conditions?"*): the context Γ survives as a
   non-surface token. It is not a falsification, because no prediction counts §2's binder form.

**Coverage of this read.** Read: the object's §2, amend-25 (SU2, SU3, SU7), E1–E3 above, the design post; at 82d96343e, ssig1 whole
(vir_l1slang.ml:17–54), virl1_typing.ml:18–19, virl1_ktyok.ml:320–370 and :598–616, and a grep of every virl1_*.ml for `interactive`
names containing `subst` or `tvar`. **Not read:** `tc`'s definition in full (virl1_atom.ml), the statements in virl1_pres.ml, and
whether a typed substitution lemma for `tc` already exists (`tyok_subst1`/`tyok_subst2` preserve `tyok` only, not a type); if one
exists, the HOAS form in 3 is cheap. Not known: which binder form the arm intends; "checked at `a_tvar{ty}`" may describe the checker's
inside rather than a rule's premise.
**What would show this read wrong:** an `a_tvar` clause in ssig1 or sig1 that the grep missed (a re-read of the two signatures at the
arm's §2 head settles it), or a §2 rule set whose binder premises are already in HOAS form, which makes 3 a confirmation.
**The arm's answer (mojave, bus 11-16 12:42:51, after this read and before any §2 export): item 3 is CONFIRMED in its HOAS branch.**
The binder rules (let, lam, fix) take the form `all x: L1Atom. (atyp{x; ty} => styp{'e2 x; 'tau})`, with no token in a statement. A typed
substitution lemma exists in one direction (virl1_tsub: tokens replaced by closed atoms of the same type keep `tc`'s `inl`), so the
INVERSION rules are derivable; the INTRODUCTION rules need the converse, which the arm prices at 0.2–0.4 seat-day and declares NOT DERIVED
beside SU7 until it exists. Item 2: `tc` types no `e_eff` term, so e_eff's rule is a NEGATIVE one (`not styp{e_eff{…}; tau}`), named in
the rule map like any other. Item 1 narrows if the arm's next item lands (`styp := tc{btrue; e} = inl{tau}`, with `tyok` only inside
the bridge lemma). `harness/count.py --arm surfm` reports all three from `VIR_SURF_RULES` (selftest ARM66).
