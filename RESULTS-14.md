# RESULTS-14 — L1 in surface syntax on the MetaPRL arm (OBJECT-SURFACE-L1, PREDICTIONS-amend-25 SU1–SU8)

Scored 2026-11-16 by the 84th vir head at the arm's export **mojave/vir-surface 53e26e5e1** (bus 11-16 13:50:48), base 2d9a6c7f0
(the object's L5-closed base). Instrument: `harness/count.py --arm surfm` (selftest ARM65 + ARM66, SELFTEST rc 0), run on a clone with
the arm's declared names (its DECLARATIONS-SURFACE-METAPRL.md at 53e26e5e1):

```
VIR_SURF_ROOT=l1_surface_induction VIR_SURF_SAFETY=s2_preservation,s2_progress,s2_safety,s2_determinism VIR_SURF_INLINE=s3_let_atom \
VIR_SURF_RULES=num_z=r_num_z,num_b0=r_num_b0,num_b1=r_num_b1,num_neg=r_num_neg,a_true=r_true,a_false=r_false,a_prim1=r_not,a_prim2=r_add,\
a_lam=r_lam_inv,a_fix=r_fix_inv,e_ret=r_ret,e_let=r_let_inv_body,e_eff=r_eff_none,e_app=r_app,e_if=r_if \
python3 harness/count.py --arm surfm --base 2d9a6c7f0 --ext 53e26e5e1 <clone>
```

## His question first: *"can we state [l1_induction] using surface syntax, or are there irritating side conditions?"*
**Yes, it can be stated, and it is derived.** `l1_surface_induction` has one premise per surface form, no variable case, and no
`mk_bterm`, `bdepth`, `BTerm`, `L1Lang` or recogniser in its statement. Each binder case takes the HOAS form `all x: L1Atom. (Pa x => Pe (e x))`.
**The side conditions that remain, all of them found before any proof, and none of them a new premise in a case:**
1. **One membership hypothesis per binder** (A4 lam, A5 fix, E2 let, E3 eff: 4 in all), as the object predicted. It excludes exotic CTT
   bodies and replaces the two `bdepth` premises.
2. **The sorts are the CLOSED subsets** (SURFACE-E1): `L1C{k} = {x: L1SLang{k} | bdepth{x} = 0 in int}`. The depth leaves every premise and
   lives in one definition.
3. **Operators, not terms,** in `a_prim`/`e_eff` (SURFACE-E2). This is notation. It also makes `L1Eff` EMPTY (ssig1 has no sort-4 entry), so
   the e_eff case is vacuous.
4. **A meaning-level rewrite needs the VALUE premise** (SURFACE-E3, form (a), his choice). Stating it in CTT names `BTerm` as the TYPE of the
   two equalities. That is what falsifies SU8 below.
5. **§2's binder INTRODUCTION rules are not derived yet.** Inversion is proved for let, lam and fix. Introduction needs the converse of the arm's token-replacement lemma (SURFACE-E4, item 3; the arm's row 716).

## Scores
| id | prediction | measured at 53e26e5e1 | verdict |
|---|---|---|---|
| SU1 | §1 DERIVED; no new primitive, no L1 rule/definition edited | rules edited **0**, definitions edited **0**, new prims **0**; grounded on the arm's fresh replays (§2 15/25/5/5/4 at 13:50:48; §3 2/2 at 12:33:56); §1's replay is the arm's earlier post, not re-read by this head (Q) | **HOLDS** |
| SU2 | §1's statement: 0 SU2 tokens | **0** (control: 3 on `l1s_induction` at base). Beside it (E1): 8 definitions carry a token and are not counted: unfold_L1C, unfold_atyp, unfold_l1reach, unfold_l1steps, unfold_s1m, unfold_s1q, unfold_styp, unfold_tkm | **HOLDS** |
| SU3 | binder cases in HOAS form | hand read of A4, A5, E2, E3: each is `all x: L1Atom. ('Pa['x] => 'Pe[…])` (A5 over f and x), with no context, depth or fresh variable; the scorer lists 4 `all` premises | **HOLDS** |
| SU4 | one membership per binder (4), nothing else | membership **4** (A4, A5, E2, E3), extra **0**, over 18 non-[wf] cases and 3 [wf] | **HOLDS** |
| SU5 | no variable case | **0** premises concluding on `var{…}`; hand read agrees | **HOLDS** |
| SU6 | §1's derivation ≤ 30,000 C5 tokens | **76,835** over 50 new rules in the closure (11 definitions unstored, 0 tokens) | **FALSIFIED** (above the arm's own guess, 35–60k, too) |
| SU7 | §2's four statements free of SU2 tokens; derived through one bridge to `tyok` | tokens **0**; the closure names all four base `virl1_pres` theorems (derived, not re-proved); bridges by needle **2**: `s2_exp_tyok` (the bridge: `e in L1Exp ⇒ tyok{e}`) and `unfold_tkm`, which on a hand read is the MOTIVE of `s2_tyok_all`'s induction, not a bridge | **HOLDS** (one bridge, by hand read) |
| SU8 | §3 stated with no SU2 token, proved as an `interactive` rule | `interactive`, stored, ≥ 1 step; tokens **2**, both `BTerm`: `aeval{'a} = inl{'a} in BTerm + unit` (the value premise) and `… in bar{BTerm{0}}` (den's codomain) | **FALSIFIED** as worded. The object's own §3 bar (no `mk_bterm`/`bdepth`) is MET; the prediction was stricter than the object |

**SURFACE-E4's three reports, beside SU7** (directions, no thresholds):
1. **Definitional bridge: 0.** The judgement narrowed after E4 was written: `styp{e; tau} := tc{btrue; e} = inl{tau}`. `tyok` is not in it.
   The tie is a lemma (`s2_exp_tyok`, through `s2_tyok_all`: one `slang_induction` at ssig1, 366,642 primitive steps on the arm's count).
2. **Per-form rules: 15 of 15 forms named.** Every named statement has **0** SU2 tokens, including all eight per-operator `a_prim2` rules (r_add …
   r_or, read one by one, control 1 on `s3_let_atom`). **Declared beside the count:** let, lam and fix are covered by INVERSION rules only
   (`r_let_inv_body`, `r_lam_inv`, `r_fix_inv`). e_eff is `r_eff_none`, which holds VACUOUSLY (L1Eff is empty). The map names one representative
   per form; the scorer does not tell introduction from inversion.
3. **Binder form: HOAS 4 of 4, token form 0.** `tvar` in ssig1/sig1: **0** (control `arrow_op` non-zero). E4's falsifier did not fire.

**Directions recorded in amend-25 (no thresholds):** whether §2's `s2_preservation` is shorter than the base `preservation` is NOT measured
here. §3 goes through `den` directly (`den_let`, `den_ret`, `reduce_subst`) and does not use §2's bridge.

## Limits
- **Scored at an export, not a close.** The arm's binder introduction (row 716) and L1Exp step-closure (row 717) are still to come. Neither is
  predicted, and a later sha does not change SU1–SU8 unless it edits the rules scored here. A re-score is owed on any such edit.
- **SU6 is an upper bound** in the arm's unit (whitespace tokens of stored proofs). The closure is every NEW rule reachable from
  `l1_surface_induction`, and `l1s_induction`'s own derivation is excluded.
- **The scorer limit found while scoring,** and fixed in the same change: `SU.E4.bridgeDefinitional` counted any definition naming `tyok`
  (it read 1, `unfold_tkm`). It now counts only definitions of a judgement that a safety statement uses (ARM66 fixture `unfold_mot`, red
  first: the old code read 2). It reads **0** here.
- **O104**, the arm's lessons-learned log, is read beside these scores and never scored.

## What would show these scores wrong
an edit to a pre-existing L1 rule or definition at a later sha that the census misses (re-run `--ext` at the arm's close) · a binder premise
whose HOAS reading depends on a definition the hand read did not open · an SU8 reading in which the type of a CTT equality is not part of
a statement (that would be a new reading, declared and dated, not a re-score).

## Addendum 1 (2026-11-16, the 84th vir head): binder INTRODUCTION derived at mojave 1fcceef92
The arm closed its row 716 (bus 11-16 14:52:42): `virs2_rsub` (22 rules, the converse token lemma) and `virs2_intro` (16 rules), exported,
fresh replays 22/22 and 16/16. The arm also reports a mutant run: retyping the body premise of `r_let_intro` and the binder of `r_lam_intro`
left exactly those two incomplete. **This supersedes E4 report 2's "let, lam and fix are covered by INVERSION rules only".**
- **No scored rule changed:** `git diff --stat 53e26e5e1 1fcceef92` is 8 files, +5,907, 0 deletions (two new modules and their
  declarations), so SU1–SU8 stand as scored above. A re-run of `surfm` at 1fcceef92 gives the same value on every SU row. The one
  difference is the E1 residue beside SU2, 8 → 12 (`unfold_ratom`, `unfold_rsubArgs`, `unfold_rsubP`, `unfold_rsubRest`: definitions inside
  the new lemma, not in any statement).
- **E4 report 2, re-run with the introduction rules** (`a_lam=r_lam_intro,a_fix=r_fix_intro,e_let=r_let_intro`, the rest as above): 15 of 15
  forms, **0** SU2 tokens in any named statement, binder form HOAS for 4 of 4, `tvar` 0. Hand read of `r_let_intro`: its premises are
  `styp{'e1; 't1}` and `all x: L1Atom. (atyp{'x; 't1} => styp{'e2 'x; 't2}`, with the let's membership `e_let{…} in L1Exp` as a [wf]
  premise, the same side condition as §1's per-binder membership.
- **For his question, one more condition, not a premise:** introduction needs every L1 type to have an atom (`s2_inhab_all`: `num_z`,
  `a_true`, `a_lam{t1; x. e_ret{w}}`, by `l1_surface_induction`), because a HOAS premise has to be instantiated at some atom. It is a
  derived lemma. The converse token lemma states one premise beyond the forward lemma, `ratom{v}`, which the arm declares semantically
  redundant for an atom-typed `v`. That premise sits in a helper lemma, not in any surface rule scored here.
- **Not re-measured here:** the arm's mutant (its report, Q); its row 717 (L1Exp closed under a step), which is optional, unpredicted and
  in progress.
