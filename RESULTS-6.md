# RESULTS-6 — layer L1, the typed pure core (O95; OBJECT-L1 at vir dc44f15; amend-13, amend-14)

Every figure here is a row of `l1/out/counts-l1.tsv` (`harness/count.py --arm l1 l1`, re-derived by `harness/reproduce.sh`,
rc 0) or is labelled as something else. The MetaPRL column is scored in addendum 1 below, at the arm's L1 tree be5312958
(LOCAL: the arm's branch has push disabled), from `harness/metaprl-counts-l1.tsv` (`count.py --arm metaprll1`; H = a harness
row, Q = quoted from the arm's check_all, which no file records).

## The scoreboard (amend-13 W1–W8)
| prediction | Lean (l1/, this file's sha) | MetaPRL (mojave) | verdict |
|---|---|---|---|
| W1 C4vir = 0 | **0** (`L1.C4vir`) | **0** in 24 `virl1_*` theories (`L1M.W1`, H) | **HOLDS on both** |
| W1b framework MetaPRL > Lean | Lean: axioms beyond the standard three **0** (`L1.C4`); the standard three only (`L1.audit` 35 rows) | AT THE PIN: reflection **24** prims (`L1M.pinReflection`, the built dirs) + integers **32** (`L1M.pinInt`), H; the arm's closure figure for reflection 23 (Q). BESIDE: PARTIALITY THEORY **31** (`L1M.PARTIALITY`, NOT-AT-PIN: itt_bar 26 · itt_bar_bterm 1 · itt_bar_strict 3 · itt_bar_bset 1), FRAMEWORK EDITS **4** files (`L1M.frameworkEdits`; M-F6, M-F7). `L1M.floorMissing` **0** | **HOLDS** (56 > 3 on the pin figure alone) |
| W2a Lean ≥ 6 binder lemmas | **3** (`L1.binder`), and **1 BESIDE** (`L1.binder.substLOnly`) | — | **FALSIFIED** (3; 4 with the one beside) |
| W2b the MetaPRL count (no threshold) | — | **216** rules (`L1M.binder`, H, a LOWER BOUND: amend-11's four named operators only), of which REVIVED **23** (`virl1_hoas_lang`); `subst{` alone **51** (`L1M.binder.substOnly`) | reported |
| W2c MetaPRL < Lean | 3 | 216 (51 on `subst{` alone) | **FALSIFIED** (on every reading) |
| W3 (i) a new operator costs 0 edits, (ii) a type former costs Lean ≥ 3, MetaPRL 0 | — | — | after BOTH arms close (the extension commits) |
| W3b the parameter's own cost | the hypotheses about Σ: `Sig.Lawful` (2 fields) + `S.O → False` | unread (not measured in addendum 1) | EXPLORATORY |
| W4 the backend | not in L1 | — | at L3 |
| W5 K1–K5 agree | 120 · ¬Dom · 42 · 7 · 55, each terminating program with a ⟶* trace (`Programs.lean`) | 120 · ¬halts · 42 · 7 · 55 (`virl1_den` k1/k3/k4/k5_den, `virl1_k2` k2_diverges), traces `l1run{n; k}` = value (`virl1_step` k1/k3/k4/k5_run), typing `virl1_typing` ty_k1..k5; read at the object, replayed complete (Q, the arm's replay log) | **HOLDS on both** |
| W6 the fixpoint is used, and leastness for K2 | `L1.fix` **1** · `L1.leastness` **2** | `fix_intro` **3** uses (`L1M.fix`: dent · dsem · k2) · K2 **1** (`L1M.fixK2`), H. fix_intro is itt_bar's ONLY fixpoint rule and IS fixpoint induction, so use and leastness are one rule | **HOLDS on both** |
| W6b the side condition | `L1.continuity` **1** (`Φ_cont`, 12 lines) | adm by adm_fun · adm_bar · adm_bterm_depth (den_wf), adm_void (K2), adm_bterm_sub (den_typed): Q, from the arm's posts | EXPLORATORY |
| W7 the six steps close | all required theorems, no fuel, no primitive step rule (`l1/STAGE-L1-LEAN.md`) | substitution lemma (`virl1_tsub`), progress · preservation · safety · determinism (`virl1_pres`), unfolding (`den_unfold`), den_wf · den_sound (`virl1_dent`), den_typed (`virl1_dsem`); 0 prims in `virl1_*`; UNIQUENESS and WEAKENING by encoding (0 rules; addendum 1, limits) | **HOLDS on both**, with addendum 1's encoding limits |
| (W7) step 6b adequacy, scored when built | **built**: `adequacy`, `den_iff_steps` (build-013, audit-002) | not built (L1's close does not wait on it, OBJECT-L1 §6) | Lean BUILT · MetaPRL not built |
| W8 conservative extension | — | — | at L2 |

C6 for the Lean arm: 20 logged saltbuild runs (`L1.C6`; 13 builds, 2 scratch, 3 audit, 2 mutants).

## What the W2a falsification says
amend-13 predicted at least 6 Lean binder lemmas from two syntactic categories and three binder shapes. The arm needed 3 (4
counting `HasTypeL.subst`, which names the list half `substL` and is not on the frozen token list). The reason is structural,
not an accident of style: a call-by-value semantics of CLOSED programs substitutes only CLOSED values, so the arm defines no
shift, weakening is at the outer end of the context (no index arithmetic), and the substitution lemma is one mutual theorem.
The prediction was written from the router fragment's 6, where the store and runtime values made more binder work. **What it
does to W2c:** W2c (MetaPRL < Lean) now asks the MetaPRL arm to come in under 3, with Lang{sop}'s revived rules counted
VIR-side (amend-13's ruling).

## The MetaPRL arm's declarations (owed by amend-13 before its first L1 file; posted 17:50, 0 L1 files at the post)
D1 pin jyh/metaprl fb8e715d7 (libmojave 623f7ac), branch mojave/vir-l1 = the pin + itt_bar + L1 files only · D2 Σ as Lang{sop},
REVIVED from `theories/itt/reflection/obsolete/itt_hoas_lang.ml` (port status unmeasured at the post; the fallback is a BTerm
subset with its own wf predicate, to be announced before any count) · D3 files `theories/vir/virl1_{hoas_lang, sig, syntax,
eval, step, typing, safety, den, progs}` · D4 partial results `bar{Val}` from `theories/vir/itt_bar.ml`, ⟦·⟧ by itt_bar's fix
rule, K2's ¬halts by fixpoint induction. **The fork it named (itt_bar is not at the pin) is ruled in amend-14.**

## Addendum 1 — the MetaPRL column, scored at be5312958 (the 14th vir head, 2026-11-03, on the helm's 05:59 order)
**Where.** The arm's L1 tree mojave/vir-l1 at be5312958 (2026-11-03 05:56 PST), cloned into vir's scratch and read there, never in
the arm's checkout. The branch has push disabled, so a stranger cannot re-derive `harness/metaprl-counts-l1.tsv` until that sha is
public. This file names the sha so the rows can be checked the day it is. `L1M.floorMissing` 0: all five soundness repairs are
ancestors (FINDINGS M-F6, M-F7). The arm's check_all, by its per-module log at this tree, reads 28 modules and 641/641 derived rules
grounded: 635 in `virl1_*` + 6 in the partiality theories. **H = Q per file:** `L1M.interactive` 635 equals the 24 modules' grounded
sum, after the comment fix of M-F7 (2). Groundedness itself stays Q.

⛔ **WHAT "GROUNDED" MEANS, AND THE REPLAY THAT SETTLES IT (mojave, 06:46 and 06:49, against its own instrument):** check_all reports
the status stored at each module's last export. It does not replay a stored proof against definitions changed upstream (with the
arm's W3 (i) in the tree it still read 641/641 while two rules were incomplete). The figure that counts is the REPLAY, `status_all`
per module (the arm's `l1/replay-each.sh`). At ec912bd80, whose `theories/` is byte-identical to be5312958 (`git diff --stat` empty):
**672/672 stored proofs replay complete, 28 modules, 0 incomplete**. That is 635 in `virl1_*` (= `L1M.interactive` 635, H = Q) and 37
in the partiality theories (31 prims + 6 derived). Read by vir from the arm's log `replay-each-base.log`.

**Is OBJECT-L1 CLOSED on both arms? YES, for every REQUIRED item, under REPLAY, with the limits below.** Read at the object against OBJECT-L1 §§2–7:
step 2 wf + display (`virl1_syntax`, `virl1_klang`) · step 3 the small step, DEFINED (`virl1_step`, 0 prims) · step 4 the substitution
lemma (`subst_lemma`, `subst_lemma2`) · step 5 progress, preservation, safety, determinism · step 6 unfolding, den typed, den sound
against the steps, semantic type soundness · §7 K1–K5 typing, values and traces. Adequacy (6b) is not built on MetaPRL, and L1's close
does not wait on it. **The arm's literal "L1 closed" post (amend-15's W3 trigger) is the arm's to make.** Its 05:5x plan status reads
"nothing owed on L1", and vir asks for the post rather than inferring it.

**Limits, riding with the verdicts:**
- **Uniqueness and weakening are DISCHARGED BY ENCODING, not stated** (0 rules). `tc` is a function, so typing is unique by
  construction. The encoding has no Γ (a binder is a token), so there is nothing to weaken. Lean states and proves both. A reader who
  holds that "required theorem" means a stated rule should count these two as UNMEASURED on MetaPRL, not as free.
- **The substitution lemma carries `tyok`**, a VIR-side well-formedness predicate the arm added at 00:26 (a variable must not sit in a
  type position, a token's type or a prim's operator child). It encodes OBJECT-L1 §2's grammar (types have no variables), which the
  raw `L1Lang` terms do not enforce. It is counted in W1's files, and it is not a framework edit.
- **The small step is a fix-defined total function `l1step`, iterated by `l1iter`/`l1run`**, not an inductive relation. It is defined,
  never primitive, so W7's clause holds. The iteration count in a `l1run{n; k}` trace is a trace length, not fuel in the semantics.
  K2's ¬halts is stated without one.
- **W2's two columns are not the same instrument.** Lean's 3 counts theorems whose statement uses shift/subst/rename/lift/weaken over
  closed-value substitution. MetaPRL's 216 counts rules whose statement APPLIES `subst{` / `bind{` / `bdepth{` / `var{` (amend-11's
  named operators; its "and siblings" was never listed, so this is a lower bound). In a HOAS-over-BTerm encoding most statements
  about terms mention `bind{`, so the count measures how often the logic makes the arm SAY binding, not how many binder theorems a
  human would name. `subst{` alone gives 51, and W2c is falsified on that reading too. The verdict does not depend on the instrument;
  its size does.
- **W1b's pin figure is a TREE figure** (prims in the built reflection dirs and the two integer files), an upper reading of what L1
  rests on. The arm's closure figure for reflection is 23 (Q). On any of these readings MetaPRL > 3, so the verdict holds.
  **The pin as released proves False twice** (M-F6 (2), M-F7 (1)). The comparison therefore reports a framework figure for a release
  that needed two soundness repairs before it could certify anything. The repairs are listed, never folded into the figure.
- **W6b and W3b are not measured here.** The adm list above is quoted from the arm's posts. W3 (the extension test) waits on both arms'
  "L1 closed" posts (amend-15).
