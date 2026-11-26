# OBJECT-NOCHECK-ENTRY — the eager entry check for an external caller without a proof (OBJECT-NOCHECK fork N3, policy 2)

**Pinned 2026-11-25 by the 90th vir head, BEFORE any file of its route.** Fork N3 (a) of `OBJECT-NOCHECK.md` deferred policy 2
until NC-S landed; NC-S landed at ddfe9e6 (RESULTS-15). The policy is his (11-15 walkthrough, `REVIEW-O95-2026-11.md` :114–121;
ruled with option (iv) at the 11-25 council). Predictions: `predictions/PREDICTIONS-amend-27.md`, in this file's commit.
**Nothing in this file is edited after its pin.** An erratum goes in `errata/ERRATA-NOCHECK-ENTRY.md`.

## 0. What exists (read at 8fc40b8)
- `S3.compile_x86_proved` needs NC-P′ (`NoFaultP vs e σ`) as a premise. An L2 `Triple {P} e {Q}` supplies it at every state with
  `P σ`. A caller WITHOUT a proof has no `P σ`.
- `S3.driver_x86`/`drv_iter` (`s3/S3/Driver3.lean`) already compose a machine-level call into compiled code with a test of its exit
  (`head_call`, `after_done`, `after_exit`).
- An L2 `Assn` is a `Prop` on stores. Some of a precondition is SHAPE (the store is a well-formed region of a size, cells placed), which
  every compile_x86 caller already supplies through `Layout`/`MemRel`/`DriverCall`. Some is CONTENT (cell values in a range: the
  router's R4 needs `0 ≤ SvA f p < 4` and `0 ≤ TvA f p < 4`), which no caller premise covers.

## 1. The target
- **NE-D, the decider.** For a proved program e with triple `{P} e {Q}`, a DECIDER `d`: an L2 program over e's arguments that returns a
  `bool`, READ-ONLY (no `store` in its word code, checked by a Bool predicate), with a SOUNDNESS premise: if d returns `true` from σ
  (under the shape premises), then `P σ`.
- **NE-C, the entry code.** Call d's code (compiled by the CHECKED `lower3`, because d itself runs on unproved input); on `false`, or on
  d reaching FAULT or OVF, jump to the FAULT exit; on `true`, call e's code compiled by `lower3u`.
- **NE-T, the theorem `compile_entry`.** For every caller state meeting compile_x86's SHAPE premises only: the machine EITHER ends at
  FAULT with every live cell unchanged (no effect: d is read-only, and e's code was never entered), OR matches e's run exactly as
  `compile_x86_proved` states it. No `P σ` premise, and no `NoFaultP` premise.
- **NE-R, the application.** The router with a decider `dF` (the capability's length is 87, and `SvA`/`TvA` are in [0, 4)), its
  soundness against R4's precondition, and `compile_entry` at F.

## 2. The forks (each with its recommendation; each proceeds on it under the 08/31 law)
- **EN1 — what form the check takes.** (a) A DECIDER PROGRAM d in L2, compiled by the existing compiler (NE-D). The check is then any
  computable precondition, and its soundness is one lemma per program. (b) A FIXED FRAGMENT emitted inline (`cmp len, n; jl FAULT` per
  capability argument). Cheaper code, but it states only region lengths and cannot state the router's cell-value bounds without loads,
  so it fails on the first program. **Rec (a).**
- **EN2 — how the two calls compose.** (a) A two-call driver built from Driver3's pieces (`head_call`, `after_done`, `after_exit`).
  (b) A new composition lemma from scratch. **Rec (a)**: the pieces exist and name no program.
- **EN3 — what "before any effect" means.** (a) Every LIVE cell unchanged at the FAULT exit, derived from d's read-only predicate.
  (b) The whole machine memory unchanged. That is false, because the driver writes its own stack and BUF. **Rec (a).**

## 3. Price (an ESTIMATE)
By analogy with Driver3 (driver_x86 and its pieces, one file of ~350 lines) and corrected by NOCHECK's own record (NC7: 12 builds
against an estimated 40–80, about 3–6× high): **15–40 builds, 1–2 vir heads**, for NE-D's predicate, NE-T and NE-R together.
**CHECKPOINT** at 40 builds without `compile_entry` at EXIT=0: post the state and the remaining obligation before going on.

## 4. What this does NOT claim
no check of the SHAPE premises (a caller that hands a malformed store is outside compile_x86's theorem today, and stays outside) · no
speed figure · no decider synthesised from a triple (d and its soundness are written per program) · no change to `compile_x86`,
`compile_x86_proved` or `lower3`/`lower3u` (their statements stay byte-identical).
**What would show this object wrong:** `compile_entry` stated after its proof · a `P σ` or `NoFaultP` premise in it · a store in a
decider accepted · a FAULT exit after which a live cell differs · a router lemma beyond `dF`'s soundness.
