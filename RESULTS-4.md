# RESULTS-4 — the B′ re-score (PREDICTIONS-amend-10): programs 1–3 on the Lean side (8th vir head, 2026-11-01)

amend-10 was pinned at 14efadc (14:59:45 PST), before any Lean B′ file existed. Everything below was built after it.
H marks a figure read from an artifact in this tree. Q marks a quote from the MetaPRL arm's record (mojave,
`theories/vir/vir-arm-tools/COUNTS-metaprl-bprime.md` on branch `mojave/vir-arm-bprime`, tools bae7fbe). This
harness had not extracted it when this file was written; addendum 2 (2026-11-02) turns the quotes it can read into H.

## The Lean B′ mirror, program 1 (`lean/VIRB/BPrime.lean`)
- `Carrier`: one structure with 8 fields (`State`, `VErr`, `wire_u32`, `can_access`, `has_tokens`, `dec_tokens`, two
  codes). `vlen`, `advance` and `read_u32` are defined over the unindexed slice `(List Int) × Int`. The I1 slice and read
  laws are theorems (`slice_law`, `read_law`).
- `router_fusion_bp` (I4 under B′) takes NO typing premise. Its chain is `VIR.router_fusion`'s rewrite steps, plus one
  `rfl` for const_fold (12 + 12 = 24 on Int literals), which the indexed arm discharged inside `slice_fuse`'s premises.
- Builds through saltbuild: `VIRB/logs/build-028.log` reads `saltbuild EXIT=0` (whole project, both libraries).
  `audit-bp-001` reads `saltbuild EXIT=0`.
- Axioms (H, audit-bp-001): `router_fusion_bp` → [propext, Quot.sound] · `slice_law` → [propext, Quot.sound] ·
  `read_law` → [propext]. The control `control_sorry_bp` → [sorryAx].
- Mutant (H, build-027): F's payload offset 24 → 20 gives `saltbuild EXIT=1` at the chain's last step. Restored, the
  build reads EXIT=0 (build-028).
- The B′ library is SEPARATE (`VIRB`, its own logs dir), so every whole-tree row of `VIR/` is unchanged.
  `harness/reproduce.sh` reads rc 0, 10/10 SAME, after the addition.

## Verdicts (Lean side predicted; MetaPRL side EXPLORATORY by amend-10)
| pred | claim | Lean B′ | MetaPRL B′ | verdict |
|---|---|---|---|---|
| B1 | C1heq = 0 on the unindexed B′ slice | **0** (H, `≍`/HEq/heq_of_eq over audit-bp-001) | — | **HOLDS** |
| B2 | C4vir equal for program 1's module | **8** Carrier fields (H, the `#print` of `Carrier`) | **8** `prim`s in vir.ml at 9ed59847c (H, `grep -cE '^\s*prim(_rw)?\s'`) | **HOLDS** |
| B3 | C4 = 0 on both arms | **0** beyond {propext, Quot.sound} (H) | 0 (Q: "C4 … is unchanged: 0") | **HOLDS** (Lean H, MetaPRL Q) |
| B4 | the A.2 parser reproduces the hand-written deep terms | **4/4** `rfl` (tc_U · tc_F · tc_U2 · tc_F2; build-037 EXIT=0); F's read-offset mutant RED (build-036); I2 spec-offset mutant RED at tc_U only (build-038) | MetaPRL's own check: 10/10 (Q) | **HOLDS** |
| B1 (p2, p3) | the same reading on programs 2 and 3 (amend-10 predicts program 1 only, so this is EXPLORATORY) | router2_fusion_bp HEq **0** · route_acl_safe_bp HEq **0** (H, audit-bp-003) | — | no prediction |
| B2 (p2) | C4vir with `take` and the bad-payload code | **10** (Carrier2 = Carrier's 8 + 2) | **10** (Q: mojave's prim list) | equal (EXPLORATORY) |

No-direction figures, reported beside B. Lean B′ C1-class tokens over the audit's terms: 33. These are the `Eq.mpr` that
`rw` leaves, the same role amend-5 separates from transport, and none is HEq. Lean B′ C6 = 4 saltbuild invocations to the
first green. ⚠️ Three red runs OVERWROTE one log (build-025), so only the green run's log survives. The count is the
author's, not an artifact's.

MetaPRL B′ (Q): router_fuse 5 → 1 rule box, 516 → 290 primitive steps. mojave's own limit rides with it: the drop is
largely work MOVED into 37 shared wf rules, not work removed.

## Programs 2 and 3 (added the same shift; amend-10 predicts program 1 only, so these rows are exploratory)
- `lean/VIRB/BPrime2.lean`: `Carrier2 extends Carrier` with `take` (a CPS field) and `errBadPayload`. `router2_fusion_bp`
  runs program 1's rewrite steps, then ONE aux rule, `aux_advance_guard_vlen` (the I1 slice law read under the advance
  binder), then `slice_fuse` and one Int arithmetic step (`12 + (off - 12) = off`). NO step needs an enclosing guard.
  This is amend-7 R1's finding again, now on the B′ carrier: on Int the rewrite stays and its context dependence goes.
  Build: build-031 EXIT=0. Mutant (F2's bound `≤` → `<`): build-030 EXIT=1.
- `lean/VIRB/BPrime3.lean`: `ValidFrame` is the subtype of the wire, mirroring `validframe`, MetaPRL's set type over
  `wirebuf`. `route_acl_safe_bp` takes the frame, the state and the routed premise, with no typing premise.
  Build: build-032 EXIT=0, on its first invocation. Mutant (the conclusion's principal → the topic, mojave's mutant):
  build-033 EXIT=1. The whole project rebuilds at build-034 EXIT=0.
- Axioms (H, audit-bp-003): router2_fusion_bp and aux_advance_guard_vlen → [propext, Quot.sound] · route_acl_safe_bp →
  [propext] · control sorryAx.
- No direction: route_acl_safe_bp's term carries 74 tokens of program 3's coercion class (`.val`/`.property`/`↑`; T1's
  L-IDX figure was C1coe 54). C6: program 2, 3 invocations to first green (⚠️ build-029 was overwritten twice, so the
  count is the author's) · program 3, 1.

## B4, the A.2 transcription check (`harness/transcribe_lean.py` → `lean/VIRB/Transcribe.lean`, generated, never hand-edited)
The translator reads I2 and I3 (router-inputs.md), A.3's F (object/appendix-A.tex, LaTeX escapes undone by a DECLARED
table that refuses an unknown escape), and J2, J3 and J4 (program2-inputs.md), each AS WRITTEN. It parses A.2's surface
syntax and expands every spec call into its continuation. It emits one `theorem tc_X : <parsed> = <hand-written deep
term> := rfl` per term, against `VIR.Deep.U/F` and `VIR.Deep2.U2/F2`. A first build gave 4/4 green.
Mutants: F's sender read 4 → 8 reds tc_F, while U, U2 and F2 stay green. I2's topic read 8 → 12 reds tc_U ALONE,
because a spec reaches U only through the expansion, and J2's own parse_header2 is untouched. After each mutant, the true
file is regenerated cmp-identical.
LIMITS, beside the verdict: equality is up to `rfl` (definitional unfolding), not characters. The forms, conditions and
codes table is written once in the translator, by hand. Spec bodies are checked only through their expansion into U and
U2. F2 is an INPUT (J4), not the object.

## Harness rows (added after the verdicts above, from the same artifacts)
`python3 harness/count.py --arm leanbp lean/VIRB` reads the newest `audit-bp-*.log` and gives
`lean/VIRB/out/counts-bp.tsv`, which `harness/reproduce.sh` checks (11 files, rc 0). The rows are per theorem:
BP1/BP2/BP3 .C1heq 0/0/0 · .C1coe 0/0/74 · .C4 0/0/0 · BP1.C4vir 8 · BP2.C4vir 10 · B.control 1. `B.C6` = 18 is the
saltbuild runs LOGGED under lean/VIRB/logs (mutants and audits included; overwritten runs are not counted, as its
`.scope` row says). Selftest ARM18 plants an HEq, an extra axiom and a missing control and reads all three, and it goes
red when `≍` is dropped from its class.

Addendum 1 (2026-11-02, after every B′ proof; no figure above moves): later B′ runs go through
`lean/VIRB/logged-build.sh NAME ...`, which refuses a log name already used (rc 3) before saltbuild runs, so no run
can be written over and lost to `B.C6`. Selftest ARM19 drives it with a stub saltbuild and goes red when the refusal
is removed. The 18 logs already in lean/VIRB/logs are unchanged.

Addendum 2 (2026-11-02, after every B′ proof on both arms; row 64): the MetaPRL B′ arm is public at jyh/metaprl
`mojave/vir-arm` = 93ff6b7c0 (a fast-forward of 81e0317b0, so every B row stays where it was). `count.py --arm metaprlbp`
reads it, giving `harness/metaprl-counts-bprime.tsv`, derived from a fresh GitHub clone. `reproduce.sh` pins it (12 files,
rc 0). Quotes that are now harness rows:
- B2: `BM1.prims` **8** (H, at the public sha; the cell above read the pre-rewrite sha). B2 (p2): `BM1.prims` +
  `BM2.prims` = 8 + 2 = **10** (H; was Q). `BM.prims` = 10 is mojave's "Prims: 10".
- Rule boxes: the scored theorem's refines are **1 · 12 · 19** for programs 1–3 (`BMn.refines.thm`). mojave's B′
  rule-box column, which comes from `status_all`, is the same 1 · 12 · 19. Two sources agree, so the column is H.
- All three replays end `err=0 rc=0` (`BMn.replay` 1).
- New B′ rows, no direction, all EXPLORATORY: C1 casts 0 · 0 · 0. Generated children over the session (wf / equality /
  conditional) are 0/0/0 · 0/2/6 · 5/0/1, and inside the theorem 0 · 8 · 6. C5chain tokens are 85 · 206 · 98.
Still Q: primitive steps (516 → 290 and the rest; `status_all` output, which no file records), B3's MetaPRL C4 = 0
(mojave's reading that the 10 prims are I5 operator typings, not extra axioms), and B4's MetaPRL 10/10. The extractor
keeps a theorem's scope across relative `cd`s, which program 3 uses. Selftest ARM20 plants that shape and goes red when
a relative cd ends the scope (4 → 2).

## Limits
- Programs 2–3 are exploratory under amend-10, which predicts program 1 only.
- B2 compares program 1's module only (vir.ml). `take` and `ERR_BAD_PAYLOAD` arrive with program 2.
- ~~This harness does not yet extract the MetaPRL B′ runs~~ (true until addendum 2, 2026-11-02; it now does, at
  93ff6b7c0). Primitive steps and B3/B4's MetaPRL cells remain Q.
