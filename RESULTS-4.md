# RESULTS-4 — the B′ re-score (PREDICTIONS-amend-10), first act: program 1 (8th vir head, 2026-11-01)

amend-10 was pinned at 14efadc (14:59:45 PST), before any Lean B′ file existed. Everything below was built after it.
H marks a figure read from an artifact in this tree. Q marks a quote from the MetaPRL arm's record (mojave,
`theories/vir/vir-arm-tools/COUNTS-metaprl-bprime.md` on branch `mojave/vir-arm-bprime`, tools bae7fbe), which this
harness has not yet extracted.

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
| B4 | the A.2 parser reproduces the hand-written deep terms | not built | MetaPRL's own check: 10/10 (Q) | **OWED** |

No-direction figures, reported beside B. Lean B′ C1-class tokens over the audit's terms: 33. These are the `Eq.mpr` that
`rw` leaves, the same role amend-5 separates from transport, and none is HEq. Lean B′ C6 = 4 saltbuild invocations to the
first green. ⚠️ Three red runs OVERWROTE one log (build-025), so only the green run's log survives. The count is the
author's, not an artifact's.

MetaPRL B′ (Q): router_fuse 5 → 1 rule box, 516 → 290 primitive steps. mojave's own limit rides with it: the drop is
largely work MOVED into 37 shared wf rules, not work removed.

## Limits
- Program 1 only on the Lean side. Programs 2 and 3, and the A.2 parser (B4), are owed.
- B2 compares program 1's module only (vir.ml). `take` and `ERR_BAD_PAYLOAD` arrive with program 2.
- This harness does not yet extract the MetaPRL B′ runs (`bp-vir*.mp`, `runs-bp-vir*.txt`), so MetaPRL B′ C1–C3 and C5
  are not read here.
