# STAGE: the S3 bridge, vir's half (STATUS-vir 286; compiler/DECLARATIONS-S3-bridge.md, written before any file here)

Built 2026-11-12 by the 67th vir head. Every Lean run goes through `bridge/logged-build.sh` (saltbuild, one log per run). Each build
is judged by its `saltbuild EXIT=` line.

## What is proved (VIRBridge/Mem.lean, against x86lean `X86/Memory.lean` at 5f2231f)
- `Rep wm m S`: every live cell address reads its word as the 8 bytes `readN a 8` (B-2). `Apart`, `Sep` (B-3's premise).
- `writeN_frame` (bytes outside a store's span are kept), `writeN_in` (inside, byte k of the value), `readN_bytes` (a read of n
  bytes is the value's low 8n bits, bit by bit).
- **B-3 (1) `readN_writeN`**: the round trip. **(2) `readN_writeN_apart`**: a store whose span does not meet the cell's leaves
  it unchanged. **(3) `Rep.store`**: a store keeps `Rep` when distinct live cells are apart.
- **B-4 `sep_of_layout`**: `Sep (Live σ lay)` ONCE from S2's `Layout` premise (`fits`, `disj`). This is no per-program lemma
  (K6). `cell_bytes`: with S2's `MemRel`, a live cell's 8 bytes hold its int as a word.
- Through x86lean's interface only: `read_write_same`, `read_write_ne`, `readN_congr`, and `readN`/`writeN` as defined. No
  lemma unfolds `Mem.bytes`, which is the seam x86lean's file names.

## Evidence
- Builds br-001 (the project: x86lean by git at 5f2231f, compiler by path, packages APFS-cloned, manifest by edit), br-002 and
  br-003 failed (lemma names, a rewrite), br-004 and br-005 green.
- Audit br-audit-002: 8 rows, every one within propext · Classical.choice · Quot.sound. `bv_omega` adds no axiom.
  br-audit-001 is the same audit before B-4. Control br-audit-control-001 shows `sorryAx`.
- Failed builds print the lean invocation with local paths. Those lines are written in the `~/fleet/vir` form that master's logs
  carry, before the commit. The private-paths gate passed over the commit range; it failed on the `/Users` form in deflate/'s
  logs, which is the control.

## Limits, declared
- No mutant has been run against the bridge lemmas.
- The initial memory's `Rep` is not built: the bridge says how a `Rep` survives a store, not how a caller's byte memory starts
  as one. That is S3's driver theorem's premise, with C3.
- S3 itself (word code → x86lean `Program`) waits on paris's C3 library (STATUS-vir 282).
