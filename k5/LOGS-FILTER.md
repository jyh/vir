# k5/logs: the replayed-warning filter (STATUS-vir 299; the helm's ruling (A), 2026-11-12 15:29, term 2)

**From which build on:** every k5 log from **k5p-121** onward, including probes and audits named after it. Logs up to and including
k5p-120 (a run stopped by its owner while queued, before it built anything) are byte-faithful, raw saltbuild output, and are never
re-filtered. **k5p-121 is EMPTY:** the first filtered wrapper had a defect (`noclobber` refused its own redirect onto the temp file),
so saltbuild never ran. It is kept as the record of that wrapper run and counts 0 EXIT lines. The fixed wrapper (`>|`) was then
checked on a stub saltbuild that replays k5p-117: rc 1 passed through, the error and EXIT lines identical, no temp file left.
The first filtered build is k5p-122.

**What it drops:** lake re-prints the warnings of every CACHED module it replays (`⚠ [i/n] Replayed <Module>`). In a k5 build that
was about 5,900 linter warnings from L1/L2/compiler/DEFLATE files, which made each log ~14.8 MB (k5p-114…k5p-119). For each such
block, the header line is kept and the block's body becomes ONE line:
`[replay_filter: dropped N lines (B bytes) sha256/16=<hex>]`, the hash of exactly the dropped bytes.

**What it never drops:** any line outside a Replayed block (the modules this build compiled, their warnings and errors, `saltqueue:`
lines, the `saltbuild EXIT=` line), and any line INSIDE a Replayed block that contains `error` in any case. A build is still judged
only by its `saltbuild EXIT=N` line, which the filter copies byte for byte.

**Why:** the dropped text is the old output of modules this build did not compile. It is reproducible by rebuilding at the same sha,
and it is not what this run did. C6 counts EXIT lines, which are untouched.

**How:** `logged-build.sh` runs saltbuild into a raw temp file outside the tree, then `tools/replay_filter.py RAW -` writes the log.
If the filter fails, the raw log is kept whole.

**Checked before first use** (k5p-118 and k5p-117 as inputs, 2026-11-12):
- 14,819,159 → 5,285 bytes;
- `saltbuild EXIT=` lines 1 → 1, and the error and EXIT lines of the failed build k5p-117 are byte-identical before and after;
- a planted `error:` line inside a Replayed block is KEPT;
- one block's printed hash recomputes from the raw bytes.
