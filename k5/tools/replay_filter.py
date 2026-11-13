#!/usr/bin/env python3
"""Drop the REPLAYED-dependency warning bodies from one saltbuild log (k5/LOGS-FILTER.md declares it; STATUS-vir 299).

usage: replay_filter.py RAW OUT   (OUT '-' = stdout)
A block opens at a line `⚠ [i/n] Replayed <Module>` (lake re-printing a CACHED module's old warnings) and runs to the line before the
next `✔ [`, `⚠ [`, `✖ [`, `saltbuild ` or `saltqueue:` line, or EOF. The header line is KEPT. The block's body is replaced by ONE line
  `[replay_filter: dropped N lines (B bytes) sha256/16=<hex>]`
with the hash of the dropped bytes exactly. EXCEPT: any body line containing `error` (any case) is kept verbatim, in order, so a
filter can never hide an error. Every line outside a Replayed block is copied byte for byte. Exit 2 if OUT exists (noclobber).
"""
import hashlib, os, re, sys
OPEN = re.compile(rb"^\xe2\x9a\xa0 \[\d+/\d+\] Replayed ")          # '⚠ [i/n] Replayed '
CLOSE = re.compile(rb"^(\xe2\x9c\x94 \[|\xe2\x9a\xa0 \[|\xe2\x9c\x96 \[|saltbuild |saltqueue:)")  # ✔ [ · ⚠ [ · ✖ [
def filt(raw: bytes) -> bytes:
    out, body, inblk = [], [], False
    def flush():
        if body:
            dropped = b"".join(l for l in body if b"error" not in l.lower())
            kept = [l for l in body if b"error" in l.lower()]
            n = sum(1 for l in body if b"error" not in l.lower())
            out.append(b"[replay_filter: dropped %d lines (%d bytes) sha256/16=%s]\n"
                       % (n, len(dropped), hashlib.sha256(dropped).hexdigest()[:16].encode()))
            out.extend(kept)
        body.clear()
    for line in raw.splitlines(keepends=True):
        if inblk and CLOSE.match(line):
            flush(); inblk = False
        if inblk:
            body.append(line); continue
        out.append(line)
        if OPEN.match(line):
            inblk = True
    if inblk:
        flush()
    return b"".join(out)
if __name__ == "__main__":
    src, dst = sys.argv[1], sys.argv[2]
    if dst == "-":
        sys.stdout.buffer.write(filt(open(src, "rb").read())); sys.exit(0)
    if os.path.exists(dst):
        print(f"replay_filter: REFUSED, {dst} exists", file=sys.stderr); sys.exit(2)
    data = filt(open(src, "rb").read())
    with open(dst, "xb") as f:
        f.write(data)
