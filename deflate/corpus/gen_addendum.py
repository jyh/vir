#!/usr/bin/env python3
"""gen_addendum.py — ADDENDUM A1 to the pinned X5 corpus (deflate/DECLARATIONS-DEFLATE.md §Addendum A1), declared before X5 runs.

The pinned corpus (gen_corpus.py, digest cc18ad46…, 313 files) is NOT touched. Its crafted iii-repeat-no-first never reaches
S6's "repeat with no first length": its code-length code is {0: 1, 16: 1}, and S4's canonical assignment gives symbol 0 the code
0, so the stream's first 0-bit decodes to length 0 (STAGE-DEFLATE finding 2). This file adds ONE stream that does reach it: the
same header, then the code 1 (symbol 16) as the first code-length symbol.

Usage: gen_addendum.py OUTDIR          -> writes OUTDIR/<name>.bin and OUTDIR/ADDENDUM-A1.tsv (name, class, bytes, sha256, note)
       gen_addendum.py --check OUTDIR  -> re-derives every addendum stream and verifies the stored files and the tsv (rc 0/1)
"""
import hashlib, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_corpus import BW, dynamic_header

def streams():
    s = {}
    bw = BW(); dynamic_header(bw, 257, 1, 4, {16: 1, 0: 1}); bw.code(1, 1); bw.put(0, 2)
    s["iiia1-repeat-no-first"] = (bw.bytes() + bytes(4), "REJECT repeat with no first length")
    return s

def rows():
    return [(n, "iii", len(d), hashlib.sha256(d).hexdigest(), note) for n, (d, note) in streams().items()]

def tsv_text():
    return "name\tclass\tbytes\tsha256\tnote\n" + "".join("\t".join(str(x) for x in r) + "\n" for r in rows())

if __name__ == "__main__":
    if sys.argv[1] == "--check":
        out = sys.argv[2]; bad = 0
        for n, (d, _) in streams().items():
            p = os.path.join(out, n + ".bin")
            if not os.path.exists(p) or open(p, "rb").read() != d: print("MISMATCH", n); bad += 1
        if open(os.path.join(out, "ADDENDUM-A1.tsv")).read() != tsv_text(): print("MISMATCH ADDENDUM-A1.tsv"); bad += 1
        print(f"addendum check: {len(streams())} files, {bad} mismatches"); sys.exit(1 if bad else 0)
    out = sys.argv[1]
    for n, (d, _) in streams().items():
        with open(os.path.join(out, n + ".bin"), "wb") as f: f.write(d)
    with open(os.path.join(out, "ADDENDUM-A1.tsv"), "w") as f: f.write(tsv_text())
    print(f"addendum A1: {len(streams())} file(s), tsv digest {hashlib.sha256(tsv_text().encode()).hexdigest()}")
