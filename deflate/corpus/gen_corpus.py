#!/usr/bin/env python3
"""O95 OBJECT-DEFLATE, fork X5 (a): the corpus, generated DETERMINISTICALLY and pinned by hash (deflate/DECLARATIONS-DEFLATE.md).

Classes:
  i   hand-built minimal streams (RFC 1951 contains no worked byte streams, so class (i) is built here, one per block type and
      per end case, each with the expected verdict written beside it as the AUTHOR'S READING of Appendix S, not as an oracle)
  ii  a fixed seed text compressed by this Python's zlib (raw, wbits -15) at levels 0-9 x strategies
      default/filtered/huffman_only/rle/fixed  (50 streams)
  iii mutations of (ii) and (i): bit flips and truncations at positions from a fixed LCG, plus crafted malformed streams
      (distance too far back, over-subscribed and incomplete code sets, HLIT > 286, a repeat code with no first length,
      BTYPE 11, a bad stored-length complement)

Usage: gen_corpus.py OUTDIR   -> writes OUTDIR/<name>.bin, OUTDIR/mutations/<name>.bin (NOT committed: derived from the stored
       class (ii) files) and OUTDIR/MANIFEST.tsv (name, class, bytes, sha256, note) pinning EVERY file
       gen_corpus.py --check OUTDIR  -> re-derives the mutations from the stored files and verifies all 313 hashes (rc 0/1)
The streams in (ii) depend on the COMPRESSOR's version; the manifest records it, and the committed .bin files are the corpus.
"""
import hashlib, os, sys, zlib

class LCG:
    def __init__(self, seed): self.s = seed & 0xFFFFFFFF
    def next(self):
        self.s = (1103515245 * self.s + 12345) & 0x7FFFFFFF
        return self.s

def seed_text():
    # 40,000 bytes: prose lines with long-distance repeats (> 32 KiB apart), runs, and LCG noise.
    words = b"the quick brown fox jumps over the lazy dog deflate inflate huffman literal length distance window".split()
    r = LCG(1951); out = bytearray()
    while len(out) < 18000:
        out += b" ".join(words[r.next() % len(words)] for _ in range(8)) + b"\n"
    out += bytes([65]) * 300                                   # a run (RLE, overlapping copy)
    out += bytes(r.next() & 0xFF for _ in range(3000))          # incompressible noise
    head = bytes(out[:4000])
    while len(out) < 36000:
        out += b" ".join(words[r.next() % len(words)] for _ in range(6)) + b"\n"
    out += head                                                 # a repeat ~36 KB back: beyond the window, must be re-literalled
    out += bytes(out[-30000:-29000])                            # a repeat ~30 KB back: inside the window
    return bytes(out[:40000])

class BW:  # LSB-first bit writer (RFC 1951 3.1.1)
    def __init__(self): self.bits = []
    def put(self, v, n):                                        # data field, least-significant bit first
        for i in range(n): self.bits.append((v >> i) & 1)
    def code(self, c, n):                                       # Huffman code, most-significant bit first
        for i in reversed(range(n)): self.bits.append((c >> i) & 1)
    def bytes(self):
        b = bytearray((len(self.bits) + 7) // 8)
        for i, x in enumerate(self.bits): b[i // 8] |= x << (i % 8)
        return bytes(b)

def fixed_lit(bw, sym):
    if sym < 144: bw.code(0x30 + sym, 8)
    elif sym < 256: bw.code(0x190 + sym - 144, 9)
    elif sym < 280: bw.code(sym - 256, 7)
    else: bw.code(0xC0 + sym - 280, 8)

def class_i():
    s = {}
    s["i-stored-empty-final"] = (bytes([0x01, 0x00, 0x00, 0xFF, 0xFF]), "ACCEPT empty")
    bw = BW(); bw.put(1, 1); bw.put(1, 2); fixed_lit(bw, 256)
    s["i-fixed-empty-final"] = (bw.bytes(), "ACCEPT empty")
    bw = BW(); bw.put(1, 1); bw.put(1, 2); fixed_lit(bw, ord("a")); fixed_lit(bw, 256)
    s["i-fixed-one-literal"] = (bw.bytes(), "ACCEPT a")
    # 'a' then length 3 distance 1: "aaaa" (an overlapping copy, 3.2.3)
    bw = BW(); bw.put(1, 1); bw.put(1, 2); fixed_lit(bw, ord("a")); fixed_lit(bw, 257); bw.code(0, 5); fixed_lit(bw, 256)
    s["i-fixed-overlap-copy"] = (bw.bytes(), "ACCEPT aaaa")
    bw = BW(); bw.put(0, 1); bw.put(0, 2); bw.put(0, 5)   # non-final stored, aligned
    data = bw.bytes() + bytes([2, 0, 0xFD, 0xFF]) + b"hi"
    s["i-two-blocks"] = (data + bytes([0x01, 0x00, 0x00, 0xFF, 0xFF]), "ACCEPT hi")
    return s

def dynamic_header(bw, hlit, hdist, hclen, cl_lens):
    bw.put(1, 1); bw.put(2, 2); bw.put(hlit - 257, 5); bw.put(hdist - 1, 5); bw.put(hclen - 4, 4)
    order = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]
    for i in range(hclen): bw.put(cl_lens.get(order[i], 0), 3)

def crafted():
    s = {}
    s["iii-btype-11"] = (bytes([0x07]), "REJECT invalid block type")
    s["iii-stored-bad-nlen"] = (bytes([0x01, 0x02, 0x00, 0x00, 0x00, 0x41, 0x41]), "REJECT invalid stored block lengths")
    bw = BW(); bw.put(1, 1); bw.put(1, 2); fixed_lit(bw, ord("a")); fixed_lit(bw, 257); bw.code(1, 5); fixed_lit(bw, 256)
    s["iii-distance-too-far"] = (bw.bytes(), "REJECT distance too far back (dist 2 > 1 byte produced)")
    bw = BW(); dynamic_header(bw, 287, 1, 4, {16: 1, 17: 1, 18: 1, 0: 1})
    s["iii-hlit-too-many"] = (bw.bytes(), "REJECT too many length or distance symbols")
    bw = BW(); dynamic_header(bw, 257, 1, 4, {16: 1, 17: 1, 18: 1, 0: 1})   # four codes of length 1: over-subscribed
    s["iii-cl-oversubscribed"] = (bw.bytes() + bytes(4), "REJECT over-subscribed (code-length code)")
    bw = BW(); dynamic_header(bw, 257, 1, 4, {16: 2, 17: 2, 18: 2})        # three codes of length 2: incomplete
    s["iii-cl-incomplete"] = (bw.bytes() + bytes(4), "REJECT incomplete (code-length code, no exception)")
    # code-length code: symbols 16 and 0 at length 1 (complete). First symbol read is 16 (code 0): a repeat with no first length.
    bw = BW(); dynamic_header(bw, 257, 1, 4, {16: 1, 0: 1}); bw.code(0, 1); bw.put(0, 2)
    s["iii-repeat-no-first"] = (bw.bytes() + bytes(4), "REJECT repeat with no first length")
    return s

def main(outdir):
    os.makedirs(outdir, exist_ok=True)
    rows = []
    def emit(name, cls, data, note):
        with open(os.path.join(outdir, name + ".bin"), "wb") as f: f.write(data)
        rows.append((name, cls, len(data), hashlib.sha256(data).hexdigest(), note))
    for n, (d, note) in class_i().items(): emit(n, "i", d, note)
    seed = seed_text(); emit("ii-seed-raw", "seed", seed, "the uncompressed seed text (not a stream)")
    strategies = [("default", zlib.Z_DEFAULT_STRATEGY), ("filtered", zlib.Z_FILTERED), ("huffman", zlib.Z_HUFFMAN_ONLY),
                  ("rle", zlib.Z_RLE), ("fixed", zlib.Z_FIXED)]
    streams = []
    for lvl in range(10):
        for sname, st in strategies:
            c = zlib.compressobj(lvl, zlib.DEFLATED, -15, 9, st)
            d = c.compress(seed) + c.flush()
            name = f"ii-l{lvl}-{sname}"; emit(name, "ii", d, "ACCEPT seed"); streams.append((name, d))
    # mutations read the STORED class (ii) files, so they do not depend on the compressor that made them
    mutdir = os.path.join(outdir, "mutations"); os.makedirs(mutdir, exist_ok=True)
    stored = [(n, open(os.path.join(outdir, n + ".bin"), "rb").read()) for n, _ in streams]
    r = LCG(32768)
    def emit_mut(name, data, note):
        with open(os.path.join(mutdir, name + ".bin"), "wb") as f: f.write(data)
        rows.append((name, "iii", len(data), hashlib.sha256(data).hexdigest(), note))
    for k in range(200):                                    # bit flips
        name, d = stored[r.next() % len(stored)]
        pos = r.next() % (len(d) * 8)
        m = bytearray(d); m[pos // 8] ^= 1 << (pos % 8)
        emit_mut(f"iii-flip-{k:03d}", bytes(m), f"flip of {name} at bit {pos}")
    for k in range(50):                                     # truncations
        name, d = stored[r.next() % len(stored)]
        cut = r.next() % len(d)
        emit_mut(f"iii-trunc-{k:03d}", d[:cut], f"{name} truncated to {cut} bytes")
    for n, (d, note) in crafted().items(): emit(n, "iii", d, note)
    with open(os.path.join(outdir, "MANIFEST.tsv"), "w") as f:
        f.write(f"# generator gen_corpus.py; compressor zlib {zlib.ZLIB_RUNTIME_VERSION} (python {sys.version.split()[0]}); "
                f"{len(rows)} files\n")
        f.write("name\tclass\tbytes\tsha256\tnote\n")
        for row in rows: f.write("\t".join(str(x) for x in row) + "\n")
    h = hashlib.sha256()
    for row in rows: h.update(f"{row[0]}\t{row[3]}\n".encode())
    print(f"corpus files={len(rows)} digest={h.hexdigest()}")

def check(outdir):
    rows = [l.rstrip("\n").split("\t") for l in open(os.path.join(outdir, "MANIFEST.tsv")) if not l.startswith(("#", "name\t"))]
    streams = [(r[0], None) for r in rows if r[1] == "ii"]
    mutdir = os.path.join(outdir, "mutations"); os.makedirs(mutdir, exist_ok=True)
    stored = [(n, open(os.path.join(outdir, n + ".bin"), "rb").read()) for n, _ in streams]
    r = LCG(32768); derived = {}
    for k in range(200):
        name, d = stored[r.next() % len(stored)]; pos = r.next() % (len(d) * 8)
        m = bytearray(d); m[pos // 8] ^= 1 << (pos % 8); derived[f"iii-flip-{k:03d}"] = bytes(m)
    for k in range(50):
        name, d = stored[r.next() % len(stored)]; cut = r.next() % len(d); derived[f"iii-trunc-{k:03d}"] = d[:cut]
    bad = 0
    for row in rows:
        name, sha = row[0], row[3]
        data = derived[name] if name in derived else open(os.path.join(outdir, name + ".bin"), "rb").read()
        if name in derived:
            with open(os.path.join(mutdir, name + ".bin"), "wb") as f: f.write(data)
        if hashlib.sha256(data).hexdigest() != sha: print("MISMATCH", name); bad += 1
    print(f"check: {len(rows)} files, {bad} mismatches"); sys.exit(1 if bad or len(rows) != 313 else 0)

if __name__ == "__main__":
    if sys.argv[1] == "--check": check(sys.argv[2])
    else: main(sys.argv[1])
