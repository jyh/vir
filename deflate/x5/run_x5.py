#!/usr/bin/env python3
"""run_x5.py — the X5 comparison (DECLARATIONS-DEFLATE.md, Addendum A2).
usage: run_x5.py ZINFLATE X5EXE WORKDIR OUT.tsv
  ZINFLATE  the oracle driver built from x5/zinflate.c against the pinned zlib
  X5EXE     the arm's driver (lake exe x5)
  WORKDIR   scratch for outputs
Population: corpus/data/MANIFEST.tsv rows of class i/ii/iii (iii-flip-*/iii-trunc-* read from data/mutations/, re-derived by
gen_corpus.py --check, which this script runs first and requires rc 0) + corpus/data/ADDENDUM-A1.tsv. Every input's sha256 is
checked against its manifest row before it is run. Writes OUT.tsv (one row per input) and prints the summary. rc 0 iff the run
COMPLETED (agreement is reported, never turned into an rc), rc 1 on any harness failure.
"""
import hashlib, os, subprocess, sys
zinf, x5exe, work, outtsv = sys.argv[1:5]
here = os.path.dirname(os.path.abspath(__file__)); data = os.path.join(here, "..", "corpus", "data")
gc = subprocess.run([sys.executable, os.path.join(here, "..", "corpus", "gen_corpus.py"), "--check", data], capture_output=True, text=True)
if gc.returncode != 0: print("gen_corpus --check FAILED:", gc.stdout, gc.stderr); sys.exit(1)
ga = subprocess.run([sys.executable, os.path.join(here, "..", "corpus", "gen_addendum.py"), "--check", data], capture_output=True, text=True)
if ga.returncode != 0: print("gen_addendum --check FAILED:", ga.stdout, ga.stderr); sys.exit(1)
rows = [l.rstrip("\n").split("\t") for l in open(os.path.join(data, "MANIFEST.tsv"))][1:]
rows += [l.rstrip("\n").split("\t") for l in open(os.path.join(data, "ADDENDUM-A1.tsv"))][1:]
pop = [r for r in rows if len(r) == 5 and r[1] in ("i", "ii", "iii")]
paths = {}
for name, cls, n, sha, note in pop:
    p = os.path.join(data, "mutations" if name.startswith(("iii-flip-", "iii-trunc-")) else "", name + ".bin")
    b = open(p, "rb").read()
    if hashlib.sha256(b).hexdigest() != sha: print("INPUT HASH MISMATCH", name); sys.exit(1)
    paths[name] = p
os.makedirs(os.path.join(work, "zlib"), exist_ok=True); os.makedirs(os.path.join(work, "arm"), exist_ok=True)
zl = {}
for name in paths:
    r = subprocess.run([zinf, paths[name], os.path.join(work, "zlib", name + ".bin")], capture_output=True, text=True)
    if r.returncode != 0 or not r.stdout.strip(): print("ORACLE FAILED", name, r.stderr); sys.exit(1)
    zl[name] = r.stdout.strip()
r = subprocess.run([x5exe, os.path.join(work, "arm")] + [paths[n] for n in paths], capture_output=True, text=True)
if r.returncode != 0: print("ARM DRIVER FAILED", r.stderr); sys.exit(1)
arm = {}
for line in r.stdout.splitlines():
    base, lit, rep = line.split("\t"); arm[base] = (lit, rep)
if set(arm) != set(paths): print("ARM POPULATION MISMATCH", len(arm), len(paths)); sys.exit(1)
def rd(p): return open(p, "rb").read() if os.path.exists(p) else None
def compare(name, verdict, armfile, control=False):
    z = zl[name]; zacc = z.startswith("ACCEPT"); aacc = verdict.startswith("ACCEPT")
    if zacc != aacc: return "VERDICT"
    if zacc:
        zb = rd(os.path.join(work, "zlib", name + ".bin")); ab = rd(armfile)
        if control: zb = bytes([zb[0] ^ 1]) + zb[1:] if zb else b"\x01"
        if zb != ab: return "BYTES"
    return "AGREE"
out = ["name\tclass\tzlib\tlit\tlit_cmp\trep\trep_cmp"]; tally = {"lit": {}, "rep": {}}; reasons = {}
cls = {r[0]: r[1] for r in pop}
for name in paths:
    lit, rep = arm[name]
    cl = compare(name, lit, os.path.join(work, "arm", name + ".lit.bin"))
    cr = compare(name, rep, os.path.join(work, "arm", name + ".rep.bin"))
    tally["lit"][cl] = tally["lit"].get(cl, 0) + 1; tally["rep"][cr] = tally["rep"].get(cr, 0) + 1
    if zl[name].startswith("REJECT") and rep.startswith("REJECT"):
        k = (" ".join(zl[name].split()[2:]), rep[7:]); reasons[k] = reasons.get(k, 0) + 1
    out.append("\t".join([name, cls[name], zl[name], lit, cl, rep, cr]))
open(outtsv, "w").write("\n".join(out) + "\n")
# positive control: alter one oracle output in memory (the first double-ACCEPT under `inflate`) -> exactly one more disagreement
ctl = next(n for n in paths if zl[n].startswith("ACCEPT") and arm[n][1].startswith("ACCEPT"))
ctl_res = compare(ctl, arm[ctl][1], os.path.join(work, "arm", ctl + ".rep.bin"), control=True)
print(f"X5 population {len(paths)}; oracle {sum(v.startswith('ACCEPT') for v in zl.values())} ACCEPT / {sum(v.startswith('REJECT') for v in zl.values())} REJECT")
print("inflateLit (S literal, D1):", dict(sorted(tally['lit'].items())))
print("inflate (E1 repaired):     ", dict(sorted(tally['rep'].items())))
print(f"control: {ctl} with one oracle byte altered -> {ctl_res} (must be BYTES)")
print("reasons (zlib msg | inflate reason) on double REJECT:")
for (zm, am), c in sorted(reasons.items(), key=lambda x: -x[1]): print(f"  {c:4d}  {zm} | {am}")
sys.exit(0 if ctl_res == "BYTES" else 1)
