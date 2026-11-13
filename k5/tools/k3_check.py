#!/usr/bin/env python3
"""K3's whitelist (compiler/DECLARATIONS-S1.md l.46-50) applied to the K3CONST lines of a probe log.

usage: k3_check.py LOG
Per declaration: OK if every constant in its type lies in VIRC.* VIRL1.* VIRL2.* X86.* or Lean core/Std/Mathlib (i.e. is in
no forbidden namespace and names no program); FALSIFIED otherwise, listing the offending constants. Exits 1 if any declaration
is FALSIFIED, 2 if the log has no K3CONST line at all (an empty haystack is not a pass).
FORBIDDEN SET (fixed 2026-11-12, 70th head): DERIVED from the authority, i.e. every top-level namespace this repository's own .lean
files declare (`git grep '^namespace '`), minus the whitelisted VIRC, VIRL1, VIRL2 and X86, plus the declared list. A hand-typed list
missed K7.* (generic definitions in a non-whitelisted namespace), and this derivation closes that hole for every namespace the repo
declares. LIMIT: a constant from OUTSIDE this repo is admitted unless program-named (core/Std/Mathlib are not enumerated).
"""
import os, re, subprocess, sys
WHITE = {"VIRC", "VIRL1", "VIRL2", "X86"}
root = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
declared = subprocess.run(["git", "-C", root, "grep", "-h", "-E", r"^namespace [A-Za-z0-9_.]+", "--", "*.lean"],
                          capture_output=True, text=True).stdout.split("\n")
repo_ns = {l.split()[1].split(".")[0] for l in declared if l.startswith("namespace ")}
if not repo_ns:
    print("k3_check: derived 0 repo namespaces: the census measured nothing"); sys.exit(2)
FORBID_NS = tuple(sorted(n + "." for n in (repo_ns - WHITE) | {"VIRL3", "VIRL4", "VIRP", "VIRDeflate", "Router", "X86Compose"}))
FORBID_WORD = re.compile(r"router|inflate|deflate", re.I)
raw = open(sys.argv[1], "rb").read().decode("utf-8", "replace")
rows = re.findall(r"K3CONST (\S+) (\S+)", raw)
if not rows:
    print("k3_check: NO K3CONST lines: the log measured nothing"); sys.exit(2)
decls = {}
print("k3_check: forbidden namespaces (derived):", " ".join(FORBID_NS))
for d, c in rows:
    decls.setdefault(d, []).append(c)
bad_any = False
for d, cs in decls.items():
    bad = [c for c in cs if c.startswith(FORBID_NS) or FORBID_WORD.search(c)]
    bad_any |= bool(bad)
    print(f"{'FALSIFIED' if bad else 'OK'} {d}: {len(cs)} constants" + (f"; offending: {' '.join(sorted(set(bad)))}" if bad else ""))
sys.exit(1 if bad_any else 0)
