#!/usr/bin/env python3
"""K3's whitelist (compiler/DECLARATIONS-S1.md l.46-50) applied to the K3CONST lines of a probe log.

usage: k3_check.py LOG
Per declaration: OK if every constant in its type lies in VIRC.* VIRL1.* VIRL2.* X86.* or Lean core/Std/Mathlib (i.e. is in
no forbidden namespace and names no program); FALSIFIED otherwise, listing the offending constants. Exits 1 if any declaration
is FALSIFIED, 2 if the log has no K3CONST line at all (an empty haystack is not a pass).
LIMIT: 'core/Std/Mathlib' is read as 'not in a forbidden namespace and not program-named'; it does not enumerate Mathlib.
"""
import re, sys
FORBID_NS = ("VIRL3.", "VIRL4.", "VIRP.", "VIRDeflate.", "Router.", "X86Compose.", "K5.")
FORBID_WORD = re.compile(r"router|inflate|deflate", re.I)
raw = open(sys.argv[1], "rb").read().decode("utf-8", "replace")
rows = re.findall(r"K3CONST (\S+) (\S+)", raw)
if not rows:
    print("k3_check: NO K3CONST lines: the log measured nothing"); sys.exit(2)
decls = {}
for d, c in rows:
    decls.setdefault(d, []).append(c)
bad_any = False
for d, cs in decls.items():
    bad = [c for c in cs if c.startswith(FORBID_NS) or FORBID_WORD.search(c)]
    bad_any |= bool(bad)
    print(f"{'FALSIFIED' if bad else 'OK'} {d}: {len(cs)} constants" + (f"; offending: {' '.join(sorted(set(bad)))}" if bad else ""))
sys.exit(1 if bad_any else 0)
