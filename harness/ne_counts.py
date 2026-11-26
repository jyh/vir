#!/usr/bin/env python3
"""RESULTS-16's counts (OBJECT-NOCHECK-ENTRY, amend-27), re-derived from committed logs and captures only. No Lean run.

Usage: python3 harness/ne_counts.py [REPO]     prints a TSV to stdout; rc 0 = every input read; rc 2 = an input missing.
The committed copy is harness/ne-counts.tsv; harness/reproduce.sh diffs this script's output against it.

Rows:
  NE8   <decl>  IDENTICAL|DIFFERS  <bytes got>  <bytes capture>  : s3/logs/ne-023.log's #check block vs s3/probes/nc-<decl>-check-deep.txt
  NE1   <decl>  NoFaultP=<n>  Triple=<n>                           : s3/logs/ne-024.log's pp.deepTerms #check block
  NE2   <decl>  <namespaces, comma-joined>                         : every `Ns.name` token in the same block
  NE6   s3      exit_lines=<n>  first=<log>  last=<log>            : `saltbuild EXIT=` lines in s3/logs/ne-001 .. ne-019
  NE6   e2      first_sorry_free_exit0_after_sorry=<log>          : the first EXIT=0 log after the last log carrying `declaration uses`
  DIR   dF      checked=<n> unchecked=<n> sites=<n> table=<n>      : k7/logs/ne-r-011.log's #eval tuple
LIMIT: reads the logs and captures as committed; it does not rebuild, and it trusts the log text to be the build's output.
"""
import os
import re
import sys

STOP = ('@', 'saltbuild', 'logged-build', 'info:', 'warning:')


def block(lines, name):
    """The #check block for `name`: from its `@name :` line to the next line that starts another record."""
    starts = [i for i, l in enumerate(lines) if l.startswith('@' + name + ' :')]
    if len(starts) != 1:
        raise SystemExit(f'ne_counts: {len(starts)} blocks for {name} (need exactly 1)')
    i, out = starts[0], []
    while i < len(lines) and (i == starts[0] or not lines[i].startswith(STOP)):
        out.append(lines[i])
        i += 1
    return '\n'.join(out).rstrip('\n')


def read(path):
    if not os.path.exists(path):
        print(f'ne_counts: MISSING {path}', file=sys.stderr)
        sys.exit(2)
    return open(path, encoding='utf-8').read()


def main(argv):
    repo = os.path.abspath(argv[1]) if len(argv) > 1 else os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    p = lambda *a: os.path.join(repo, *a)
    rows = []
    l23 = read(p('s3', 'logs', 'ne-023.log')).split('\n')
    for d in ('compile_x86', 'compile_x86_proved'):
        got = block(l23, 'S3.' + d)
        want = read(p('s3', 'probes', f'nc-{d}-check-deep.txt')).rstrip('\n')
        rows.append(['NE8', d, 'IDENTICAL' if got == want else 'DIFFERS', str(len(got.encode())), str(len(want.encode()))])
    l24 = read(p('s3', 'logs', 'ne-024.log')).split('\n')
    for d in ('compile_entry', 'compile_entry_run'):
        t = block(l24, 'S3.' + d)
        rows.append(['NE1', d, f"NoFaultP={t.count('NoFaultP')}", f"Triple={len(re.findall(r'[^A-Za-z]Triple[^A-Za-z]', t))}"])
    for d in ('compile_entry', 'compile_entry_run'):
        t = block(l24, 'S3.' + d)
        ns = sorted({m.split('.')[0] for m in re.findall(r'(?<![\w.])([A-Z][A-Za-z0-9]*\.[A-Za-z_][\w′₀-₉]*)', t)})
        rows.append(['NE2', d, ','.join(ns)])
    exits, sorry_logs, exit0 = [], [], []
    for k in range(1, 20):
        name = f'ne-{k:03d}'
        txt = read(p('s3', 'logs', name + '.log'))
        e = re.findall(r'^saltbuild EXIT=(\d+)', txt, re.M)
        exits += [(name, x) for x in e]
        if 'declaration uses' in txt:
            sorry_logs.append(k)
        if e and e[-1] == '0':
            exit0.append(k)
    rows.append(['NE6', 's3', f'exit_lines={len(exits)}', f'first={exits[0][0]}', f'last={exits[-1][0]}'])
    after = [k for k in exit0 if sorry_logs and k > max(sorry_logs)]
    rows.append(['NE6', 'e2', f"first_sorry_free_exit0_after_sorry=ne-{after[0]:03d}" if after else 'first_sorry_free_exit0_after_sorry=-'])
    m = re.findall(r'^\((\d+), (\d+), (\d+), (\d+)\)$', read(p('k7', 'logs', 'ne-r-011.log')), re.M)
    if len(m) != 1:
        raise SystemExit(f'ne_counts: {len(m)} #eval tuples in ne-r-011.log (need exactly 1)')
    c, u, s, tb = m[0]
    rows.append(['DIR', 'dF', f'checked={c}', f'unchecked={u}', f'sites={s}', f'table={tb}'])
    for r in rows:
        print('\t'.join(r))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
