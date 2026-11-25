#!/usr/bin/env python3
"""vir STATUS row 46: the AXIOM GATE. Since 2026-11-23 an axiom receipt is a TRIPLE (the helm's routing, h2c's probe).

  axiom_gate.py AUDIT.log --build BUILD.log [--build ...] [--control CONTROL.log]   the receipt form (default)
  axiom_gate.py --legacy-pair [--no-control] AUDIT.log                      the pre-11-23 pair, for logs taken before it

WHY: `#print axioms` on an IMPORTED name reads a table written into that name's olean when its module was built. With an
upstream proof turned to `sorry` and only the upstream rebuilt, a downstream name prints "does not depend on any axioms"
(STALE CLEAN), in a log with saltbuild EXIT=0 and an in-file planted sorry printing sorryAx (h2c, salt's pin, p4). The
in-file control tests the printer only. A control can show the path REPORTS; only a build shows the tables are CURRENT.

THE TRIPLE (every term read from the logs; headers are written by harness/build_header.py through logged-build.sh):
 (1) BUILD: each --build log carries `logged-build: mode=build … root=… targets=… src=… start=…`, ends `saltbuild EXIT=0`
     and then `logged-build: end=`; its src (sha over every library source in the repo) and root (which clone) EQUAL the
     audit's; it ENDED before the audit STARTED; no other build log at a different src in the same log directories
     started between them (edit, build, revert); and the union of the targets covers every vir-library module the
     audit file imports, each EXACTLY.
 (2) AUDIT: `logged-build: mode=audit … imports=… prints=… src=… start=…`, ends `saltbuild EXIT=0`, every `#print axioms`
     row is at most propext · Classical.choice · Quot.sound (or none) except the controls, and the rows parsed equal
     prints= (Lean wraps a row past 120 columns; a row is read from `[` to the first `]` across lines).
 (3) IMPORTED CONTROL: `'Lean.reduceBool' depends on axioms: [Lean.trustCompiler]` in the audit log (an imported core
     constant, read from its table), or in a --control log (mode=audit, EXIT=0, the SAME src as the audit: vir's
     AuditControl.lean run). An in-file `control_sorry`, if present, must still show sorryAx (a printer check).
rc 0 = all three hold; rc 1 = a named violation; rc 2 = no log / no axiom rows / bad usage.
LIMITS, printed with the verdict: it reads logs and does not re-run Lean; it gates only the names the audit file prints;
src covers library sources of this repo (not .lake/packages, which the manifest pins); an import is covered only
by a build target of EXACTLY that module (lake makes the target's cone current; a lib root need not import every submodule).
"""
import glob, os, re, sys
OK = {'propext', 'Classical.choice', 'Quot.sound'}
IMP = ('Lean.reduceBool', {'Lean.trustCompiler'})
LIM = ('(limit: reads logs only, no Lean re-run; gates only the names the audit prints; src = this repo\'s library sources; '
       'the between-builds check reads every logs/ and repro/ directory of the repo; a build outside logged-build.sh is not seen by it)')

def read(p):
    try:
        return open(p, encoding='utf-8', errors='replace').read().splitlines()
    except OSError:
        return None

def header(lines):
    for ln in lines:
        if ln.startswith('logged-build: mode='):
            return dict(kv.split('=', 1) for kv in ln[len('logged-build: '):].split() if '=' in kv)
    return None

def hdr_word(h, want):
    """row 420: a header PRESENT in another mode is not a missing header; name what the log is."""
    if h is None:
        return 'HEADER MISSING (no `logged-build: mode=` line: targets, src and start unreadable)'
    return f'mode={h.get("mode")}, not a{"n" if want == "audit" else ""} {want} log'

def end_of(lines):
    e = [ln for ln in lines if ln.startswith('logged-build: end=')]
    try:
        return int(e[-1].split('=', 1)[1]) if e else None
    except ValueError:
        return None

def log_dirs(*logs):
    """h2c X1: a path dependency builds IN PLACE, so an edit-build-revert launched from a sibling project rewrites the same
    oleans and logs in that project's directory. Scan every `logs`/`repro` directory of the repo holding the logs (walked
    up to its .git), not only the two the logs sit in."""
    dirs = {os.path.dirname(os.path.abspath(x)) for x in logs}
    for x in logs:
        d = os.path.dirname(os.path.abspath(x))
        while d != '/' and not os.path.exists(os.path.join(d, '.git')):
            d = os.path.dirname(d)
        if d == '/':
            continue
        for w, ds, _ in os.walk(d):
            ds[:] = [y for y in ds if y not in ('.lake', '.git', 'node_modules')]
            if os.path.basename(w) in ('logs', 'repro'):
                dirs.add(w)
    return dirs

def builds_between(dirs, lo, hi, src, root, skip):
    """h2c F3: another build in the same log directories, started between the chosen build and the audit, at a DIFFERENT
    src, may have rewritten the tables the audit reads (edit, build, revert). Refuse it; a bare saltbuild is not seen."""
    hits = []
    for d in dirs:
        for q in sorted(glob.glob(os.path.join(d, '*.log'))):
            if os.path.abspath(q) in skip:
                continue
            h = header(read(q) or [])
            if not h or h.get('mode') != 'build' or h.get('root') != root:
                continue
            try:
                t = int(h.get('start', 'x'))
            except ValueError:
                continue
            if lo < t < hi and h.get('src') != src:
                hits.append(os.path.basename(q))
    return hits

def last_exit(lines):
    ex = [ln for ln in lines if ln.startswith('saltbuild EXIT=')]
    return ex[-1] if ex else 'MISSING'

def rows_of(lines):
    """h2c F1 (measured at v4.32.0-rc1): Lean wraps a row past 120 columns, after a comma inside `[...]`, so a row is
    every line from its `'name' depends on axioms: [` to the first `]`, joined."""
    out, i = [], 0
    while i < len(lines):
        ln = lines[i]
        n = re.match(r"^'(.+)' does not depend on any axioms$", ln)   # (.+): a PRIMED name holds a ' (h2c N5)
        if n:
            out.append((n.group(1), set())); i += 1; continue
        m = re.match(r"^'(.+?)' depends on axioms: \[(.*)$", ln)
        if m:
            body, j = m.group(2), i
            while ']' not in body and j + 1 < len(lines):
                j += 1; body += ' ' + lines[j].strip()
            inner = body.split(']', 1)[0]
            out.append((m.group(1), {a.strip() for a in inner.split(',') if a.strip()}))
            i = j + 1; continue
        i += 1
    return out

def gate_rows(lines, bad):
    rows, control, imp = rows_of(lines), None, None
    for name, ax in rows:
        if name == 'control_sorry':
            control = 'sorryAx' in ax
        elif name == IMP[0]:
            imp = ax == IMP[1]
        elif not ax <= OK:
            bad.append(f'{name}: {sorted(ax - OK)}')
    if last_exit(lines) != 'saltbuild EXIT=0':
        bad.append(f'audit exit line: {last_exit(lines)}')
    if control is False:
        bad.append('control_sorry: does NOT show sorryAx')
    return len(rows), control, imp

def legacy(p, no_control):
    lines = read(p)
    if lines is None:
        print(f'AXIOM-GATE NO-LOG {p}'); return 2
    bad = []
    n, control, _ = gate_rows(lines, bad)
    if n == 0:
        print(f'AXIOM-GATE EMPTY {p} (no #print axioms rows)'); return 2
    lim = '(LEGACY PAIR: in-file control only; STALE CLEAN NOT EXCLUDED, no build line read; ' + LIM[1:]
    if control is None and not no_control:
        bad.append('control_sorry: MISSING')
    if bad:
        print(f'AXIOM-GATE FAIL {p} rows={n} ' + '; '.join(bad) + ' ' + lim); return 1
    print(f'AXIOM-GATE LEGACY-OK {p} rows={n} control=' + ('ABSENT (--no-control)' if control is None else 'sorryAx') + ' ' + lim); return 0

def control_from(c, ah, bad):
    cl = read(c)
    if cl is None:
        bad.append(f'control {c}: NO-LOG'); return None
    ch = header(cl)
    if ch is None or ch.get('mode') != 'audit':
        bad.append(f'control {c}: ' + hdr_word(ch, 'audit')); return None
    if last_exit(cl) != 'saltbuild EXIT=0':
        bad.append(f'control {c}: {last_exit(cl)}'); return None
    if ah and (ch.get('src') != ah.get('src') or ch.get('root') != ah.get('root')):
        bad.append(f'control {c}: src {ch.get("src")} != audit src {ah.get("src")}'); return None
    got = [ax for name, ax in rows_of(cl) if name == IMP[0]]
    return None if not got else got[-1] == IMP[1]

def triple(p, builds, controls=()):
    lines = read(p)
    if lines is None:
        print(f'AXIOM-GATE NO-LOG {p}'); return 2
    bad = []
    n, control, imp = gate_rows(lines, bad)
    if n == 0:
        print(f'AXIOM-GATE EMPTY {p} (no #print axioms rows)'); return 2
    ah = header(lines)
    for c in controls:
        ci = control_from(c, ah, bad)
        if imp is None and ci is not None:
            imp = ci
    if imp is None:
        bad.append(f'IMPORTED CONTROL MISSING (`#print axioms {IMP[0]}` must print [Lean.trustCompiler]; an in-file sorry tests the printer only)')
    elif imp is False:
        bad.append(f'IMPORTED CONTROL does not report ({IMP[0]} must print exactly [Lean.trustCompiler])')
    if ah is None:
        bad.append('AUDIT HEADER MISSING (no `logged-build: mode=audit` line: imports, src and start cannot be read)')
    elif ah.get('mode') != 'audit':
        bad.append(f'AUDIT LOG is mode={ah.get("mode")}, not an audit log (imports and prints= are not in its header)')
    if ah:
        try:
            pr = int(ah.get('prints', 'x'))
            if pr != n:
                bad.append(f'ROW COUNT {n} != the audit file\'s {pr} `#print axioms` lines (a row the parser cannot read is not a pass)')
        except ValueError:
            bad.append('AUDIT HEADER has no prints= (the row count cannot be checked)')
    if not builds:
        bad.append('NO BUILD LINE (--build): a control cannot show an olean is CURRENT; the stale-clean shape passes without one')
    covered, used = set(), []
    for b in builds:
        bl = read(b)
        if bl is None:
            bad.append(f'build {b}: NO-LOG'); continue
        bh = header(bl)
        if bh is None or bh.get('mode') != 'build':
            bad.append(f'build {b}: ' + hdr_word(bh, 'build')); continue
        if last_exit(bl) != 'saltbuild EXIT=0':
            bad.append(f'build {b}: {last_exit(bl)}'); continue
        if ah:
            if bh.get('root') != ah.get('root'):
                bad.append(f'build {b}: root {bh.get("root")} != audit root {ah.get("root")} (another clone)'); continue
            if bh.get('src') != ah.get('src'):
                bad.append(f'build {b}: src {bh.get("src")} != audit src {ah.get("src")} (a library source changed between build and audit)'); continue
            be = end_of(bl)
            try:
                bs, as_ = int(bh.get('start', 'x')), int(ah.get('start', 'x'))
            except ValueError:
                bad.append(f'build {b}: start unreadable'); continue
            if be is None:
                bad.append(f'build {b}: NO end= line (it cannot be shown to have FINISHED before the audit started)'); continue
            if be >= as_:
                bad.append(f'build {b}: ended at/after the audit started (overlap: the order is unknown)'); continue
            mid = builds_between(log_dirs(p, b), bs, as_,
                                 ah.get('src'), ah.get('root'), {os.path.abspath(x) for x in builds})
            if mid:
                bad.append(f'build {b}: a build at ANOTHER src ran between it and the audit ({",".join(mid)})'); continue
        tg = [t for t in bh.get('targets', '').split(',') if t and t != '-']
        covered |= set(tg); used.append(','.join(tg))
    imports = [m for m in (ah or {}).get('imports', '-').split(',') if m and m != '-']
    if ah and builds:
        miss = [m for m in imports if m not in covered]   # exact: a lib root need not import every submodule
        if miss:
            bad.append(f'imports NOT BUILT: {",".join(miss)} (targets {",".join(sorted(covered)) or "-"})')
        if not imports:
            bad.append('audit imports no vir library module (nothing to make current; is this the right audit?)')
    if bad:
        print(f'AXIOM-GATE FAIL {p} rows={n} ' + '; '.join(bad) + ' ' + LIM); return 1
    print(f'AXIOM-GATE OK {p} rows={n} TRIPLE build=[{" | ".join(used)}] imports={",".join(imports)} src={ah.get("src")} '
          f'imported-control={IMP[0]}:trustCompiler in-file-control=' + ('ABSENT' if control is None else 'sorryAx') + ' ' + LIM); return 0

def main(argv):
    args, builds, controls, i = [], [], [], 0
    while i < len(argv):
        if argv[i] == '--build' and i + 1 < len(argv):
            builds.append(argv[i + 1]); i += 2
        elif argv[i] == '--control' and i + 1 < len(argv):
            controls.append(argv[i + 1]); i += 2
        else:
            args.append(argv[i]); i += 1
    flags = {a for a in args if a.startswith('--')}
    pos = [a for a in args if not a.startswith('--')]
    if len(pos) != 1 or flags - {'--legacy-pair', '--no-control'} or ('--no-control' in flags and '--legacy-pair' not in flags):
        print('usage: axiom_gate.py AUDIT.log --build BUILD.log [...] [--control CONTROL.log] | axiom_gate.py --legacy-pair [--no-control] AUDIT.log'); return 2
    if '--legacy-pair' in flags:
        if builds or controls:
            print('usage: --legacy-pair takes no --build/--control (it is the pre-11-23 form)'); return 2
        return legacy(pos[0], '--no-control' in flags)
    return triple(pos[0], builds, controls)

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
