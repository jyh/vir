#!/usr/bin/env python3
"""build_header.py PROJECT_DIR [saltbuild args...] — print ONE header line for a logged-build.sh log, BEFORE saltbuild runs.

WHY (the helm's routing 2026-11-23, h2c's probe at salt's pin): `#print axioms` on an IMPORTED name reads a table written
into that name's olean when its module was built. If an upstream proof gains a `sorry` and only the upstream is rebuilt,
a downstream name still prints "does not depend on any axioms" (STALE CLEAN), with saltbuild EXIT=0 and an in-file
planted-sorry control printing sorryAx in the same log. No control can show an olean is current; only a BUILD of the
audited file's imports, taken over the same library sources, can. This header is what lets axiom_gate.py check that
from the logs alone:

  logged-build: mode=build project=<dir> targets=<M,...> src=<sha256/16> srcfiles=<n> start=<epoch ms>
  logged-build: mode=audit project=<dir> file=<f.lean> file_sha256=<16> imports=<vir libs' modules> extimports=<others> src=… start=…

src = sha256 over every LIBRARY source in this repo: for each lakefile.toml outside .lake/, each [[lean_lib]] name L gives
<proj>/L.lean and <proj>/L/**.lean (path and bytes, sorted). Scratch files (Audit*.lean, probes/, mutants/) are NOT in it,
so writing a scratch between the build and the audit does not move it, and editing any library file does.
LIMITS, declared: a lean_lib with `roots`/`globs` other than its name is not modelled (none in this repo at 2026-11-23,
measured); packages under .lake/packages (mathlib, x86lean) are pinned by manifest and not hashed.
"""
import hashlib, os, re, sys, time

def repo_root(d):
    d = os.path.abspath(d)
    while d != '/' and not os.path.isdir(os.path.join(d, '.git')) and not os.path.isfile(os.path.join(d, '.git')):
        d = os.path.dirname(d)
    return d

def libs_of(lakefile):
    t = open(lakefile, encoding='utf-8').read()
    out = []
    for blk in re.split(r'^\[\[', t, flags=re.M)[1:]:
        if blk.startswith('lean_lib]]'):
            m = re.search(r'^name\s*=\s*"([^"]+)"', blk, re.M)
            if m:
                out.append(m.group(1))
    dt = re.search(r'^defaultTargets\s*=\s*\[([^\]]*)\]', t, re.M)
    return out, ([x.strip().strip('"') for x in dt.group(1).split(',') if x.strip()] if dt else [])

def lib_files(root):
    files, libnames = [], set()
    for d, dirs, fs in os.walk(root):
        dirs[:] = [x for x in dirs if x not in ('.lake', '.git')]
        if 'lakefile.toml' in fs:
            libs, _ = libs_of(os.path.join(d, 'lakefile.toml'))
            for L in libs:
                libnames.add(L)
                top = os.path.join(d, L + '.lean')
                if os.path.isfile(top):
                    files.append(top)
                for d2, dirs2, fs2 in os.walk(os.path.join(d, L)):
                    dirs2[:] = [x for x in dirs2 if x not in ('.lake',)]
                    files += [os.path.join(d2, f) for f in fs2 if f.endswith('.lean')]
    return sorted(set(files)), libnames

def src_hash(root):
    files, libnames = lib_files(root)
    h = hashlib.sha256()
    for f in files:
        h.update(os.path.relpath(f, root).encode() + b'\0')
        h.update(open(f, 'rb').read() + b'\0')
    return h.hexdigest()[:16], len(files), libnames

def main(argv):
    if not argv:
        print('logged-build: header REFUSED (no project dir)'); return 2
    proj = os.path.abspath(argv[0]); args = argv[1:]
    root = repo_root(proj)
    src, n, libnames = src_hash(root)
    rel = os.path.relpath(proj, root)
    pos = [a for a in args if not a.startswith('-')]
    # saltbuild: `--cap N X.lean` is an audit; the cap's value is not a target
    if '--cap' in args:
        i = args.index('--cap'); pos = [a for a in args[i + 2:] if not a.startswith('-')] + [a for a in args[:i] if not a.startswith('-')]
    start = int(time.time() * 1000)   # ms: a fast build and its audit can share a second
    if pos and pos[-1].endswith('.lean'):
        f = pos[-1]; fp = os.path.join(proj, f)
        try:
            b = open(fp, 'rb').read()
        except OSError:
            print(f'logged-build: mode=audit project={rel} file={f} file_sha256=MISSING src={src} srcfiles={n} start={start}'); return 0
        imps = re.findall(r'^import\s+(\S+)', b.decode('utf-8', 'replace'), re.M)
        own = [m for m in imps if m.split('.')[0] in libnames]
        ext = [m for m in imps if m not in own]
        print(f'logged-build: mode=audit project={rel} file={f} file_sha256={hashlib.sha256(b).hexdigest()[:16]} '
              f'imports={",".join(own) or "-"} extimports={",".join(ext) or "-"} src={src} srcfiles={n} start={start}')
    else:
        tg = [a for a in pos if a != 'build']
        if not tg:
            _, dflt = libs_of(os.path.join(proj, 'lakefile.toml'))
            tg = dflt; tag = ' (default)'
        else:
            tag = ''
        print(f'logged-build: mode=build project={rel} targets={",".join(tg) or "-"}{tag} src={src} srcfiles={n} start={start}')
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
