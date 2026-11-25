#!/usr/bin/env python3
"""triple_drive.py OUTDIR [--dry-run] [--only PROJ ...] — drive the axiom TRIPLE on every lake project and PRINT the census.

WHY (row 430, 2026-11-25): harness/TRIPLE-CENSUS-2026-11-25.md was the author's transcription of AXIOM-GATE lines from
scratch logs ("not a count anyone can reproduce from the artifacts"; its own Limits). This script is the drive itself, so
a reader re-checks the census with one command and the table is the script's output, never typed by hand.

POPULATION, derived from the tree (never a list in this file):
  projects = every tracked lakefile.toml's directory. Each must have exactly ONE logged-build.sh: <proj>/logged-build.sh,
             or <proj>/<sub>/logged-build.sh whose header builds <proj> (lean/ -> lean/VIRB). None or two: REFUSED.
  targets  = the project's [[lean_lib]] names (build_header.libs_of), plus every in-repo module an audit imports that is
             not a lib root (l1/AuditInduction.lean imports VIRL1.Induction, which `lake build VIRL1` does not build).
  audits   = every tracked <proj>/Audit*.lean directly in the project dir, except AuditControl.lean (probes/ etc. are scratch).
  control  = <proj>/AuditControl.lean, required (the imported control; axiom_gate refuses an audit without it).
  in-file  = an audit file declaring `theorem control_sorry<suffix>` with a suffix gets --in-file-control <that name>;
             a file declaring two such names is REFUSED (the gate takes one exact name).
ORDER per project: build (targets) -> AuditControl.lean -> each audit -> axiom_gate.py AUDIT --build B --control C.
Every saltbuild goes through the project's logged-build.sh with LOGDIR=OUTDIR/<proj> (so no counted logs/ changes and
C6 is unaffected) and SALTBUILD_PRIO as set by the caller (O95 builds run PRIO=P1).

OUTPUT: one TSV row per audit (project, targets, audit, rows, verdict, gate rc, gate line), then
  TRIPLE-DRIVE <n_ok>/<n> OK  projects=<p>  (rc 0 iff every audit's gate read rc 0 and every saltbuild read EXIT=0)
rc 0 all OK · rc 1 a gate or a build failed · rc 2 the population is malformed (refused before any build) or bad usage.
--dry-run prints the population and the commands, runs nothing.
LIMITS, declared beside the verdict: the gate reads logs and re-runs no Lean beyond this drive; it gates only the names an
audit file prints; src hashes this repo's library sources, not .lake/packages.
"""
import os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from build_header import libs_of  # noqa: E402

ROOT = os.path.dirname(HERE)
LIM = ('(limits: gates only the names each audit prints; src = this repo\'s library sources, not .lake/packages; '
       'one drive at one source state)')


def tracked(pattern_re):
    out = subprocess.run(['git', '-C', ROOT, 'ls-files'], capture_output=True, text=True, check=True).stdout.split('\n')
    return sorted(p for p in out if p and re.search(pattern_re, p))


def population():
    refusals, projs = [], []
    files = tracked(r'.')
    for lf in tracked(r'(^|/)lakefile\.toml$'):
        proj = os.path.dirname(lf)
        if '.lake/' in lf or not proj:
            continue
        wrappers = [p for p in files if p == f'{proj}/logged-build.sh'
                    or re.fullmatch(re.escape(proj) + r'/[^/]+/logged-build\.sh', p)]
        if len(wrappers) != 1:
            refusals.append(f'{proj}: {len(wrappers)} logged-build.sh wrappers (need exactly one): {wrappers or "-"}')
            continue
        libs, _ = libs_of(os.path.join(ROOT, lf))
        if not libs:
            refusals.append(f'{proj}: no [[lean_lib]] in {lf}')
            continue
        audits = [p for p in files if re.fullmatch(re.escape(proj) + r'/Audit[A-Za-z0-9_]*\.lean', p)
                  and not p.endswith('/AuditControl.lean')]
        if f'{proj}/AuditControl.lean' not in files:
            refusals.append(f'{proj}: no AuditControl.lean (the imported control)')
            continue
        if not audits:
            refusals.append(f'{proj}: no Audit*.lean to gate')
            continue
        rows = []
        for a in audits:
            names = re.findall(r'^theorem\s+(control_sorry\w*)', open(os.path.join(ROOT, a), encoding='utf-8').read(), re.M)
            if len(set(names)) > 1:
                refusals.append(f'{a}: {len(set(names))} in-file controls {sorted(set(names))} (the gate takes one name)')
                continue
            rows.append((a, names[0] if names and names[0] != 'control_sorry' else None))
        # the build covers every in-repo module an audit imports, not only the lib roots: l1/AuditInduction.lean imports
        # VIRL1.Induction, which `lake build VIRL1` does not reach (drive-430: axiom_gate 'imports NOT BUILT', rc 1)
        mods = set()
        for a, _ in rows:
            for m in re.findall(r'^import\s+(\S+)', open(os.path.join(ROOT, a), encoding='utf-8').read(), re.M):
                if m.split('.')[0] in libs and m not in libs:
                    mods.add(m)
        projs.append({'proj': proj, 'wrapper': wrappers[0], 'libs': libs, 'targets': libs + sorted(mods), 'audits': rows})
    return projs, refusals


def run_wrapper(wrapper, logdir, name, args):
    env = dict(os.environ, LOGDIR=logdir)
    r = subprocess.run(['bash', os.path.join(ROOT, wrapper), name] + args, env=env, capture_output=True, text=True)
    log = os.path.join(logdir, name + '.log')
    exit_lines = [l for l in open(log, encoding='utf-8', errors='replace').read().split('\n')
                  if l.startswith('saltbuild EXIT=')] if os.path.exists(log) else []
    return r.returncode, log, (exit_lines[-1] if exit_lines else 'saltbuild EXIT= MISSING')


def main(argv):
    dry = '--dry-run' in argv
    only, rest, i = [], [], 0
    args = [a for a in argv if a != '--dry-run']
    while i < len(args):
        if args[i] == '--only' and i + 1 < len(args):
            only.append(args[i + 1].rstrip('/')); i += 2
        else:
            rest.append(args[i]); i += 1
    if len(rest) != 1 or rest[0].startswith('-'):
        print('usage: triple_drive.py OUTDIR [--dry-run] [--only PROJ ...]'); return 2
    outdir = os.path.abspath(rest[0])
    if outdir == ROOT or outdir.startswith(ROOT + os.sep):
        print(f'TRIPLE-DRIVE REFUSED: OUTDIR {outdir} is inside the repo (logs would land in the tree; use scratch)'); return 2
    projs, refusals = population()
    if refusals:
        for r in refusals:
            print(f'TRIPLE-DRIVE REFUSED: {r}')
        print(f'TRIPLE-DRIVE POPULATION MALFORMED: {len(refusals)} refusal(s), nothing built'); return 2
    if only:
        unknown = [o for o in only if o not in {p['proj'] for p in projs}]
        if unknown:
            print(f'TRIPLE-DRIVE REFUSED: --only names no project: {unknown}'); return 2
        projs = [p for p in projs if p['proj'] in only]
    n_aud = sum(len(p['audits']) for p in projs)
    print(f'# population: {len(projs)} projects, {n_aud} audits (from tracked lakefile.toml + Audit*.lean)')
    print('project\ttargets\taudit\trows\tverdict\tgate_rc\tgate_line')
    ok = 0
    for p in projs:
        proj, logdir = p['proj'], os.path.join(outdir, p['proj'].replace('/', '_'))
        if dry:
            for a, ctl in p['audits']:
                print(f"{proj}\t{' '.join(p['libs'])}\t{os.path.basename(a)}\t-\tDRY\t-\t"
                      f"{p['wrapper']} build {' '.join(p['targets'])} · AuditControl.lean · {os.path.basename(a)}"
                      + (f' · --in-file-control {ctl}' if ctl else ''))
            continue
        os.makedirs(logdir, exist_ok=False)
        brc, blog, bexit = run_wrapper(p['wrapper'], logdir, 'build', p['targets'])
        crc, clog, cexit = run_wrapper(p['wrapper'], logdir, 'audit-control', ['AuditControl.lean'])
        for k, (a, ctl) in enumerate(p['audits']):
            base = os.path.basename(a)
            arc, alog, aexit = run_wrapper(p['wrapper'], logdir, f'audit-{k:02d}', [base])
            exits = [bexit, cexit, aexit]
            if any(e != 'saltbuild EXIT=0' for e in exits) or brc or crc or arc:
                print(f"{proj}\t{' '.join(p['libs'])}\t{base}\t-\tBUILD-FAIL\t-\tbuild:{bexit} control:{cexit} audit:{aexit}")
                continue
            g = [sys.executable, '-I', os.path.join(HERE, 'axiom_gate.py'), alog, '--build', blog, '--control', clog]
            if ctl:
                g += ['--in-file-control', ctl]
            r = subprocess.run(g, capture_output=True, text=True)
            line = (r.stdout.strip().split('\n') or [''])[-1]
            m = re.search(r'rows=(\d+)', line)
            verdict = 'OK' if r.returncode == 0 else 'FAIL'
            ok += r.returncode == 0
            print(f"{proj}\t{' '.join(p['targets'])}\t{base}\t{m.group(1) if m else '-'}\t{verdict}\t{r.returncode}\t{line[:300]}")
    if dry:
        print(f'TRIPLE-DRIVE DRY {len(projs)} projects, {n_aud} audits; nothing run'); return 0
    print(f'TRIPLE-DRIVE {ok}/{n_aud} OK  projects={len(projs)}  logs={outdir}  {LIM}')
    return 0 if ok == n_aud else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
