#!/usr/bin/env python3
"""vir STATUS row 46: the AXIOM GATE over one saltbuild audit log.
rc 0 = the log ends `saltbuild EXIT=0`, EVERY `#print axioms` row is at most propext · Classical.choice · Quot.sound
(or 'does not depend on any axioms'), EXCEPT `control_sorry`, which MUST show sorryAx (the positive control).
`--no-control` accepts a log with NO control_sorry row and says so in the verdict line (vir lean/Audit.lean has none).
rc 1 = a named violation; rc 2 = no log / no axiom rows (an empty log is not a pass).
LIMIT, printed with the verdict: it reads the log, it does not re-run Lean, and it gates only the declarations
the audit file names (an unaudited theorem is invisible to it)."""
import re, sys
OK = {'propext', 'Classical.choice', 'Quot.sound'}
def main(p, no_control=False):
    try:
        lines = open(p, encoding='utf-8', errors='replace').read().splitlines()
    except OSError:
        print(f'AXIOM-GATE NO-LOG {p}'); return 2
    bad, rows, control = [], 0, None
    for ln in lines:
        m = re.match(r"^'([^']+)' depends on axioms: \[(.*)\]$", ln)
        n = re.match(r"^'([^']+)' does not depend on any axioms$", ln)
        if not (m or n):
            continue
        rows += 1
        name = (m or n).group(1)
        ax = {a.strip() for a in m.group(2).split(',')} if m else set()
        if name == 'control_sorry':
            control = 'sorryAx' in ax
        elif not ax <= OK:
            bad.append(f'{name}: {sorted(ax - OK)}')
    exits = [ln for ln in lines if ln.startswith('saltbuild EXIT=')]
    lim = '(limit: reads the log only; gates only the declarations the audit names)'
    if rows == 0:
        print(f'AXIOM-GATE EMPTY {p} (no #print axioms rows)'); return 2
    if not exits or exits[-1] != 'saltbuild EXIT=0':
        bad.append(f'exit line: {exits[-1] if exits else "MISSING"}')
    if no_control and control is None:
        lim = '(limit: NO POSITIVE CONTROL in this log, DECLARED by --no-control; ' + lim[8:]
    elif control is not True:
        bad.append('control_sorry: ' + ('MISSING' if control is None else 'does NOT show sorryAx'))
    if bad:
        print(f'AXIOM-GATE FAIL {p} rows={rows} ' + '; '.join(bad) + ' ' + lim); return 1
    print(f'AXIOM-GATE OK {p} rows={rows} control=' + ('ABSENT' if control is None else 'sorryAx') + ' ' + lim); return 0
if __name__ == '__main__':
    a = [x for x in sys.argv[1:] if x != '--no-control']
    sys.exit(main(a[0], '--no-control' in sys.argv) if len(a) == 1 else 2)
