# gen_audit.py — run from l2/: python3 gen_audit.py > Audit.lean. Walks VIRL2.lean imports in order; one #print axioms per theorem, namespace path kept.
import re,sys
mods=[l.split()[1] for l in open('VIRL2.lean') if l.startswith('import ')]
out=[]
for m in mods:
    ns=[]
    for line in open(m.replace('.','/')+'.lean'):
        mm=re.match(r'^namespace\s+(\S+)',line)
        if mm: ns.append(mm.group(1)); continue
        mm=re.match(r'^end\s+(\S+)',line)
        if mm and ns and ns[-1]==mm.group(1): ns.pop(); continue
        mm=re.match(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+)?theorem\s+(\S+)',line)
        if mm: out.append('.'.join(ns+[mm.group(1)]))
print('import VIRL2')
for n in out: print('#print axioms '+n)
