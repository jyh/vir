#!/usr/bin/env python3
"""transcribe_l3.py INPUTS LEANLOG — the L3 transcription check (l3/DECLARATIONS-LEAN.md).

Reads the TEXT of inputs/L3-programs.md: the layout numerals, the F and U code blocks. Expands the macros RD32 / EXIT / EMIT
as the file's "Macros" section states them, compiles names to de Bruijn indices (innermost binder wins), and prints each term
as the S-expression VIRL3/Transcribe.lean prints. U_tx is built from U by R3's stated rule: the post-decrement EXIT(2)
preceded by `store(w1, add(K, sender), t)` (the binder's name, w2, is the Lean arm's, declared). Compares with the lines
`F …`, `U …`, `U_tx …` of LEANLOG (a saltbuild log of VIRL3/Transcribe.lean). Prints SAME/DIFF per term; rc 0 iff all SAME.
LIMITS: the parser reads only the forms L3's programs use; it shares the S-expression FORMAT with the Lean printer (one author),
so it checks the transcription (which ops, which operands, which binders) and not the printer.
"""
import re, sys

def section(text, head):
    i = text.index(head)
    j = text.index('```', i); k = text.index('```', j + 3)
    return text[j + 3:k]

def numerals(text):
    m = re.search(r'NW = (\d+), NS = (\d+), NT = (\d+)', text)
    nw, ns, nt = map(int, m.groups())
    a = 3 + nw
    return {'NW': nw, 'NS': ns, 'NT': nt, 'A': a, 'K': a + ns * nt}

TOK = re.compile(r'\s*(←|\[|\]|\(|\)|,|:|=|/|[A-Za-z_][A-Za-z0-9_′″]*|-?\d+)')

def tokens(s):
    out, i = [], 0
    s = s.strip()
    while i < len(s):
        m = TOK.match(s, i)
        if not m:
            raise SystemExit(f'transcribe_l3: cannot tokenise at {s[i:i+30]!r}')
        out.append(m.group(1)); i = m.end()
        while i < len(s) and s[i].isspace(): i += 1
    return out

class P:
    def __init__(self, toks, nums): self.t, self.i, self.n = toks, 0, nums
    def peek(self): return self.t[self.i] if self.i < len(self.t) else None
    def eat(self, x=None):
        t = self.peek()
        if x is not None and t != x: raise SystemExit(f'transcribe_l3: expected {x!r}, got {t!r} at token {self.i}')
        self.i += 1; return t
    def atom(self):
        t = self.eat()
        if re.fullmatch(r'-?\d+', t): return ('i', int(t))
        if t in self.n: return ('i', self.n[t])
        if self.peek() == '(':
            self.eat('('); args = [self.atom()]
            while self.peek() == ',': self.eat(','); args.append(self.atom())
            self.eat(')'); return ('p', t, args)
        return ('v', t)
    def subst_suffix(self, w):
        if self.peek() == '[':
            self.eat('['); new = self.eat(); self.eat('/'); old = self.eat(); self.eat(']')
            assert old == 'w', old
            return new
        return w
    def expr(self, w='w'):
        t = self.peek()
        if t == 'let':
            self.eat('let'); x = self.eat(); self.eat(':'); ty = self.eat()
            if self.peek() == '←':
                self.eat('←'); op = self.eat(); self.eat('('); args = [self.atom()]
                while self.peek() == ',': self.eat(','); args.append(self.atom())
                self.eat(')'); self.eat('in'); return ('op', x, ty, op, args, self.expr(w))
            self.eat('='); self.eat('ret'); a = self.atom(); self.eat('in')
            return ('let', x, ty, ('ret', a), self.expr(w))
        if t == 'if':
            self.eat('if'); a = self.atom(); self.eat('then'); e1 = self.expr(w); self.eat('else'); e2 = self.expr(w)
            return ('if', a, e1, e2)
        if t == 'ret':
            self.eat('ret'); return ('ret', self.atom())
        if t == 'RD32':
            self.eat('RD32'); self.eat('('); o = int(self.eat()); self.eat(','); x = self.eat(); self.eat(')')
            k = self.expr(w)
            ld = lambda nm, off, rest: ('op', nm, 'int', 'load', [('v', w), ('i', off)], rest)
            s = ('p', 'add', [('v', x + '0'), ('p', 'add', [('p', 'mul', [('i', 256), ('v', x + '1')]),
                 ('p', 'add', [('p', 'mul', [('i', 65536), ('v', x + '2')]), ('p', 'mul', [('i', 16777216), ('v', x + '3')])])])])
            return ld(x + '0', 3 + o, ld(x + '1', 4 + o, ld(x + '2', 5 + o, ld(x + '3', 6 + o, ('let', x, 'int', ('ret', s), k)))))
        if t == 'EXIT':
            self.eat('EXIT'); self.eat('('); c = int(self.eat()); self.eat(')'); ww = self.subst_suffix(w)
            return ('op', 'w′', 'cap', 'store', [('v', ww), ('i', 1), ('i', c)], ('ret', ('v', 'w′')))
        if t == 'EMIT':
            self.eat('EMIT'); ww = self.subst_suffix(w)
            return ('op', 'w′', 'cap', 'store', [('v', ww), ('i', 1), ('i', 0)],
                    ('op', 'w″', 'cap', 'store', [('v', 'w′'), ('i', 2), ('i', 24)], ('ret', ('v', 'w″'))))
        raise SystemExit(f'transcribe_l3: unexpected token {t!r} at {self.i}')

def utx(e):
    """R3's rule: the post-decrement EXIT(2), i.e. the EXIT whose world is w1, preceded by store(w1, add(K, sender), t)."""
    if e[0] == 'op' and e[3] == 'store' and e[4][0] == ('v', 'w1') and e[4][1:] == [('i', 1), ('i', 2)]:
        return ('op', 'w2', 'cap', 'store', [('v', 'w1'), ('p', 'add', [('i', NUMS['K']), ('v', 'sender')]), ('v', 't')],
                ('op', 'w′', 'cap', 'store', [('v', 'w2'), ('i', 1), ('i', 2)], ('ret', ('v', 'w′'))))
    if e[0] == 'op': return e[:5] + (utx(e[5]),)
    if e[0] == 'let': return ('let', e[1], e[2], e[3], utx(e[4]))
    if e[0] == 'if': return ('if', e[1], utx(e[2]), utx(e[3]))
    return e

def sa(a, env):
    if a[0] == 'i': return str(a[1])
    if a[0] == 'v': return f'#{env.index(a[1])}'
    return '(' + a[1] + ''.join(' ' + sa(x, env) for x in a[2]) + ')'

def st(e, env):
    if e[0] == 'ret': return f'(ret {sa(e[1], env)})'
    if e[0] == 'let': return f'(let {e[2]} {st(e[3], env)} {st(e[4], [e[1]] + env)})'
    if e[0] == 'op': return f'({e[3]} {e[2]} [{" ".join(sa(a, env) for a in e[4])}] {st(e[5], [e[1]] + env)})'
    if e[0] == 'if': return f'(if {sa(e[1], env)} {st(e[2], env)} {st(e[3], env)})'

def main():
    global NUMS
    text = open(sys.argv[1], encoding='utf-8').read()
    NUMS = numerals(text)
    f = P(tokens(section(text, '## F ')), NUMS).expr()
    u = P(tokens(section(text, '## U ')), NUMS).expr()
    mine = {'F': st(f, ['w']), 'U': st(u, ['w']), 'U_tx': st(utx(u), ['w'])}
    lean = {}
    for line in open(sys.argv[2], encoding='utf-8'):
        m = re.match(r'^(F|U|U_tx) (\(.*\))\s*$', line)
        if m: lean[m.group(1)] = m.group(2)
    rc = 0
    for k in ('F', 'U', 'U_tx'):
        ok = lean.get(k) == mine[k]
        print(f'TRANSCRIBE {k}: {"SAME" if ok else "DIFF"} (text {len(mine[k])} chars, lean {len(lean.get(k, ""))} chars)')
        if not ok:
            rc = 1
            a, b = mine[k], lean.get(k, '')
            i = next((j for j in range(min(len(a), len(b))) if a[j] != b[j]), min(len(a), len(b)))
            print(f'  first difference at char {i}: text …{a[max(0,i-40):i+40]}… lean …{b[max(0,i-40):i+40]}…')
    print(f'TRANSCRIBE rc={rc} (limit: one author for both printers; checks the transcription, not the printer)')
    sys.exit(rc)

if __name__ == '__main__':
    main()
