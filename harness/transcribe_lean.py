#!/usr/bin/env python3
"""vir: the A.2 TRANSCRIPTION CHECK for the Lean arm (PREDICTIONS-amend-10, B4).

Reads each definition AS WRITTEN (I2's specs and I3's U in inputs/router-inputs.md; A.3's F in object/appendix-A.tex,
its LaTeX escapes undone by a declared table; J2's specs, J3's U2 and J4's F2 in inputs/program2-inputs.md), parses A.2's
surface syntax, expands every spec call by substitution into its continuation, and emits lean/VIRB/Transcribe.lean: one
`theorem tc_<name> : <parsed term> = <hand-written deep term> := rfl` per term. The Lean build is the check: a parse that
differs from the hand-written term fails `rfl` and the build reads EXIT=1.

LIMITS (printed with --check): equality is up to Lean's definitional unfolding (`rfl`), not characters; the hand-written
side is the deep embedding (VIR.Deep for program 1, VIR.Deep2 for program 2); the translation table (forms, conditions,
codes) is written once here, by hand; the bodies are what is checked.

usage: transcribe_lean.py [--mutate read-offset|spec-offset] [--out FILE]
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# ---------------------------------------------------------------- extraction (the text as written)
LATEX = {'_{0}': '0', r'\ge': '≥', r'\le': '≤', r'\wedge': '∧', r'\equiv': '≡'}


def undo_latex(s):
    def rep(m):
        k = m.group(1)
        if k not in LATEX:
            sys.exit(f"transcribe: REFUSED, an unknown LaTeX escape {k!r} (the table is declared, never guessed)")
        return LATEX[k]
    return re.sub(r'`\\uc\{\$([^$]*)\$\}`', rep, s)


def strip_comments(s):
    return re.sub(r'\(\*.*?\*\)', ' ', s, flags=re.S)


def md_block(path, heading):
    t = open(path, encoding='utf-8').read()
    i = t.index('\n' + heading)
    j = t.index('```', i)
    k = t.index('```', j + 3)
    return t[j + 3:k]


def a3_F():
    t = open(os.path.join(ROOT, 'object', 'appendix-A.tex'), encoding='utf-8').read()
    i = t.index('(* Synthesized & Fused Single-Pass VIR Term *)')
    j = t.index(r'\end{lstlisting}', i)
    return undo_latex(t[i:j])


def defs(block):
    """Split a block into definitions `HEAD ≡ BODY`; returns [(head, body)]."""
    s = strip_comments(block)
    parts = re.split(r'\n(?=\S[^\n]*≡)', '\n' + s.strip())
    out = []
    for p in parts:
        p = p.strip()
        if not p:
            continue
        h, b = p.split('≡', 1)
        out.append((h.strip(), b.strip()))
    return out


# ---------------------------------------------------------------- tokens and AST
TOK = re.compile(r"\s*(?:(?P<num>\d+)|(?P<id>[A-Za-z_][A-Za-z0-9_']*)|(?P<sym>[{}();,.\[\]≥≤=∧+−-]))")


def lex(s):
    out, i = [], 0
    s = s.rstrip()
    while i < len(s):
        m = TOK.match(s, i)
        if not m or m.end() == i:
            if s[i:].strip() == '':
                break
            sys.exit(f"transcribe: REFUSED, cannot lex at {s[i:i+30]!r}")
        out.append(m.group('num') or m.group('id') or m.group('sym'))
        i = m.end()
    return ['-' if t == '−' else t for t in out]


class P:
    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self, k=0):
        return self.t[self.i + k] if self.i + k < len(self.t) else None

    def eat(self, x=None):
        v = self.peek()
        if x is not None and v != x:
            sys.exit(f"transcribe: REFUSED, expected {x!r} got {v!r} at token {self.i}: {' '.join(self.t[max(0,self.i-6):self.i+6])}")
        self.i += 1
        return v

    # expressions (indices and condition operands)
    def atom_expr(self):
        v = self.eat()
        if v == 'len':
            self.eat('('); x = self.eat(); self.eat(')')
            return ('len', x)
        if v.isdigit():
            return ('lit', int(v))
        return ('var', v)

    def expr(self):
        e = self.atom_expr()
        while self.peek() in ('+', '-'):
            op = self.eat()
            e = ('add' if op == '+' else 'sub', e, self.atom_expr())
        return e

    def cond_atom(self):
        if self.peek() in ('can_access', 'has_tokens'):
            f = self.eat(); self.eat('('); a = self.eat(); self.eat(','); b = self.eat(); self.eat(')')
            return (f, a, b)
        lhs = self.expr()
        op = self.eat()
        rhs = self.expr()
        if op == '=' and rhs == ('var', 'MAGIC'):
            return ('isMagic', lhs)
        if op == '≥':
            return ('le', rhs, lhs)
        if op == '≤':
            return ('le', lhs, rhs)
        sys.exit(f"transcribe: REFUSED, an unknown relation {op!r}")

    def cond(self):
        c = self.cond_atom()
        if self.peek() == '∧':
            self.eat()
            return ('and', c, self.cond())   # right-associative, as A.3 writes the conjunction
        return c

    def binders(self):
        """`a, b, c.` -> [a, b, c] (consumes the dot)."""
        bs = [self.eat()]
        while self.peek() == ',':
            self.eat(); bs.append(self.eat())
        self.eat('.')
        return bs

    def is_binder_seg(self):
        j = self.i
        while j < len(self.t) and re.match(r"[A-Za-z_]", self.t[j]):
            j += 1
            if j < len(self.t) and self.t[j] == ',':
                j += 1
                continue
            return j < len(self.t) and self.t[j] == '.'
        return False

    def term(self):
        f = self.eat()
        if f == 'k' and self.peek() != '[':
            return ('hole', [])        # a bare term parameter (verify_acl's k)
        if f == 'k':
            self.eat('['); args = [self.eat()]
            while self.peek() == ';':
                self.eat(); args.append(self.eat())
            self.eat(']')
            return ('hole', args)
        self.eat('{')
        if f == 'guard':
            c = self.cond(); self.eat(';'); ok = self.term(); self.eat(';'); er = self.term(); self.eat('}')
            return ('guard', c, ok, er)
        if f in ('read_u32', 'advance', 'take'):
            b = self.eat(); self.eat(';'); e = self.expr(); self.eat(';'); (v,) = self.binders(); k = self.term(); self.eat('}')
            return (f, b, e, v, k)
        if f == 'let_lin':
            self.eat('dec_tokens'); self.eat('('); a = self.eat(); self.eat(','); b = self.eat(); self.eat(')'); self.eat(';')
            (v,) = self.binders(); k = self.term(); self.eat('}')
            return ('letLinDec', a, b, v, k)
        if f == 'return':
            self.eat('('); a = self.eat(); self.eat(','); b = self.eat(); self.eat(')'); self.eat('}')
            return ('ret', a, b)
        if f == 'drop':
            c = self.eat(); self.eat('}')
            return ('drop', c)
        # a spec call: f{arg; …; [binders.] term} or f{arg; …; arg}
        args = []
        while True:
            if self.is_binder_seg():
                bs = self.binders(); body = self.term(); self.eat('}')
                return ('call', f, args, bs, body)
            if re.match(r"[A-Za-z_]", self.peek() or '') and self.peek(1) == '{':
                body = self.term(); self.eat('}')
                return ('call', f, args, None, body)
            args.append(self.eat())
            if self.peek() == '}':
                self.eat()
                return ('call', f, args, None, None)
            self.eat(';')


def parse_term(s):
    p = P(lex(s))
    t = p.term()
    if p.peek() is not None:
        sys.exit(f"transcribe: REFUSED, trailing tokens {p.t[p.i:p.i+5]}")
    return t


def parse_head(h):
    """`name{formals; [binders.] k[...]}` or `name{a; b; k}` or `NAME` -> (name, formals, binders|None, termparam|None)."""
    p = P(lex(h))
    name = p.eat()
    if p.peek() is None:
        return name, [], None, None
    p.eat('{')
    formals = []
    while True:
        if p.is_binder_seg():
            bs = p.binders(); p.term(); p.eat('}')
            return name, formals, bs, None
        x = p.eat()
        if p.peek() == '}':
            p.eat()
            if x == 'k':
                return name, formals, None, 'k'
            return name, formals + [x], None, None
        formals.append(x); p.eat(';')


# ---------------------------------------------------------------- expansion
def subst(t, m):
    """Rename free variables by m (binders shadow)."""
    if isinstance(t, str):
        return m.get(t, t)
    tag = t[0]
    if tag in ('read_u32', 'advance', 'take'):
        _, b, e, v, k = t
        m2 = {a: c for a, c in m.items() if a != v}
        return (tag, subst(b, m), subst_e(e, m), v, subst(k, m2))
    if tag == 'letLinDec':
        _, a, b, v, k = t
        m2 = {x: c for x, c in m.items() if x != v}
        return (tag, subst(a, m), subst(b, m), v, subst(k, m2))
    if tag == 'guard':
        return ('guard', subst_c(t[1], m), subst(t[2], m), subst(t[3], m))
    if tag == 'ret':
        return ('ret', subst(t[1], m), subst(t[2], m))
    if tag == 'drop':
        return t
    if tag == 'hole':
        return ('hole', [subst(a, m) for a in t[1]])
    if tag == 'call':
        _, f, args, bs, body = t
        m2 = {x: c for x, c in m.items() if not bs or x not in bs}
        return ('call', f, [subst(a, m) for a in args], bs, subst(body, m2) if body is not None else None)
    sys.exit(f"transcribe: internal, subst on {tag}")


def subst_e(e, m):
    if e[0] == 'var':
        return ('var', m.get(e[1], e[1]))
    if e[0] == 'len':
        return ('len', m.get(e[1], e[1]))
    if e[0] == 'lit':
        return e
    return (e[0], subst_e(e[1], m), subst_e(e[2], m))


def subst_c(c, m):
    if c[0] in ('can_access', 'has_tokens'):
        return (c[0], m.get(c[1], c[1]), m.get(c[2], c[2]))
    if c[0] == 'isMagic':
        return ('isMagic', subst_e(c[1], m))
    if c[0] == 'le':
        return ('le', subst_e(c[1], m), subst_e(c[2], m))
    return ('and', subst_c(c[1], m), subst_c(c[2], m))


def fill_hole(t, fill):
    """Replace the hole k[...] (or a bare `k` term parameter) by fill(args)."""
    if isinstance(t, str):
        return t
    tag = t[0]
    if tag == 'hole':
        return fill(t[1])
    if tag == 'call' and t[1] == 'k' and t[4] is None:
        return fill([])
    if tag in ('read_u32', 'advance', 'take'):
        return (tag, t[1], t[2], t[3], fill_hole(t[4], fill))
    if tag == 'letLinDec':
        return (tag, t[1], t[2], t[3], fill_hole(t[4], fill))
    if tag == 'guard':
        return ('guard', t[1], fill_hole(t[2], fill), fill_hole(t[3], fill))
    if tag == 'call':
        return ('call', t[1], t[2], t[3], fill_hole(t[4], fill) if t[4] is not None else None)
    return t


def expand(t, specs):
    if isinstance(t, str):
        return t
    tag = t[0]
    if tag == 'call':
        _, f, args, bs, body = t
        if f not in specs:
            sys.exit(f"transcribe: REFUSED, an undefined spec {f!r}")
        formals, dbs, tparam, dbody = specs[f]
        m = dict(zip(formals, args))
        if len(formals) != len(args):
            sys.exit(f"transcribe: REFUSED, {f} takes {len(formals)} args, given {len(args)}")
        inst = subst(dbody, m)
        if dbs is not None:      # a binder continuation: k[a; b; …] := body[bs := a, b, …]
            inst = fill_hole(inst, lambda actual: expand(subst(body, dict(zip(bs, actual))), specs))
        elif tparam is not None:  # a term parameter
            inst = fill_hole(inst, lambda _: expand(body, specs))
        return expand(inst, specs)
    if tag in ('read_u32', 'advance', 'take', 'letLinDec'):
        return t[:-1] + (expand(t[-1], specs),)
    if tag == 'guard':
        return ('guard', t[1], expand(t[2], specs), expand(t[3], specs))
    return t


# ---------------------------------------------------------------- emission (the declared translation table)
CODES = {'ERR_TRUNCATED_FRAME': '.truncated', 'ERR_UNAUTHORIZED_OR_RATE_LIMITED': '.unauthOrRate', 'ERR_BAD_PAYLOAD': '.badPayload'}
RENAME = {'bucket_st': 'st'}   # I4: `bucket_st` is the state argument


def nm(x):
    return RENAME.get(x, x)


def ix(e, prog):
    if prog == 1:
        if e[0] != 'lit':
            sys.exit("transcribe: REFUSED, program 1's indices are literals")
        return str(e[1])
    if e[0] == 'lit':
        return f'(.lit {e[1]})'
    if e[0] == 'var':
        return f'(.var {nm(e[1])})'
    if e[0] == 'len':
        return f'(.len {nm(e[1])})'
    if e[0] == 'add':
        return f'(.add {ix(e[1], prog)} {ix(e[2], prog)})'
    if e[0] == 'sub' and e[2][0] == 'lit':
        return f'(.sub {ix(e[1], prog)} {e[2][1]})'
    sys.exit(f"transcribe: REFUSED, an index form {e}")


def cond(c, prog):
    if c[0] == 'and':
        return f'(.and {cond(c[1], prog)} {cond(c[2], prog)})'
    if c[0] == 'can_access':
        return f'(.canAcc {nm(c[1])} {nm(c[2])})'
    if c[0] == 'has_tokens':
        return f'(.hasTok {nm(c[1])} {nm(c[2])})'
    if c[0] == 'isMagic':
        return f'(.isMagic {nm(c[1][1])})'
    if c[0] == 'le':
        if prog == 1:   # program 1's deep Cond has only `lenGe b k` (k ≤ len b)
            if c[1][0] == 'lit' and c[2][0] == 'len':
                return f'(.lenGe {nm(c[2][1])} {c[1][1]})'
            sys.exit("transcribe: REFUSED, program 1 allows only len(b) ≥ k")
        return f'(.le {ix(c[1], prog)} {ix(c[2], prog)})'
    sys.exit(f"transcribe: REFUSED, a condition {c}")


def emit(t, prog):
    tag = t[0]
    if tag == 'guard':
        return f'(.guard {cond(t[1], prog)} {emit(t[2], prog)} {emit(t[3], prog)})'
    if tag == 'read_u32':
        if t[2][0] != 'lit':
            sys.exit("transcribe: REFUSED, a read offset must be a literal")
        return f'(.readU32 {nm(t[1])} {t[2][1]} fun {t[3]} => {emit(t[4], prog)})'
    if tag == 'advance':
        return f'(.advance {nm(t[1])} {ix(t[2], prog)} fun {t[3]} => {emit(t[4], prog)})'
    if tag == 'take':
        return f'(.take {nm(t[1])} {ix(t[2], prog)} fun {t[3]} => {emit(t[4], prog)})'
    if tag == 'letLinDec':
        return f'(.letLinDec {nm(t[1])} {nm(t[2])} fun {t[3]} => {emit(t[4], prog)})'
    if tag == 'ret':
        return f'(.ret {nm(t[1])} {nm(t[2])})'
    if tag == 'drop':
        if t[1] not in CODES:
            sys.exit(f"transcribe: REFUSED, an unknown code {t[1]}")
        return f'(.drop {CODES[t[1]]})'
    sys.exit(f"transcribe: REFUSED, an unexpanded form {tag}")


def specs_of(blocks):
    sp = {}
    for blk in blocks:
        for h, b in defs(blk):
            name, formals, bs, tparam = parse_head(h)
            sp[name] = (formals, bs, tparam, parse_term(b))
    return sp


def main():
    mutate = '--mutate' in sys.argv and sys.argv[sys.argv.index('--mutate') + 1]
    out = sys.argv[sys.argv.index('--out') + 1] if '--out' in sys.argv else os.path.join(ROOT, 'lean', 'VIRB', 'Transcribe.lean')
    r1 = os.path.join(ROOT, 'inputs', 'router-inputs.md')
    r2 = os.path.join(ROOT, 'inputs', 'program2-inputs.md')
    I2 = md_block(r1, '## I2.')
    I3 = md_block(r1, '## I3.')
    J2 = md_block(r2, '## J2.')
    J3 = md_block(r2, '## J3.')
    J4 = md_block(r2, '## J4.')
    F_text = a3_F()
    if mutate == 'read-offset':   # a planted transcription error: F's sender read at 8 instead of 4
        F_text, n = re.subn(r'read_u32\{ b0; 4; sender', 'read_u32{ b0; 8; sender', F_text)
        if n != 1:
            sys.exit("transcribe: the mutant did not apply exactly once")
    if mutate == 'spec-offset':   # a planted error in a SPEC body: I2's topic read at 12 instead of 8 (reaches U only through expansion)
        I2, n = re.subn(r'read_u32\{ b0; 8; topic\.', 'read_u32{ b0; 12; topic.', I2)
        if n != 1:
            sys.exit("transcribe: the mutant did not apply exactly once")
    p1 = specs_of([I2])
    p2 = dict(p1); p2.update(specs_of([J2]))
    U = expand(parse_term(defs(I3)[0][1]), p1)
    F = parse_term(strip_comments(F_text))
    U2 = expand(parse_term(defs(J3)[0][1]), p2)
    F2 = parse_term(defs(J4)[0][1])
    rows = [('tc_U', 'VIR.Deep', 'U', emit(U, 1)), ('tc_F', 'VIR.Deep', 'F', emit(F, 1)),
            ('tc_U2', 'VIR.Deep2', 'U2', emit(U2, 2)), ('tc_F2', 'VIR.Deep2', 'F2', emit(F2, 2))]
    with open(out, 'w', encoding='utf-8') as f:
        f.write('/-\n  GENERATED by harness/transcribe_lean.py' + (f' (MUTANT: {mutate})' if mutate else '') +
                ' — never edited by hand. The A.2 transcription check (amend-10 B4):\n'
                '  each term parsed from the object or the inputs AS WRITTEN, `rfl`-equal to the hand-written deep term.\n-/\n'
                'import VIR.Deep\nimport VIR.Deep2\n\nnamespace VIR.Transcribe\n\n')
        for name, ns, target, term in rows:
            f.write(f'theorem {name} {{V : Type}} (b0 st : V) :\n    ({term} : {ns}.Tm V) = {ns}.{target} b0 st := rfl\n\n')
        f.write('end VIR.Transcribe\n')
    print(f"transcribe: wrote {len(rows)} checks to {os.path.relpath(out, ROOT)}" + (f" (MUTANT {mutate})" if mutate else ''))
    print("LIMITS: equality up to rfl (definitional unfolding), not characters; the forms/conditions/codes table is "
          "written once here by hand; spec bodies are checked only through their expansion into U and U2.")


if __name__ == '__main__':
    main()
