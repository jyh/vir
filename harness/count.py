#!/usr/bin/env python3
"""vir harness: the counts C1-C6 of predictions/PREDICTIONS.md, computed from an arm's ARTIFACTS alone.

usage: count.py --arm lean|metaprl DIR        prints one line per count:  ARM Cn VALUE STATE  (tab-separated)
       STATE is MEASURED, EMPTY (the arm has no artifact of that kind yet; VALUE is 0), or UNMEASURED (no extractor yet).

Artifacts the LEAN arm leaves (lean/ in this tree, built only by ../saltbuild.sh):
  out/terms.txt     `#print` of every theorem on the I4 path (elaborated terms)   -> C1
  out/axioms.txt    `#print axioms` output                                      -> C4
  VIR/**/*.lean     sources: theorems named aux_* are AUX RULES                 -> C3, C5
  logs/*.log        saltbuild logs, one per invocation (carry `saltbuild EXIT=`) -> C6
The METAPRL arm's artifact names are fixed with mojave (STATUS-vir row 6); until then only C5 is read (*.ml / *.mli).
C2 has no extractor on either side until mojave's census label is known: it prints UNMEASURED, never 0.
"""
import argparse, os, re, sys

# C1: the token class fixed in PREDICTIONS.md (elaborated-term spellings).
CAST_RE = re.compile(r'(?<![A-Za-z0-9_.])(HEq|cast|Eq\.mpr|Eq\.rec|heq_of_eq|eq_rec|Eq\.ndrec|Nat\.sub_sub)(?![A-Za-z0-9_])|▸|≍')  # ≍ = HEq's notation
STD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
AUX_RE = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\s+(?:[A-Za-z0-9_.]*\.)?aux_[A-Za-z0-9_]*', re.M)


AUX_NAME_RE = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\s+(?:[A-Za-z0-9_.]*\.)?(aux_[A-Za-z0-9_]*)', re.M)
DECL_RE = re.compile(r'^(?:/-[\s\S]*?-/\s*)?(?:@\[[^\]]*\]\s*)?(?:theorem|lemma|def|structure|inductive|instance|abbrev)\b', re.M)


def blocks(text):
    starts = [m.start() for m in re.finditer(r'^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma|def|structure|inductive|instance|abbrev)\b', text, re.M)]
    starts.append(len(text))
    return [text[a:b] for a, b in zip(starts, starts[1:])]


def strip_shortcuts(text):
    # a theorem named *_casesplit is a recorded SHORTCUT (inputs I7) and is never scored
    return ''.join(b for b in blocks(text) if not re.match(r'(?:@\[[^\]]*\]\s*)?theorem\s+\S*_casesplit\b', b))


def scored_body(text):
    # the scored I4 proof: the theorem named router_fusion
    for b in blocks(text):
        if re.match(r'(?:@\[[^\]]*\]\s*)?theorem\s+(?:\S*\.)?router_fusion\b', b):
            return b
    return ''


def chain_tokens(block):
    # C5chain (row 10, one unit for both arms): whitespace tokens of the scored chain's proof script,
    # comments dropped; Lean: the text after the first `:= by`; MetaPRL: the c2-router.mp lines that `refine`
    if ':= by' in block:
        block = block.split(':= by', 1)[1]
    block = re.sub(r'/-[\s\S]*?-/|--[^\n]*', '', block)
    return len(block.split())


def read(p):
    with open(p, 'rb') as f:
        return f.read().decode('utf-8', 'replace')


def files(d, exts):
    out = []
    for root, _, names in os.walk(d):
        for n in sorted(names):
            if n.endswith(exts):
                out.append(os.path.join(root, n))
    return sorted(out)


def lean(d):
    rows = []
    t = os.path.join(d, 'out', 'terms.txt')
    if os.path.isfile(t):
        tt = read(t)
        rows.append(('C1', len(CAST_RE.findall(tt)), 'MEASURED'))
        # split (amend-4): the slice_fuse path (slice_fuse and the Slice.* lemmas it uses) vs the rest
        tb = re.split(r'\n(?=(?:@\[[^\]]*\]\s*)?theorem\s)', tt)
        def cnt(pat):
            return sum(len(CAST_RE.findall(b)) for b in tb if re.match(r'(?:@\[[^\]]*\]\s*)?theorem\s+' + pat, b))
        fl = cnt(r'\S*\.Flat\.')                      # L-FLAT control (P1b)
        sl = cnt(r'(?!\S*\.Flat\.)\S*(slice_fuse|\.Slice\.)')   # L-IDX slice_fuse path (P1)
        rows += [('C1slice', sl, 'MEASURED'), ('C1flat', fl, 'MEASURED'), ('C1rest', len(CAST_RE.findall(tt)) - sl - fl, 'MEASURED')]
        # amend-5 C1heq per program path: P1 = slice_fuse + Slice.heq_of/congr_heq/adv_adv_heq; P2 = slice_fuse_dep + congr_heq_dep + aux_advance_idx + heq_of/adv_adv_heq
        HEQ = re.compile(r'(?<![A-Za-z0-9_.])(HEq|heq_of_eq)(?![A-Za-z0-9_])|≍')
        def heq(names):
            return sum(len(HEQ.findall(b)) for b in tb if re.match(r'(?:@\[[^\]]*\]\s*)?theorem\s+VIR\.(' + names + r')\s', b))
        rows += [('C1heq', heq(r'slice_fuse|Slice\.heq_of|Slice\.congr_heq|Slice\.adv_adv_heq'), 'MEASURED'),
                 ('P2.C1heq', heq(r'slice_fuse_dep|Slice\.congr_heq_dep|aux_advance_idx|Slice\.heq_of|Slice\.adv_adv_heq'), 'MEASURED')]
    else:
        rows.append(('C1', 0, 'EMPTY'))
    src = files(os.path.join(d, 'VIR'), ('.lean',))
    text = ''.join(read(p) for p in src)
    scored = strip_shortcuts(text)
    if src:
        # C2 (provisional extractor, written after the Lean arm's first green; amend-4): term-mode side proofs.
        # cond = the hypotheses a conditional rule demands at its use inside the scored I4 proof; wf = all others.
        side = len(re.findall(r'\(by |\bby have[^\n]*omega', scored))
        body = scored_body(scored)
        cond = len(re.findall(r'\(by ', body))
        rows += [('C2wf', side - cond, 'MEASURED'), ('C2cond', cond, 'MEASURED'), ('C2', side, 'MEASURED')]
        declared = set(m.group(1) for m in AUX_NAME_RE.finditer(text))
        used = {a for a in declared if re.search(r'(?<![A-Za-z0-9_])' + re.escape(a) + r'(?![A-Za-z0-9_])', body)}
        rows += [('C3', len(used), 'MEASURED'), ('C3declared', len(declared), 'MEASURED')]
        rows.append(('C5chain', chain_tokens(body), 'MEASURED'))
        # PROGRAM 2 (predictions-program2): the scored chain is router2_fusion
        b2 = next((b for b in blocks(scored) if re.match(r'theorem\s+router2_fusion\b', b)), '')
        if b2:
            u2 = {a for a in declared if re.search(r'(?<![A-Za-z0-9_])' + re.escape(a) + r'(?![A-Za-z0-9_])', b2)}
            rows += [('P2.C3', len(u2), 'MEASURED'), ('P2.C2cond', len(re.findall(r'\(by ', b2)), 'MEASURED'),
                     ('P2.C5chain', chain_tokens(b2), 'MEASURED')]
        # L-DEEP (row 9): aux rules are constructors of Step; used = referenced in router_fusion_deep_steps
        dblk = next((b for b in blocks(scored) if re.match(r'theorem\s+router_fusion_deep_steps\b', b)), '')
        if dblk:
            dec = set(re.findall(r'^\s*\|\s*(aux_[A-Za-z0-9_]*)', text, re.M))
            giv = set(re.findall(r'^\s*\|\s*(slice_fuse|guard_merge|read_comm|beta_lin|dce_atom|const_fold|guard_true)\b', text, re.M))
            u = {a for a in dec if re.search(r'\.' + a + r'\b', dblk)}
            g = {a for a in giv if re.search(r'\.' + a + r'\b', dblk)}
            rows += [('C3deep', len(u), 'MEASURED'), ('C3deepGivenUsed', len(g), 'MEASURED'), ('C5chainDeep', chain_tokens(dblk), 'MEASURED'),
                     ('C2deepCond', len(re.findall(r'\(by ', dblk)), 'MEASURED')]
    else:
        rows += [('C2', 0, 'EMPTY'), ('C3', 0, 'EMPTY')]
    a = os.path.join(d, 'out', 'axioms.txt')
    if os.path.isfile(a):
        found = set()
        for m in re.finditer(r'\[([^\]]*)\]', read(a)):
            found |= {x.strip() for x in m.group(1).split(',') if x.strip()}
        rows.append(('C4', len(found - STD_AXIOMS), 'MEASURED'))
    else:
        rows.append(('C4', 0, 'EMPTY'))
    rows += size(src)
    logs = files(os.path.join(d, 'logs'), ('.log',))
    n = sum(len(re.findall(r'^saltbuild EXIT=\d+', read(p), re.M)) for p in logs)
    rows.append(('C6', n, 'MEASURED') if logs else ('C6', 0, 'EMPTY'))
    return rows


def size(src):
    if not src:
        return [('C5', 0, 'EMPTY')]
    lines = toks = 0
    for p in src:
        for ln in read(p).splitlines():
            if ln.strip():
                lines += 1
                toks += len(ln.split())
    return [('C5', lines, 'MEASURED'), ('C5tok', toks, 'MEASURED')]


FORM_UNFOLD_RE = re.compile(r'(?<![A-Za-z0-9_])unfold_(read_u32|vguard|guard|advance|let_lin|let_atom|vreturn|vdrop)(?![A-Za-z0-9_])')


def metaprl(d, sfx=''):
    """d = the arm's root holding vir-metaprl/ (theory) and vir-arm-tools/ (scripts, driver runs).
    The extractor names were agreed with mojave @[bus] (STATUS-vir row 6)."""
    th = os.path.join(d, 'vir-metaprl', 'theories', 'vir', 'vir' + sfx + '.ml')
    tools = os.path.join(d, 'vir-arm-tools')
    if not os.path.isfile(th):
        return [(c, 0, 'EMPTY') for c in ('C1', 'C2', 'C3', 'C4', 'C5', 'C6')]
    rows = []
    steps = files(os.path.join(tools, 'steps'), ('.mp',))
    rows.append(('C1', sum(len(CAST_RE.findall(read(p))) for p in steps), 'MEASURED'))
    # C2: indented child-goal labels in the per-step C2 replays (amend-1: wf / equality / any premise of a conditional rule)
    lab = {'wf': 0, 'equality': 0, 'assertion': 0}
    for f in (('runs-c2-router.txt', 'runs-c2-lemmas.txt') if not sfx else ('runs-c2-router' + sfx + '.txt',)):
        fp = os.path.join(tools, f)
        if os.path.isfile(fp):
            for m in re.finditer(r'^[ \t]+\.\.\.\.(wf|equality|assertion)\.\.\.\.', read(fp), re.M):
                lab[m.group(1)] += 1
    # GENERATED convention (row 12): mpdrive's `=== CHILDREN k: <labels>` line (direct children of each refine; mojave c7df66d)
    gen = {'wf': 0, 'equality': 0, 'assertion': 0}; have_children = False
    for f in (('runs-c2-router.txt', 'runs-c2-lemmas.txt') if not sfx else ('runs-c2-router' + sfx + '.txt',)):
        fp = os.path.join(tools, f)
        if os.path.isfile(fp):
            for m in re.finditer(r'^=== CHILDREN \d+:(.*)$', read(fp), re.M):
                have_children = True
                for w in m.group(1).split():
                    if w in gen:
                        gen[w] += 1
    if have_children:
        rows += [('C2genWf', gen['wf'], 'MEASURED'), ('C2genEq', gen['equality'], 'MEASURED'),
                 ('C2genCond', gen['assertion'], 'MEASURED'), ('C2gen', sum(gen.values()), 'MEASURED')]
    rows += [('C2wf', lab['wf'], 'MEASURED'), ('C2eq', lab['equality'], 'MEASURED'),
             ('C2cond', lab['assertion'], 'MEASURED'), ('C2', sum(lab.values()), 'MEASURED')]
    # C3: aux rules USED by the scored chain script, plus A.2-form unfolds (amend-3)
    ml = read(th)
    if sfx:   # program 2's module imports program 1's, where the aux rules are declared
        base = os.path.join(d, 'vir-metaprl', 'theories', 'vir', 'vir.ml')
        if os.path.isfile(base):
            ml = read(base) + '\n' + ml
    declared = set(re.findall(r'^\s*interactive(?:_rw)?\s+(aux_[A-Za-z0-9_]*)', ml, re.M))
    chain = os.path.join(tools, 'steps', 'c2-router' + sfx + '.mp')
    body = read(chain) if os.path.isfile(chain) else ''
    used = {a for a in declared if re.search(r'(?<![A-Za-z0-9_])' + re.escape(a) + r'(?![A-Za-z0-9_])', body)}
    forms = set(m.group(1) for m in FORM_UNFOLD_RE.finditer(body))
    rows += [('C3', len(used) + len(forms), 'MEASURED'), ('C3strict', len(used), 'MEASURED'), ('C3declared', len(declared), 'MEASURED')]
    rows.append(('C4', len(re.findall(r'^\s*prim(?:_rw)?\s', ml, re.M)), 'MEASURED'))
    rows.append(('C5', 0, 'UNMEASURED'))   # mojave measures the stored tactic text in vir.prla; no extractor yet
    rows.append(('C5chain', len(' '.join(l for l in body.splitlines() if l.strip().startswith('refine')).split()), 'MEASURED'))
    runs = [p for p in files(tools, ('.txt',)) if re.search(r'/runs-\d+\.txt$', p)]
    refines = sum(len(re.findall(r'^=== STEP .*:: refine', read(p), re.M)) for p in runs)
    rows += [('C6sessions', len(runs), 'MEASURED'), ('C6refines', refines, 'MEASURED')]
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--arm', required=True, choices=['lean', 'metaprl'])
    ap.add_argument('--program', default='1', choices=['1', '2'])
    ap.add_argument('dir')
    a = ap.parse_args()
    rows = lean(a.dir) if a.arm == 'lean' else metaprl(a.dir, '' if a.program == '1' else a.program)
    for c, v, s in rows:
        print(f'{a.arm}\t{c}\t{v}\t{s}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
