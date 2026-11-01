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
    block = re.split(r'^end\b', block, flags=re.M)[0]   # a file-final proof ends at its namespace's `end`
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


# ROW 19: each program's DECLARED file set. Whole-tree rows move whenever a file is added; the `.scoped` rows do not.
# Variants (Flat, Deep*, Router2Z, Exit*) are in no program's scope: they are scored only by their own rows.
PROGRAM_FILES = {'1': ('Core.lean', 'Rules.lean', 'Router.lean'),
                 '2': ('Core.lean', 'Rules.lean', 'Router.lean', 'Router2.lean'),
                 '3': ('Core.lean', 'Rules.lean', 'Router.lean', 'Router2.lean', 'Router3.lean')}


def lean(d, prog='1'):
    rows = []
    t = os.path.join(d, 'out', 'terms.txt')
    if os.path.isfile(t):
        tt = read(t)
        # split (amend-4): the slice_fuse path (slice_fuse and the Slice.* lemmas it uses) vs the rest
        tball = re.split(r'\n(?=(?:@\[[^\]]*\]\s*)?theorem\s)', tt)
        # ROW 15: the Int-offset VARIANT's prints (VIR.Z.*) are scored only by their own P2Z rows, never in the arm's pool
        tb = [b for b in tball if not re.match(r'(?:@\[[^\]]*\]\s*)?theorem\s+VIR\.Z\.', b)]
        rows.append(('C1', sum(len(CAST_RE.findall(b)) for b in tb), 'MEASURED'))
        def cnt(pat):
            return sum(len(CAST_RE.findall(b)) for b in tb if re.match(r'(?:@\[[^\]]*\]\s*)?theorem\s+' + pat, b))
        fl = cnt(r'\S*\.Flat\.')                      # L-FLAT control (P1b)
        sl = cnt(r'(?!\S*\.Flat\.)\S*(slice_fuse|\.Slice\.)')   # L-IDX slice_fuse path (P1)
        rows += [('C1slice', sl, 'MEASURED'), ('C1flat', fl, 'MEASURED'), ('C1rest', sum(len(CAST_RE.findall(b)) for b in tb) - sl - fl, 'MEASURED')]
        # amend-5 C1heq per program path: P1 = slice_fuse + Slice.heq_of/congr_heq/adv_adv_heq; P2 = slice_fuse_dep + congr_heq_dep + aux_advance_idx + heq_of/adv_adv_heq
        COE_RE = re.compile(r'↑|(?<![A-Za-z0-9_])Subtype\.val(?![A-Za-z0-9_])|(?<!Subtype)\.val(?![A-Za-z0-9_])|\.property(?![A-Za-z0-9_])')   # program 3 (PREDICTIONS-program3)
        HEQ = re.compile(r'(?<![A-Za-z0-9_.])(HEq|heq_of_eq)(?![A-Za-z0-9_])|≍')
        def heq(names):
            return sum(len(HEQ.findall(b)) for b in tball if re.match(r'(?:@\[[^\]]*\]\s*)?theorem\s+VIR\.(' + names + r')\s', b))
        rows += [('C1heq', heq(r'slice_fuse|Slice\.heq_of|Slice\.congr_heq|Slice\.adv_adv_heq'), 'MEASURED'),
                 ('P2.C1heq', heq(r'slice_fuse_dep|Slice\.congr_heq_dep|aux_advance_idx|Slice\.heq_of|Slice\.adv_adv_heq'), 'MEASURED'),
                 ('C1heqFlat', heq(r'Flat\.[A-Za-z0-9_.]+'), 'MEASURED'),
                 ('P2Z.C1heq', heq(r'Z\.slice_fuse_dep|Z\.SliceZ\.congr_heq_dep|Z\.aux_advance_idx|Z\.SliceZ\.heq_of|Z\.SliceZ\.adv_adv_heq'), 'MEASURED')]
        b3t = [b for b in tball if re.match(r'(?:@\[[^\]]*\]\s*)?theorem\s+VIR\.route_acl_safe\s', b)]
        b3f = [b for b in tball if re.match(r'(?:@\[[^\]]*\]\s*)?theorem\s+VIR\.route_acl_safe_flat\s', b)]
        if b3f:   # amend-9: the L-FLAT control for program 3
            rows += [('P3F.C1coe', sum(len(COE_RE.findall(b)) for b in b3f), 'MEASURED')]
        if b3t:   # program 3: EMPTY until the theorem is printed, never a 0 that reads as T1 falsified
            rows += [('P3.C1heq', heq(r'route_acl_safe'), 'MEASURED'), ('P3.C1coe', sum(len(COE_RE.findall(b)) for b in b3t), 'MEASURED')]
        else:
            rows += [('P3.C1coe', 0, 'EMPTY')]
    else:
        rows.append(('C1', 0, 'EMPTY'))
    src = files(os.path.join(d, 'VIR'), ('.lean',))
    # a sentinel decl between files, so a file-final block never absorbs the next file's header (2nd vir head, row 25)
    text = '\ndef vir_file_boundary : Nat := 0\n'.join(read(p) for p in src)
    scored = strip_shortcuts(text)
    if src:
        # C2 (provisional extractor, written after the Lean arm's first green; amend-4): term-mode side proofs.
        # cond = the hypotheses a conditional rule demands at its use inside the scored I4 proof; wf = all others.
        side = len(re.findall(r'\(by |\bby have[^\n]*omega', scored))
        body = scored_body(scored)
        cond = len(re.findall(r'\(by ', body))
        rows += [('C2wf', side - cond, 'MEASURED'), ('C2cond', cond, 'MEASURED'), ('C2', side, 'MEASURED')]
        # P2's Lean figure (9) was read when VIR/ held only program 1's files; this row reproduces it as the tree grows
        p1 = [p for p in src if os.path.basename(p) in ('Core.lean', 'Rules.lean', 'Router.lean')]
        if len(p1) == 3:
            s1 = strip_shortcuts(''.join(read(p) for p in p1))
            rows.append(('C2.p1files', len(re.findall(r'\(by |\bby have[^\n]*omega', s1)), 'MEASURED'))
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
        # PROGRAM 3 (PREDICTIONS-program3, fixed before any proof): the scored theorem is route_acl_safe
        b3 = next((b for b in blocks(scored) if re.match(r'theorem\s+route_acl_safe\b', b)), '')
        if b3:
            u3 = {a for a in declared if re.search(r'(?<![A-Za-z0-9_])' + re.escape(a) + r'(?![A-Za-z0-9_])', b3)}
            rows += [('P3.C3', len(u3), 'MEASURED'), ('P3.C2cond', len(re.findall(r'\(by ', b3)), 'MEASURED'),
                     ('P3.C5chain', chain_tokens(b3), 'MEASURED')]
        b3d = next((b for b in blocks(scored) if re.match(r'theorem\s+route_acl_safe_deep\b', b)), '')
        if b3d:   # row 26, exploratory (no prediction pinned)
            rows += [('P3D.C5chain', chain_tokens(b3d), 'MEASURED'), ('P3D.C2cond', len(re.findall(r'\(by ', b3d)), 'MEASURED')]
        b3s = next((b for b in blocks(scored) if re.match(r'theorem\s+route_acl_safe_flat\b', b)), '')
        if b3s:
            rows += [('P3F.C5chain', chain_tokens(b3s), 'MEASURED'), ('P3F.ctxCleared', len(re.findall(r'\bclear\s', b3s)), 'MEASURED')]
        # ROW 15 (amend-7): the Int-offset variant's scored chain, router2z_fusion
        bz = next((b for b in blocks(scored) if re.match(r'theorem\s+router2z_fusion\b', b)), '')
        if bz:
            uz = {a for a in declared if re.search(r'(?<![A-Za-z0-9_])' + re.escape(a) + r'(?![A-Za-z0-9_])', bz)}
            rows += [('P2Z.C3', len(uz), 'MEASURED'), ('P2Z.C2cond', len(re.findall(r'\(by ', bz)), 'MEASURED'),
                     ('P2Z.C5chain', chain_tokens(bz), 'MEASURED'),
                     ('P2Z.ctxCleared', len(re.findall(r'\bclear\s', bz)), 'MEASURED')]
        # L-DEEP (row 9): aux rules are constructors of Step; used = referenced in router_fusion_deep_steps
        dblk = next((b for b in blocks(scored) if re.match(r'theorem\s+router_fusion_deep_steps\b', b)), '')
        if dblk:
            dec = set(re.findall(r'^\s*\|\s*(aux_[A-Za-z0-9_]*)', text, re.M))
            giv = set(re.findall(r'^\s*\|\s*(slice_fuse|guard_merge|read_comm|beta_lin|dce_atom|const_fold|guard_true)\b', text, re.M))
            u = {a for a in dec if re.search(r'\.' + a + r'\b', dblk)}
            g = {a for a in giv if re.search(r'\.' + a + r'\b', dblk)}
            rows += [('C3deep', len(u), 'MEASURED'), ('C3deepGivenUsed', len(g), 'MEASURED'), ('C5chainDeep', chain_tokens(dblk), 'MEASURED'),
                     ('C2deepCond', len(re.findall(r'\(by ', dblk)), 'MEASURED')]
        # L-DEEP PROGRAM 2 (row 13): the same reading over router2_fusion_deep_steps (VIR.Deep2.Step)
        d2 = next((b for b in blocks(scored) if re.match(r'theorem\s+router2_fusion_deep_steps\b', b)), '')
        if d2:
            dec = set(re.findall(r'^\s*\|\s*(aux_[A-Za-z0-9_]*)', text, re.M))
            giv = set(re.findall(r'^\s*\|\s*(slice_fuse|guard_merge|read_comm|beta_lin|dce_atom|const_fold|guard_true)\b', text, re.M))
            u = {a for a in dec if re.search(r'\.' + a + r'\b', d2)}
            g = {a for a in giv if re.search(r'\.' + a + r'\b', d2)}
            rows += [('P2.C3deep', len(u), 'MEASURED'), ('P2.C3deepGivenUsed', len(g), 'MEASURED'),
                     ('P2.C5chainDeep', chain_tokens(d2), 'MEASURED'), ('P2.C2deepCond', len(re.findall(r'\(by ', d2)), 'MEASURED'),
                     ('P2.ctxHolds', len(re.findall(r'\.mem\b', d2)), 'MEASURED')]
        # ROW 18 (amend-8): the own-conjunct variant's chain, router2s_fusion_deep_steps (VIR.Deep2S.StepS)
        ds = next((b for b in blocks(scored) if re.match(r'theorem\s+router2s_fusion_deep_steps\b', b)), '')
        if ds:
            dec = set(re.findall(r'^\s*\|\s*(aux_[A-Za-z0-9_]*)', text, re.M))
            u = {a for a in dec if re.search(r'\.' + a + r'\b', ds)}
            rows += [('P2S.C3deep', len(u), 'MEASURED'), ('P2S.ctxHolds', len(re.findall(r'\.mem\b', ds)), 'MEASURED'),
                     ('P2S.C2deepCond', len(re.findall(r'\(by ', ds)), 'MEASURED'), ('P2S.C5chainDeep', chain_tokens(ds), 'MEASURED')]
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
    sc = [p for p in src if os.path.basename(p) in PROGRAM_FILES[prog]]
    if len(sc) == len(PROGRAM_FILES[prog]):
        st = strip_shortcuts(''.join(read(p) for p in sc))
        sside = len(re.findall(r'\(by |\bby have[^\n]*omega', st))
        rows.append(('C2.scoped', sside, 'MEASURED'))
        rows += [(c + '.scoped', v, m) for c, v, m in size(sc)]
    else:
        rows.append(('C2.scoped', 0, 'EMPTY'))
    logs = files(os.path.join(d, 'logs'), ('.log',))
    n = sum(len(re.findall(r'^saltbuild EXIT=\d+', read(p), re.M)) for p in logs)
    rows.append(('C6', n, 'MEASURED') if logs else ('C6', 0, 'EMPTY'))
    rows.append(('C6.scope', 0, 'UNSCOPED'))   # build logs are not per-program; C6 stays whole-tree
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
    gen = {'wf': 0, 'equality': 0, 'assertion': 0}; have_children = False; off_path = {}
    wf_stmt = 0   # row 31 (EXPLORATORY, post-proof): wf children of a bare `refine (dT 0);;` = the statement's well-formedness
    for f in (('runs-c2-router.txt', 'runs-c2-lemmas.txt') if not sfx else ('runs-c2-router' + sfx + '.txt', 'runs-c2-lemmas.txt')):
        fp = os.path.join(tools, f)
        if os.path.isfile(fp):
            txt = read(fp)
            cmds = dict(re.findall(r'^=== STEP (\d+) \[[^\]]*\][^:]*:: (.*)$', txt, re.M))
            # PATH RULE (row 14): a lemma replay counts only for a lemma the program's scored chain USES.
            # The replay file switches lemma at `cd "/vir/vir/<name>"`; the router replay is the path itself.
            lemma_at = {}; cur = None
            for k in sorted(cmds, key=int):
                lm = re.match(r'cd "/vir/vir/([A-Za-z0-9_]+)"', cmds[k])
                if lm:
                    cur = lm.group(1)
                lemma_at[k] = cur
            chain_fp = os.path.join(tools, 'steps', 'c2-router' + sfx + '.mp')
            chain_txt = read(chain_fp) if os.path.isfile(chain_fp) else ''
            for m in re.finditer(r'^=== CHILDREN (\d+):(.*)$', txt, re.M):
                have_children = True
                # CLOSER residuals are not generated obligations (mojave @[bus]): a step that runs omegaT
                if 'omegaT' in cmds.get(m.group(1), ''):
                    continue
                if f == 'runs-c2-lemmas.txt':
                    lem = lemma_at.get(m.group(1))
                    if lem is None or not re.search(r'(?<![A-Za-z0-9_])' + re.escape(lem) + r'(?![A-Za-z0-9_])', chain_txt):
                        off_path[lem] = off_path.get(lem, 0) + sum(1 for w in m.group(2).split() if w in gen)
                        continue
                for w in m.group(2).split():
                    if w in gen:
                        gen[w] += 1
                        if w == 'wf' and re.fullmatch(r'refine \(dT 0\);;\s*', cmds.get(m.group(1), '')):
                            wf_stmt += 1
    if have_children:
        rows += [('C2genWf', gen['wf'], 'MEASURED'), ('C2genEq', gen['equality'], 'MEASURED'),
                 ('C2genCond', gen['assertion'], 'MEASURED'), ('C2gen', sum(gen.values()), 'MEASURED'),
                 ('C2genWf.stmt', wf_stmt, 'EXPLORATORY'), ('C2genWf.proof', gen['wf'] - wf_stmt, 'EXPLORATORY')]
        for lem, n in sorted((k or '?', v) for k, v in off_path.items()):
            rows.append(('C2genOffPath:' + lem, n, 'EXCLUDED'))
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
    rows += metaprl_c5(d, tools, sfx)
    rows.append(('C5chain', len(' '.join(l for l in body.splitlines() if l.strip().startswith('refine')).split()), 'MEASURED'))
    # C6 is PROGRAM-SCOPED (mojave @[bus]; ARM11): program 1's sessions are runs-NN.txt, program N's runs-pN-NN.txt.
    # Until 2026-11-01 (3rd vir head) --program 2/3 read program 1's files. This post-dates the proofs; C6 is no T-prediction.
    run_re = r'/runs-\d+\.txt$' if not sfx else r'/runs-p' + re.escape(sfx) + r'-\d+\.txt$'
    runs = [p for p in files(tools, ('.txt',)) if re.search(run_re, p)]
    refines = sum(len(re.findall(r'^=== STEP .*:: refine', read(p), re.M)) for p in runs)
    rows += [('C6sessions', len(runs), 'MEASURED'), ('C6refines', refines, 'MEASURED')]
    return rows


def metaprl_c5(d, tools, sfx):
    """C5 (rows 32, 34): mojave's MANIFEST vir-arm-tools/STORED.tsv (@[bus]; lemma rows @[bus]) names, per program,
    each stored script, its archive and its theorem. A theorem's block in a shared script runs from the `cd` naming it
    (`cd "/vir/vir/<t>"` or `cd "../<t>"`) to the next `cd`; a script with no such cd is taken whole.
    C5 = refine lines over every row of the program · C5tok = their whitespace tokens (C5chain's unit) · C5lex = LEXICAL
    tokens of each refine's argument (mojave's unit) · C5.inArchive = arguments found, whitespace-normalised, as a `String`
    node of the row's .prla · C5.main = refine lines of the program's FIRST row. Post-dates every proof; no direction."""
    man = os.path.join(tools, 'STORED.tsv')
    prog = sfx or '1'
    if not os.path.isfile(man):
        return [('C5', 0, 'UNMEASURED')]
    mrows = [f for f in (ln.split('\t') for ln in read(man).splitlines()[1:]) if len(f) >= 4 and f[0] == prog]
    if not mrows:
        return [('C5', 0, 'UNMEASURED')]
    norm = lambda t: ' '.join(t.split())
    lex = re.compile(r"[A-Za-z_][A-Za-z_0-9']*|\d+|<<|>>|[^\sA-Za-z_0-9]")
    lines_all, inarch, have_arch, main = [], 0, False, None
    for _, script, arch, thm in mrows:
        sp, ap = os.path.join(tools, script), os.path.join(d, arch)
        if not os.path.isfile(sp):
            return [('C5', 0, 'MISSING')]
        src = [l.strip() for l in read(sp).splitlines()]
        start = next((k for k, l in enumerate(src) if re.fullmatch(r'cd "(?:/vir/vir\d*/|\.\./)' + re.escape(thm) + r'";;', l)), None)
        if start is not None:
            # ends at the next cd naming ANOTHER theorem (`..`, `../<ident>`, `/vir/vir*/<other>`), never at a subgoal cd
            # (`cd "1"`, `cd "../2"`, `cd "/vir/vir3/<thm>/2/1"`) — those are inside the proof
            def other(l):
                m = re.fullmatch(r'cd "(.*)";;', l)
                if not m:
                    return False
                t = m.group(1)
                if t == '..':
                    return True
                m2 = re.fullmatch(r'\.\./([A-Za-z_][A-Za-z_0-9]*)', t) or re.fullmatch(r'/vir/vir\d*/([A-Za-z_][A-Za-z_0-9]*)(?:/.*)?', t)
                return bool(m2) and m2.group(1) != thm
            end = next((k for k in range(start + 1, len(src)) if other(src[k])), len(src))
            src = src[start:end]
        lines = [l for l in src if l.startswith('refine')]
        if main is None:
            main = len(lines)
        stored = set()
        if os.path.isfile(ap):
            have_arch = True
            # the archive QUOTES a string only when it must: `String "(dT 0)"` but `String (autoT)` and `String logicAutoT` bare
            stored = {norm(q if q else bare) for q, bare in re.findall(r'^P\t\S+\tString (?:"(.*)"|(\S+))$', read(ap), re.M)}
        inarch += sum(1 for l in lines if norm(re.sub(r';;\s*$', '', l)[len('refine'):]) in stored)
        lines_all += lines
    args = [re.sub(r';;\s*$', '', l)[len('refine'):] for l in lines_all]
    return [('C5', len(lines_all), 'MEASURED'), ('C5tok', len(' '.join(lines_all).split()), 'MEASURED'),
            ('C5lex', sum(len(lex.findall(a)) for a in args), 'MEASURED'), ('C5.main', main, 'MEASURED'),
            ('C5.inArchive', inarch, 'MEASURED' if have_arch else 'EMPTY')]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--arm', required=True, choices=['lean', 'metaprl'])
    ap.add_argument('--program', default='1', choices=['1', '2', '3'])
    ap.add_argument('dir')
    a = ap.parse_args()
    rows = lean(a.dir, a.program) if a.arm == 'lean' else metaprl(a.dir, '' if a.program == '1' else a.program)
    for c, v, s in rows:
        print(f'{a.arm}\t{c}\t{v}\t{s}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
