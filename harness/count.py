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
import argparse, os, re, subprocess, sys

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

CC_LAYERS = {'layer0': ('AsWritten', 'Repaired'), 'layer1': ('Steps', 'Paths'), 'layer2': ('Bridge', 'Refines')}


def compiler(repo, sha, compose, compose_sha=None):
    """STATUS-vir row 40 (exploratory, POST-PROOF, no prediction): the compiler application's proof size.
    repo = paris's spike, read AT `sha` by `git show` (the working tree moves); compose = vir's compose/ dir.
    Layers: layer0 the programs + concrete controls, layer1 per-address steps + exit paths, layer2 the
    abstraction bridge + the refinement. Units are C5's: non-blank lines (C5) and whitespace tokens (C5tok)."""
    import subprocess
    def show(path):
        r = subprocess.run(['git', '-C', repo, 'show', f'{sha}:{path}'], capture_output=True, text=True)
        return r.stdout if r.returncode == 0 else None
    ls = subprocess.run(['git', '-C', repo, 'ls-tree', '--name-only', sha, 'Router/'], capture_output=True, text=True)
    if ls.returncode != 0:
        return [('CC.spike.C5', 0, 'EMPTY')]
    names = sorted(n for n in ls.stdout.split() if n.endswith('.lean'))
    texts = {os.path.basename(n)[:-5]: show(n) or '' for n in names}
    def sz(ts):
        lines = [ln for t in ts for ln in t.splitlines() if ln.strip()]
        return len(lines), sum(len(ln.split()) for ln in lines)
    rows = []
    for k, mods in CC_LAYERS.items():
        a, b = sz([texts.get(m, '') for m in mods])
        rows += [(f'CC.{k}.C5', a, 'MEASURED'), (f'CC.{k}.C5tok', b, 'MEASURED')]
    a, b = sz(texts.values())
    rows += [('CC.spike.C5', a, 'MEASURED'), ('CC.spike.C5tok', b, 'MEASURED')]
    th = sum(len(re.findall(r'^theorem\s', t, re.M)) for t in texts.values())
    if compose and compose_sha:
        # row 45: read compose/Compose/*.lean AT a vir sha (paths relative to `compose`, so `./`)
        r = subprocess.run(['git', '-C', compose, 'ls-tree', '-r', '--name-only', compose_sha, 'Compose/'],
                           capture_output=True, text=True)
        csrc = sorted(n for n in r.stdout.split() if n.endswith('.lean')) if r.returncode == 0 else []
        ctexts = [subprocess.run(['git', '-C', compose, 'show', f'{compose_sha}:./{n}'], capture_output=True,
                                 text=True).stdout for n in csrc]
    else:
        csrc = files(os.path.join(compose, 'Compose'), ('.lean',)) if compose else []
        ctexts = [read(p) for p in csrc]
    a, b = sz(ctexts)
    rows += [('CC.compose.C5', a, 'MEASURED' if csrc else 'EMPTY'), ('CC.compose.C5tok', b, 'MEASURED' if csrc else 'EMPTY')]
    th += sum(len(re.findall(r'^theorem\s', t, re.M)) for t in ctexts)
    rows += [('CC.theorems', th, 'MEASURED'), ('CC.sha', sha, 'PINNED')]
    if compose_sha:
        rows.append(('CC.compose.sha', compose_sha, 'PINNED'))
    elif compose:
        rows.append(('CC.compose.sha', 'WORKTREE', 'UNPINNED'))
    return rows


# amend-10 (B′, the Lean mirror): read from lean/VIRB/ alone, so VIR/'s rows never move. Every row is per theorem.
BP_THEOREMS = {'1': 'router_fusion_bp', '2': 'router2_fusion_bp', '3': 'route_acl_safe_bp'}


def leanbp(d):
    """d = lean/VIRB. Reads the NEWEST logs/audit-bp-*.log (terms + axioms) and every logs/*.log (C6)."""
    logs = files(os.path.join(d, 'logs'), ('.log',))
    audits = [p for p in logs if re.search(r'/audit-bp-\d+\.log$', p)]
    if not audits:
        return [('B.audit', 0, 'EMPTY')]
    t = read(sorted(audits)[-1])
    HEQ = re.compile(r'(?<![A-Za-z0-9_.])(HEq|heq_of_eq)(?![A-Za-z0-9_])|≍')
    COE = re.compile(r'↑|(?<![A-Za-z0-9_])Subtype\.val(?![A-Za-z0-9_])|(?<!Subtype)\.val(?![A-Za-z0-9_])|\.property(?![A-Za-z0-9_])')
    blocks = re.split(r'\n(?=(?:@\[[^\]]*\]\s*)?theorem\s)', t)
    rows = [('B.audit', 1, 'READ:' + os.path.basename(sorted(audits)[-1]))]
    for prog, name in BP_THEOREMS.items():
        b = [x for x in blocks if re.match(r'theorem VIR\.BPrime\.' + name + r'\s', x)]
        if not b:
            rows.append(('BP%s.C1heq' % prog, 0, 'EMPTY')); continue
        rows += [('BP%s.C1heq' % prog, sum(len(HEQ.findall(x)) for x in b), 'MEASURED'),
                 ('BP%s.C1coe' % prog, sum(len(COE.findall(x)) for x in b), 'MEASURED')]
        ax = re.search(r"'VIR\.BPrime\." + name + r"' depends on axioms: \[([^\]]*)\]", t)
        extra = [a.strip() for a in ax.group(1).split(',')] if ax else []
        rows.append(('BP%s.C4' % prog, len(set(extra) - STD_AXIOMS), 'MEASURED' if ax else 'EMPTY'))
    for struct, prog in (('Carrier', '1'), ('Carrier2', '2')):
        m = re.search(r'structure VIR\.BPrime\.' + struct + r' .*?fields:\n(.*?)\nconstructor:', t, re.S)
        if m:
            own = len([l for l in m.group(1).splitlines() if l.strip()])
            rows.append(('BP%s.C4vir' % prog, own, 'MEASURED'))
    rows.append(('B.control', 1 if re.search(r"'control_sorry_bp' depends on axioms: \[sorryAx\]", t) else 0, 'MEASURED'))
    rows.append(('B.C6', sum(len(re.findall(r'^saltbuild EXIT=\d+', read(p), re.M)) for p in logs), 'MEASURED'))
    rows.append(('B.C6.scope', 0, 'LOGGED-RUNS-ONLY'))   # runs whose log was overwritten are not counted (RESULTS-4)
    return rows


# amend-10 (B′, the MetaPRL arm; STATUS-vir row 64). Read from a vir-metaprl checkout at mojave's PUBLIC B′ sha, whose
# tools snapshot is theories/vir/vir-arm-tools. EXPLORATORY by amend-10 on the MetaPRL side; rows per program.
# Rule boxes and primitive steps come from MetaPRL's status_all, which no file in the snapshot records: they stay Q.
BPM = {'1': ('vir', 'router_fuse'), '2': ('vir2', 'router2_fuse'), '3': ('vir3', 'route_acl_safe')}


def metaprlbp(d):
    """d = a dir holding vir-metaprl/ at the B′ sha."""
    root = os.path.join(d, 'vir-metaprl', 'theories', 'vir')
    tools = os.path.join(root, 'vir-arm-tools')
    if not os.path.isfile(os.path.join(tools, 'COUNTS-metaprl-bprime.md')):
        return [('BM.snapshot', 0, 'EMPTY')]
    rows = []
    prims = 0
    for prog, (mod, thm) in sorted(BPM.items()):
        ml = os.path.join(root, mod + '.ml')
        np_ = len(re.findall(r'^\s*prim(?:_rw)?\s', read(ml), re.M)) if os.path.isfile(ml) else 0
        prims += np_
        step = os.path.join(tools, 'steps', 'bp-' + mod + '.mp')
        run = os.path.join(tools, 'runs-bp-' + mod + '.txt')
        if not (os.path.isfile(step) and os.path.isfile(run)):
            rows.append(('BM%s.run' % prog, 0, 'EMPTY')); continue
        st, txt = read(step), read(run)
        end = re.search(r'^=== END steps=(\d+) ok=(\d+) err=(\d+) rc=(\d+)', txt, re.M)
        rows.append(('BM%s.replay' % prog, 1 if end and end.group(3) == '0' and end.group(4) == '0' else 0,
                     'MEASURED' if end else 'NO-END-LINE'))
        rows.append(('BM%s.C1' % prog, len(CAST_RE.findall(st)), 'MEASURED'))
        rows.append(('BM%s.prims' % prog, np_, 'MEASURED'))
        # SCOPE (one rule for the script and the run): a `cd` to an absolute path /vir/<mod>/<rule>[/<subgoal>...] sets the
        # current rule; a RELATIVE cd ("3", "../2") moves inside the current rule's proof tree and keeps it; any other
        # absolute cd leaves every rule. Program 3 navigates its proof by both forms (a first needle stopping at the
        # next cd read its chain as 13 tokens).
        def scope(cmd, cur):
            c = re.match(r'cd "([^"]*)"', cmd.strip())
            if not c:
                return cur
            path = c.group(1)
            if not path.startswith('/'):
                return cur
            a = re.match(r'/vir/' + re.escape(mod) + r'/([A-Za-z0-9_]+)(?:/|$)', path)
            return a.group(1) if a else None
        cur, chain_lines = None, []
        for ln in st.splitlines():
            cur = scope(ln, cur)
            if cur == thm and ln.strip().startswith('refine'):
                chain_lines.append(ln)
        rows.append(('BM%s.C5chain' % prog, len(' '.join(chain_lines).split()), 'MEASURED' if chain_lines else 'EMPTY'))
        rows.append(('BM%s.refines.thm' % prog, len(chain_lines), 'MEASURED'))
        # generated children over the WHOLE session (lemmas included) and over the theorem's own steps
        cmds = dict(re.findall(r'^=== STEP (\d+) \[[^\]]*\][^:]*:: (.*)$', txt, re.M))
        at, cur = {}, None
        for k in sorted(cmds, key=int):
            cur = scope(cmds[k], cur)
            at[k] = cur
        whole = {'wf': 0, 'equality': 0, 'assertion': 0}; own = dict(whole)
        for c in re.finditer(r'^=== CHILDREN (\d+):(.*)$', txt, re.M):
            if 'omegaT' in cmds.get(c.group(1), ''):
                continue
            for w in c.group(2).split():
                if w in whole:
                    whole[w] += 1
                    if at.get(c.group(1)) == thm:
                        own[w] += 1
        rows += [('BM%s.C2genWf' % prog, whole['wf'], 'MEASURED'), ('BM%s.C2genEq' % prog, whole['equality'], 'MEASURED'),
                 ('BM%s.C2genCond' % prog, whole['assertion'], 'MEASURED'),
                 ('BM%s.C2gen.thm' % prog, sum(own.values()), 'MEASURED')]
    rows.append(('BM.prims', prims, 'MEASURED'))
    # B4 (the A.2 transcription check, theory virtc): a tc rule is CLOSED when it is entered by `cd "/vir/virtc/<rule>"`
    # and every refine under it ran [ok] and left NO children. Read from the run transcript, never from
    # verdicttc.expected (an expectation, not a verdict). Limit: a goal closed by the replay, not status_all's "complete".
    st, run = os.path.join(tools, 'steps', 'tc.mp'), os.path.join(tools, 'runs-tc.txt')
    if os.path.isfile(st) and os.path.isfile(run):
        txt = read(run)
        steps = re.findall(r'^=== STEP (\d+) \[([^\]]*)\][^:]*:: (.*)$', txt, re.M)
        kids = {k: v.split() for k, v in re.findall(r'^=== CHILDREN (\d+):(.*)$', txt, re.M)}
        rules, cur = {}, None
        for k, status, cmd in steps:
            c = re.match(r'cd "/vir/virtc/([A-Za-z0-9_]+)"', cmd.strip())
            if c:
                cur = c.group(1); rules[cur] = {'refines': 0, 'bad': 0}
            elif cmd.strip().startswith('cd '):
                cur = None
            elif cur and cmd.strip().startswith('refine'):
                rules[cur]['refines'] += 1
                if status != 'ok' or k not in kids or kids[k]:
                    rules[cur]['bad'] += 1
        closed = sum(1 for r in rules.values() if r['refines'] and not r['bad'])
        rows += [('BMtc.rules', len(rules), 'MEASURED'), ('BMtc.closed', closed, 'MEASURED')]
    else:
        rows.append(('BMtc.rules', 0, 'EMPTY'))
    return rows


# amend-11 (the VIR PROGRAM, STATUS-vir row 76). d = virp. Rows P.*: V1 (C4vir), V2a (binder lemmas by D1's frozen
# operator list), the `ins` lemmas reported BESIDE V2a (not on the list), V6 (fixpoints), the audit and C6.
P_OPS = ('subst', 'shift', 'rename')     # D1; `lift`/`weaken` join only if VIRP DEFINES one (def/abbrev), never a theorem name


def p_statement(block):
    """A theorem's STATEMENT: its text after the declared name, up to the proof (`:=`) or its first match arm."""
    m = re.match(r'(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\s+\S+', block)
    rest = block[m.end():] if m else block
    cut = [i for i in (rest.find(':='), rest.find('\n  |')) if i >= 0]
    return rest[:min(cut)] if cut else rest


def leanp(d, sub='VIRP', tag='P'):
    src = files(os.path.join(d, sub), ('.lean',))
    if not src:
        return [(tag + '.src', 0, 'EMPTY')]
    text = '\n'.join(re.sub(r'/-[\s\S]*?-/|--[^\n]*', '', read(p)) for p in src)
    ops = list(P_OPS) + re.findall(r'^(?:def|abbrev)\s+(?:\S*\.)?(lift|weaken)\b', text, re.M)
    op_re = re.compile(r'(?<![A-Za-z0-9_])(?:[A-Za-z0-9_]+\.)*(' + '|'.join(ops) + r')(?![A-Za-z0-9_])')
    ins_re = re.compile(r'(?<![A-Za-z0-9_.])ins(?![A-Za-z0-9_])')
    thms = [b for b in blocks(text) if re.match(r'(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\b', b)]
    stm = [p_statement(b) for b in thms]
    binder = sum(1 for x in stm if op_re.search(x))
    ins_only = sum(1 for x in stm if ins_re.search(x) and not op_re.search(x))
    rows = [(tag + '.src', len(src), 'MEASURED'), (tag + '.theorems', len(thms), 'MEASURED'),
            (tag + '.C4vir', len(re.findall(r'^\s*(?:axiom|opaque|constant)\s', text, re.M)), 'MEASURED'),
            (tag + '.binder', binder, 'MEASURED'), (tag + '.binder.insOnly', ins_only, 'BESIDE'),
            (tag + '.fix', len(re.findall(r'(?<![A-Za-z0-9_])(?:Part|PFun)\.fix(?![A-Za-z0-9_])', text)), 'MEASURED')]
    # S5 (inputs/vir-program-inputs.md, EXPLORATORY): the separation model's theorems, from VIRP/Sep.lean alone
    sep = [p for p in src if os.path.basename(p) == 'Sep.lean']
    if sep:
        st = re.sub(r'/-[\s\S]*?-/|--[^\n]*', '', read(sep[0]))
        sth = [b for b in blocks(st) if re.match(r'(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\b', b)]
        rows += [(tag + '.sep.theorems', len(sth), 'EXPLORATORY'),
                 (tag + '.sep.laws', sum(1 for b in sth if re.search(r'(?<![A-Za-z0-9_])(union|Disj|emp)(?![A-Za-z0-9_])', p_statement(b))
                                    and not re.search(r'(?<![A-Za-z0-9_])(denote|own)(?![A-Za-z0-9_])', p_statement(b))), 'EXPLORATORY')]
    else:
        rows.append((tag + '.sep.theorems', 0, 'EMPTY'))
    logs = files(os.path.join(d, 'logs'), ('.log',))
    audits = [p for p in logs if re.search(r'/audit-\d+\.log$', p)]
    if audits:
        t = read(sorted(audits)[-1])
        ax = re.findall(r"depends on axioms: \[([^\]]*)\]", t)
        extra = set(a.strip() for g in ax for a in g.split(',')) - STD_AXIOMS
        rows += [(tag + '.audit', len(ax) + len(re.findall(r'does not depend on any axioms', t)), 'READ:' + os.path.basename(sorted(audits)[-1])),
                 (tag + '.C4', len(extra), 'MEASURED')]
    else:
        rows.append((tag + '.audit', 0, 'EMPTY'))
    ctl = [p for p in logs if re.search(r'/audit-control-\d+\.log$', p)]
    rows.append((tag + '.control', 1 if ctl and re.search(r"'control_sorry' depends on axioms: \[[^\]]*sorryAx", read(sorted(ctl)[-1])) else 0, 'MEASURED'))
    rows.append((tag + '.C6', sum(len(re.findall(r'^saltbuild EXIT=\d+', read(p), re.M)) for p in logs), 'MEASURED'))
    return rows

# amend-13 (layer L1, STATUS-vir row 94). d = l1. The leanp rows on VIRL1/ (W1 = L1.C4vir, W2a = L1.binder, W6 = L1.fix and
# the audit), plus W6's LEASTNESS uses (the fixpoint's approximation characterisation or its least-prefixed-point rule), W6b's
# continuity theorems (a statement mentioning ωScottContinuous), and the mutants: a mutant log counts RED only if its LAST
# `saltbuild EXIT=N` line has N != 0. A mutant log with no EXIT line is UNREAD, never red.
def leanl1(d):
    rows = leanp(d, 'VIRL1', 'L1')
    src = files(os.path.join(d, 'VIRL1'), ('.lean',))
    text = '\n'.join(re.sub(r'/-[\s\S]*?-/|--[^\n]*', '', read(p)) for p in src)
    thms = [b for b in blocks(text) if re.match(r'(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\b', b)]
    # BESIDE W2a (never in it: amend-13 froze the token list before the count was read): statements that mention the LIST half
    # of the mutual substitution (`substL`) and no token on the list.
    op_re = re.compile(r'(?<![A-Za-z0-9_])(?:[A-Za-z0-9_]+\.)*(' + '|'.join(P_OPS) + r')(?![A-Za-z0-9_])')
    rows.append(('L1.binder.substLOnly', sum(1 for b in thms if re.search(r'(?<![A-Za-z0-9_])(?:[A-Za-z0-9_]+\.)*substL(?![A-Za-z0-9_])', p_statement(b))
                                          and not op_re.search(p_statement(b))), 'BESIDE'))
    rows.append(('L1.leastness', len(re.findall(r'(?<![A-Za-z0-9_])Part\.(?:Fix\.mem_iff|Fix\.fix_le|fix_le)(?![A-Za-z0-9_])', text)), 'MEASURED'))
    rows.append(('L1.continuity', sum(1 for b in thms if re.search(r'ωScottContinuous', p_statement(b))), 'MEASURED'))
    muts = [p for p in files(os.path.join(d, 'logs'), ('.log',)) if re.search(r'/mutant-\d+\.log$', p)]
    red = unread = 0
    for p in muts:
        ex = re.findall(r'^saltbuild EXIT=(\d+)', read(p), re.M)
        if not ex:
            unread += 1
        elif ex[-1] != '0':
            red += 1
    rows += [('L1.mutants', len(muts), 'MEASURED'), ('L1.mutants.red', red, 'MEASURED'), ('L1.mutants.unread', unread, 'MEASURED')]
    return rows


# amend-16 (layer L2, STATUS-vir rows 105-106). d = l2. The leanp rows on VIRL2/ (Y1 = L2.C4vir, Y8 = L2.fix and the audit),
# plus: Y4, the frame rule's explicit binder groups (`theorem frame`'s statement; the rule's own two are R and the triple, so
# a side condition is any third group); Y3, the ⊢₂ family in the frame theorem's TRANSITIVE closure, read from the newest
# logs/closure-NNN.log (l2/Closure.lean), REFUSED (row Y3.control = 0) unless the PROOF control's line reads typing2 > 0 in the
# same log (a closure that follows statements only reads it 0: l2 mutant-001); Y7, statements mentioning the mask or its
# split (EXPLORATORY); Y6, the acceptance-program theorems present by name.
Y6_NAMES = ('M1_typed', 'M1_triple', 'M1_meaning', 'M2_typed', 'M2_triple', 'M2_meaning', 'M3_typed', 'M3_no_triple',
            'M3_meaning', 'M4_untyped', 'M4_triple', 'M4_leak', 'M4_meaning', 'M5_typed', 'M5_triple', 'M5_meaning')

Y5_ROUTE = ('SemBase.lean', 'MaskLemmas.lean', 'Subst2.lean', 'Runtime.lean', 'Progress.lean', 'RTSubst.lean',
            'OwnAll.lean', 'Preservation.lean', 'Y5.lean')




def proof_of(block):
    """A theorem's PROOF: its text after the statement (amend-18 Z5/Z6/Z8; amend-19 I3)."""
    st = p_statement(block)
    i = block.find(st) + len(st) if st else 0
    return block[i:]


IND_NAMES = ('ind_ty', 'ind_atom', 'ind_atoms', 'ind_tm', 'three_sorted_induction')
STD_AX = {'propext', 'Classical.choice', 'Quot.sound'}
NONPROOF_RE = re.compile(r'^\s*(?:include\b|mutual\b|end\b|set_option\b|section\b|variable\b|namespace\b|open\b|:=\s*$|by\s*$|:=\s*by\s*$)')


def leanind(d):
    """amend-19 on the Lean arm: DIR is the L1 project (l1/), the rule in VIRL1/Induction.lean."""
    p = os.path.join(d, 'VIRL1', 'Induction.lean')
    if not os.path.exists(p):
        return [('IND.src', 0, 'EMPTY')]
    text = re.sub(r'/-[\s\S]*?-/|--[^\n]*', '', read(p))
    thm = {}
    for b in blocks(text):
        m = re.match(r'(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\s+([A-Za-z0-9_.]+)', b)
        if m:
            thm[m.group(1)] = b
    lines = 0
    for n in IND_NAMES:
        if n in thm:
            lines += len([l for l in proof_of(thm[n]).splitlines() if l.strip() and not NONPROOF_RE.match(l)])
    aux = [n for n in thm if n not in IND_NAMES]
    rows = [('IND.I3.theorems', len([n for n in IND_NAMES if n in thm]), 'MEASURED:of %d' % len(IND_NAMES)),
            ('IND.I3.proofLines', lines, 'MEASURED:proof bodies of the five, statements and include/mutual/end lines excluded'),
            ('IND.I3.auxLemmas', len(aux), 'MEASURED:' + (','.join(aux) or '-')),
            ('IND.I3.proofTokens', sum(len(proof_of(thm[n]).split()) for n in IND_NAMES if n in thm), 'BESIDE:for I4(b)'),
            ('IND.I6.w3Premises', len(re.findall(r'\(X\d+\s*:', text)), 'MEASURED')]
    logs = sorted(q for q in files(os.path.join(d, 'logs'), ('.log',)) if re.search(r'/ind-audit-\d+\.log$', q))
    if logs:
        t = read(logs[-1])
        ax = re.findall(r"depends on axioms: \[([^\]]*)\]", t)
        bad = [a for a in ax if not {x.strip() for x in a.split(',')} <= STD_AX]
        rows.append(('IND.I2.audited', len(ax) + len(re.findall(r'does not depend on any axioms', t)), 'READ:' + os.path.basename(logs[-1])))
        rows.append(('IND.I2.nonStandard', len(bad), 'MEASURED'))
    else:
        rows += [('IND.I2.audited', 0, 'EMPTY'), ('IND.I2.nonStandard', 0, 'EMPTY')]
    return rows


def leanl2(d):
    rows = leanp(d, 'VIRL2', 'L2')
    src = files(os.path.join(d, 'VIRL2'), ('.lean',))
    text = '\n'.join(re.sub(r'/-[\s\S]*?-/|--[^\n]*', '', read(p)) for p in src)
    thms = [b for b in blocks(text) if re.match(r'(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\b', b)]
    fr = [b for b in thms if re.match(r'(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\s+frame\s', b)]
    if fr:
        st = p_statement(fr[0])
        rows.append(('L2.Y4.frameExplicitBinders', len(re.findall(r'\(\s*[^():]+?\s*:', st)), 'MEASURED'))
    else:
        rows.append(('L2.Y4.frameExplicitBinders', 0, 'EMPTY'))
    logs = sorted(p for p in files(os.path.join(d, 'logs'), ('.log',)) if re.search(r'/closure-\d+\.log$', p))
    if logs:
        t = read(logs[-1])
        def t2(name):
            m = re.search(r'closure ' + re.escape(name) + r': constants \d+ · VIRL2 \d+ · typing2 (\d+)', t)
            return int(m.group(1)) if m else None
        ctl = t2('control_proof_uses_typing')
        ok = 1 if ctl is not None and ctl > 0 else 0
        rows.append(('L2.Y3.control', ok, 'READ:' + os.path.basename(logs[-1])))
        for nm in ('VIRL2.frame', 'VIRL2.op_frame'):
            v = t2(nm)
            rows.append(('L2.Y3.' + nm.split('.')[-1], v if (v is not None and ok) else 0,
                         ('MEASURED' if ok else 'REFUSED:control') if v is not None else 'EMPTY'))
    else:
        rows.append(('L2.Y3.control', 0, 'EMPTY'))
    rows.append(('L2.Y7.maskLemmas', sum(1 for b in thms if re.search(r'(?<![A-Za-z0-9_])(?:Split|Mask\.\w+)(?![A-Za-z0-9_])', p_statement(b))), 'EXPLORATORY'))
    names = set(re.findall(r'^(?:theorem|lemma)\s+(\S+)', text, re.M))
    rows.append(('L2.Y6.theorems', sum(1 for n in Y6_NAMES if n in names), 'MEASURED:of%d' % len(Y6_NAMES)))
    rows.append(('L2.continuity', sum(1 for b in thms if re.search(r'ωScottContinuous', p_statement(b))), 'MEASURED'))
    # amend-16 Y5 (STATUS-vir row 124; selftest ARM36): the two theorems by name; fuel tokens in THEIR statements (Y5 is
    # FALSIFIED if it cannot be stated without fuel); bound premises inside the ⊢₂ inductives (FALSIFIED under (ii) if ⊢₂
    # needs one; each block cut at its namespace's `end`). Y7 (EXPLORATORY): the C5 size of the nine route files.
    y5 = {}
    for b in thms:
        m = re.match(r'(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\s+(y5_closed|y5_open)\s', b)
        if m:
            y5[m.group(1)] = b
    rows.append(('L2.Y5.closed', 1 if 'y5_closed' in y5 else 0, 'MEASURED'))
    rows.append(('L2.Y5.open', 1 if 'y5_open' in y5 else 0, 'MEASURED'))
    fuel = r'(?<![A-Za-z0-9_])(?:Nat|fuel|run₂?|stepFn₂?)(?![A-Za-z0-9_₂])'
    rows.append(('L2.Y5.fuelInStatement', sum(len(re.findall(fuel, p_statement(b))) for b in y5.values()),
                 'MEASURED' if y5 else 'EMPTY'))
    typ = [re.split(r'^end\b', b, flags=re.M)[0] for b in blocks(text) if re.match(r'inductive\s+HasType[AL]?₂\s', b)]
    rows.append(('L2.Y5.boundsInTyping', sum(len(re.findall(r'<|≤|InRegion|lookup', b)) for b in typ),
                 ('MEASURED:%d blocks' % len(typ)) if typ else 'EMPTY'))
    route = [p for p in src if os.path.basename(p) in Y5_ROUTE]
    sz = size(route)
    rows.append(('L2.Y7.semTypingC5', sz[0][1], 'EXPLORATORY:%d of %d files' % (len(route), len(Y5_ROUTE))))
    rows.append(('L2.Y7.semTypingC5tok', sz[-1][1], 'EXPLORATORY'))
    return rows


# amend-11 V3 (STATUS-vir row 87): how many of the CENTRAL DEFINITIONS one commit EDITS, as opposed to adds beside them.
# Lean names fixed by amend-11 (term syntax, step relation, typing relation, denotation). A definition is EDITED iff its
# declaration block exists at BOTH shas and its text differs. A block that only exists at `ext` is an ADDITION, and it is
# reported beside the count, never in it. The MetaPRL extractor is owed when the arm's file and declaration names are posted.
V3_LEAN = ('Tm', 'Step', 'HasType', 'den')


def git_show(repo, sha, path):
    r = subprocess.run(['git', '-C', repo, 'show', '%s:%s' % (sha, path)], capture_output=True)
    return r.stdout.decode('utf-8', 'replace') if r.returncode == 0 else None


def lean_decls(text):
    out = {}
    for b in blocks(re.sub(r'/-[\s\S]*?-/|--[^\n]*', '', text)):
        m = re.match(r'(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma|def|structure|inductive|instance|abbrev)\s+(\S+)', b)
        if m:
            out[m.group(1)] = re.sub(r'\s+', ' ', b).strip()
    return out


def v3(repo, base, ext, prefix):
    r = subprocess.run(['git', '-C', repo, 'ls-tree', '-r', '--name-only', ext, prefix], capture_output=True, text=True)
    paths = [x for x in r.stdout.split() if x.endswith('.lean')]
    if not paths:
        return [('V3.edited', 0, 'EMPTY')]
    before, after = {}, {}
    for p in paths:
        b, a = git_show(repo, base, p), git_show(repo, ext, p)
        if b is not None:
            before.update(lean_decls(b))
        if a is not None:
            after.update(lean_decls(a))
    rows = []
    edited = [n for n in V3_LEAN if n in before and n in after and before[n] != after[n]]
    missing = [n for n in V3_LEAN if n not in before]
    rows.append(('V3.edited', len(edited), 'MEASURED:' + (','.join(edited) or '-')))
    rows.append(('V3.central.missingAtBase', len(missing), 'MEASURED:' + (','.join(missing) or '-')))
    added = [n for n in after if n not in before]
    rows.append(('V3.added', len(added), 'BESIDE'))
    other = [n for n in after if n in before and before[n] != after[n] and n not in V3_LEAN]
    rows.append(('V3.otherEdited', len(other), 'BESIDE'))
    return rows


# amend-15 (W3 on layer L1): the four CENTRAL-DEFINITION CATEGORIES of OBJECT-L1, by the Lean names fixed in amend-15 BEFORE
# either arm's extension commit. A category is EDITED iff one of its declarations exists at BOTH shas with different text.
# The count is the number of CATEGORIES edited (0-4), never the number of blocks. Additions are reported beside.
W3_L1 = {'syntax': ('Ty', 'Atom', 'Tm'), 'step': ('Atom.eval', 'Atom.evalL', 'Step'),
         'typing': ('HasTypeA', 'HasTypeL', 'HasType'), 'den': ('head', 'Head.run', 'Φ', 'den')}


MODS = r'(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*'


def lean_decls_mod(text):
    """lean_decls, but a declaration MODIFIER (noncomputable, private, ...) starts a block instead of gluing the declaration
    onto the block before it. Local to W3 on L1: the shared `blocks` is left as it is, so no recorded router count moves."""
    text = re.sub(r'/-[\s\S]*?-/|--[^\n]*', '', text)
    kw = r'(?:theorem|lemma|def|structure|inductive|instance|abbrev)'
    starts = [m.start() for m in re.finditer(r'^(?:@\[[^\]]*\]\s*)?' + MODS + kw + r'\b', text, re.M)] + [len(text)]
    out = {}
    for a, b in zip(starts, starts[1:]):
        blk = text[a:b]
        m = re.match(r'(?:@\[[^\]]*\]\s*)?' + MODS + kw + r'\s+(\S+)', blk)
        if m:
            out[m.group(1)] = re.sub(r'\s+', ' ', blk).strip()
    return out


def v3l1(repo, base, ext, prefix):
    r = subprocess.run(['git', '-C', repo, 'ls-tree', '-r', '--name-only', ext, prefix], capture_output=True, text=True)
    paths = [x for x in r.stdout.split() if x.endswith('.lean')]
    if not paths:
        return [('W3.categories', 0, 'EMPTY')]
    before, after = {}, {}
    for p in paths:
        b, a = git_show(repo, base, p), git_show(repo, ext, p)
        if b is not None:
            before.update(lean_decls_mod(b))
        if a is not None:
            after.update(lean_decls_mod(a))
    names = [(cat, n) for cat, ns in W3_L1.items() for n in ns]
    edited = [(cat, n) for cat, n in names if n in before and n in after and before[n] != after[n]]
    cats = sorted(set(cat for cat, n in edited))
    # a name is required at base only if the category has no other name there (Head.run / Atom.evalL may not exist in an arm)
    missing = [cat for cat, ns in W3_L1.items() if not any(n in before for n in ns)]
    added = [n for n in after if n not in before]
    central = set(n for _, n in names)
    other = [n for n in after if n in before and before[n] != after[n] and n not in central]
    return [('W3.categories', len(cats), 'MEASURED:' + (','.join(cats) or '-')),
            ('W3.blocksEdited', len(edited), 'BESIDE:' + (','.join(n for _, n in edited) or '-')),
            ('W3.central.missingAtBase', len(missing), 'MEASURED:' + (','.join(missing) or '-')),
            ('W3.added', len(added), 'BESIDE'), ('W3.otherEdited', len(other), 'BESIDE')]


# layer L1, the MetaPRL side (STATUS-vir row 99; amend-13 W1, amend-14's file rule). Read from a vir-metaprl checkout at the
# arm's sha (FINDINGS M-F6: at or after EVERY soundness repair, by ancestry; M-F5's e0f16ac71 alone is not enough). W1 = prims in virl1_* theories ALONE; itt_bar* is the
# PARTIALITY THEORY column (NOT-AT-PIN), printed beside and never summed into W1. Groundedness comes from MetaPRL's check_all,
# which no file records: it stays the arm's QUOTED figure.
PRIM_RE = re.compile(r'^\s*prim(?:_rw)?\s', re.M)


def strip_ml_comments(t):
    # OCaml comments NEST; a commented-out prim or interactive is not a rule (ARM29: virl1_hoas_lang carries 4 commented
    # interactives). Newlines inside a comment are KEPT so the line structure (and ^-anchored regexes) survive.
    out, depth, i, n = [], 0, 0, len(t)
    while i < n:
        if t.startswith('(*', i):
            depth += 1; i += 2; continue
        if depth and t.startswith('*)', i):
            depth -= 1; i += 2; continue
        if depth == 0 or t[i] == '\n':
            out.append(t[i])
        i += 1
    return ''.join(out)


def metaprll1(d):
    root = os.path.join(d, 'vir-metaprl', 'theories', 'vir')
    if not os.path.isdir(root):
        return [('L1M.root', 0, 'EMPTY')]
    w1 = part = inter = 0; nf = 0; per = []
    for f in sorted(os.listdir(root)):
        if f.startswith('virl1_') and f.endswith('.ml'):
            t = strip_ml_comments(read(os.path.join(root, f))); n = len(PRIM_RE.findall(t)); nf += 1
            w1 += n; inter += len(re.findall(r'^\s*interactive(?:_rw)?\s', t, re.M)); per.append('%s=%d' % (f[:-3], n))
        elif f.startswith('itt_bar') and f.endswith('.ml'):
            part += len(PRIM_RE.findall(strip_ml_comments(read(os.path.join(root, f)))))
    bd, rv, bs, bper = metaprll1_binders(root)
    fx, fk2, fper = 0, 0, []
    for f in sorted(os.listdir(root)):
        if f.startswith('virl1_') and f.endswith('.prla'):
            n = len(FIXI_RE.findall(read(os.path.join(root, f))))
            fx += n; fk2 += n if f == 'virl1_k2.prla' else 0
            if n:
                fper.append('%s=%d' % (f[:-5], n))
    rows = [('L1M.files', nf, 'MEASURED'), ('L1M.W1', w1, 'MEASURED:' + (','.join(per) or '-')),
            ('L1M.binder', bd, 'MEASURED:LOWER-BOUND(named ops only):' + (','.join(bper) or '-')),
            ('L1M.binder.revived', rv, 'BESIDE:virl1_hoas_lang'), ('L1M.binder.substOnly', bs, 'BESIDE:subst{ alone'),
            ('L1M.fix', fx, 'MEASURED:fix_intro in virl1_*.prla:' + (','.join(fper) or '-')),
            ('L1M.fixK2', fk2, 'MEASURED:virl1_k2 (fix_intro IS fixpoint induction: the W6 leastness use)'),
            ('L1M.PARTIALITY', part, 'BESIDE:NOT-AT-PIN'), ('L1M.interactive', inter, 'MEASURED'),
            ('L1M.grounded', 0, 'Q:check_all')]
    return rows + metaprll1_pin_prims(os.path.join(d, 'vir-metaprl')) + metaprll1_floor(os.path.join(d, 'vir-metaprl'))


# W1b's PIN figure (ARM31): prims READ AT L1M_PIN from git objects, in the reflection dirs the pin BUILDS (reflection/MetaprlInfo's
# DIRS, read at the pin: obsolete/ and obsolete_flat/ are present and unbuilt, so not framework, amend-13) and the integer theory. These are TREE figures, an upper reading of what L1 rests on;
# the arm's own closure figure (reflection 23, RESULTS-5) is quoted beside. Lean's side is L1.audit's standard three.
L1M_INT = ('theories/itt/core/itt_int_base.ml', 'theories/itt/core/itt_int_ext.ml')


def metaprll1_pin_prims(repo):
    g = lambda *a: subprocess.run(['git', '-C', repo] + list(a), capture_output=True, text=True)
    ls = g('ls-tree', '-r', '--name-only', L1M_PIN, '--', 'theories/itt')
    if ls.returncode != 0:
        return [('L1M.pinReflection', 0, 'EMPTY:pin-unreadable'), ('L1M.pinInt', 0, 'EMPTY:pin-unreadable')]
    info = g('show', L1M_PIN + ':theories/itt/reflection/MetaprlInfo').stdout
    m = re.search(r'DIRS\[\]\s*=\s*\n((?:[ \t]+\S.*\n|#.*\n)+)', info)
    built = [x.strip() for x in (m.group(1).splitlines() if m else []) if x.strip() and not x.strip().startswith('#')]
    refl = intg = 0
    for p in ls.stdout.split():
        if not p.endswith('.ml'):
            continue
        if p.startswith('theories/itt/reflection/'):
            if p.split('/')[3] in built:
                refl += len(PRIM_RE.findall(strip_ml_comments(g('show', L1M_PIN + ':' + p).stdout)))
        elif p in L1M_INT:
            intg += len(PRIM_RE.findall(strip_ml_comments(g('show', L1M_PIN + ':' + p).stdout)))
    return [('L1M.pinReflection', refl, 'MEASURED:AT-PIN:tree'), ('L1M.pinInt', intg, 'MEASURED:AT-PIN')]


# W2b at L1, MetaPRL (ARM30): a BINDER LEMMA is a rule in virl1_* whose STATEMENT (the .ml text; proofs live in .prla)
# applies one of amend-11's NAMED reflection binder operators as op{...}. amend-11's "and siblings" was never enumerated, so
# this is a LOWER BOUND; virl1_hoas_lang (Lang{sop}, REVIVED under amend-13) is printed beside as its own sub-column.
FIXI_RE = re.compile(r'(?<![A-Za-z0-9_])fix_intro(?![A-Za-z0-9_])')
MPL_BINDER_RE = re.compile(r"(?<![A-Za-z0-9_'])(subst|bind|bdepth|var)\{")
MPL_ITEM_RE = re.compile(r'^[ \t]*(?=(?:interactive|interactive_rw|prim|prim_rw|define|declare|dform|let|doc|extends|open|val|topval)\b)', re.M)
MPL_RULE_RE = re.compile(r'^interactive(?:_rw)?\s+(\S+)')


def metaprll1_binders(root):
    tot = rev = sub = 0; per = []
    for f in sorted(os.listdir(root)):
        if not (f.startswith('virl1_') and f.endswith('.ml')):
            continue
        n = 0
        for blk in MPL_ITEM_RE.split(strip_ml_comments(read(os.path.join(root, f)))):
            if MPL_RULE_RE.match(blk) and MPL_BINDER_RE.search(blk):
                n += 1
                sub += 1 if re.search(r"(?<![A-Za-z0-9_'])subst\{", blk) else 0
        tot += n
        if f == 'virl1_hoas_lang.ml':
            rev = n
        if n:
            per.append('%s=%d' % (f[:-3], n))
    return tot, rev, sub, per


# W3 on L1, MetaPRL (ARM33; STATUS-vir row 98). The category map is the MetaPRL arm's OWN declaration (bus 2026-11-03 06:38,
# before any extension commit): by declaration, never by file alone. A central item is a define/declare in the files below,
# keyed by the TERM it defines; the Σ instance and the K programs are not central. The arm's stated alternative (interp, pty,
# pty1 as central, which it says reads W3 (i) as 2) is printed beside as W3M.categories.altCentral.
W3_L1M_FILES = {'virl1_sig': 'syntax', 'virl1_syntax': 'syntax', 'virl1_eval': 'step', 'virl1_step': 'step',
                'virl1_typing': 'typing', 'virl1_den': 'den'}
W3_L1M_SIGMA = re.compile(r'^(?:l1_(?:add|sub|mul|lt|le|eq|and|or|not)|(?:add|sub|mul|lt|le|eq|and|or|not)_op|sig1|interp|pty|pty1)$')
W3_L1M_ALT = re.compile(r'^(?:interp|pty|pty1)$')
W3_L1M_PROG = re.compile(r'^(?:lit\d+|k\d+)$')
MPL_DEF_RE = re.compile(r"^(?:declare\s+([A-Za-z_][A-Za-z0-9_]*)|define\s+\S+\s*:\s*([A-Za-z_][A-Za-z0-9_]*))")


def mpl_items(t):
    out = {}
    for blk in MPL_ITEM_RE.split(t):
        m = MPL_DEF_RE.match(blk)
        if m:
            out[m.group(1) or m.group(2)] = ' '.join(blk.split())
    return out


def v3l1m(repo, base, ext):
    g = lambda *a: subprocess.run(['git', '-C', repo] + list(a), capture_output=True, text=True)
    def at(sha):
        items, cats = {}, {}
        for f, cat in W3_L1M_FILES.items():
            path = 'theories/vir/%s.ml' % f
            r = g('show', sha + ':' + path)
            if r.returncode != 0:
                continue
            t = strip_ml_comments(g('show', sha + ':' + path).stdout)
            for k, v in mpl_items(t).items():
                items[k] = v; cats[k] = cat
        return items, cats
    b, bc = at(base)
    a, ac = at(ext)
    empty = not b
    edited = [k for k in b if k in a and b[k] != a[k] and not W3_L1M_PROG.match(k)]
    central = [k for k in edited if not W3_L1M_SIGMA.match(k)]
    alt = [k for k in edited if not W3_L1M_SIGMA.match(k) or W3_L1M_ALT.match(k)]
    cats = sorted(set(bc[k] for k in central)); altc = sorted(set(bc[k] for k in alt))
    added = [k for k in a if k not in b]
    # W3b (ARM34): rules over EVERY theories/vir/*.ml, and the stored-proof archives changed, beside the count
    def rules_at(sha):
        out = {}
        for p in g('ls-tree', '--name-only', sha, 'theories/vir/').stdout.split():
            if not p.endswith('.ml'):
                continue
            rt = strip_ml_comments(g('show', sha + ':' + p).stdout)
            for blk in MPL_ITEM_RE.split(rt):
                m = re.match(r'(?:interactive|prim)(?:_rw)?\s+(\S+)', blk)
                if m:
                    out[p + ':' + m.group(1)] = ' '.join(blk.split())
        return out
    rb, ra = rules_at(base), rules_at(ext)
    redit = [k for k in rb if k in ra and rb[k] != ra[k]]
    radd = [k for k in ra if k not in rb]
    prla = [p for p in g('diff', '--name-only', base, ext, '--', 'theories/vir').stdout.split() if p.endswith('.prla')]
    w3b = [('W3M.rulesEdited', len(redit), 'BESIDE:W3b'), ('W3M.rulesAdded', len(radd), 'BESIDE:W3b'),
           ('W3M.prlaChanged', len(prla), 'BESIDE:W3b:stored-proof archives')]
    if empty:
        return [('W3M.categories', 0, 'EMPTY:no-central-file-at-base')] + w3b
    return [('W3M.categories', len(cats), 'MEASURED:' + (','.join(cats) or '-')),
            ('W3M.rulesEdited', len(redit), 'BESIDE:W3b'), ('W3M.rulesAdded', len(radd), 'BESIDE:W3b'),
            ('W3M.prlaChanged', len(prla), 'BESIDE:W3b:stored-proof archives'),
            ('W3M.itemsEdited', len(central), 'BESIDE:' + (','.join(sorted(central)) or '-')),
            ('W3M.categories.altCentral', len(altc), 'BESIDE:interp/pty/pty1 read as central:' + (','.join(altc) or '-')),
            ('W3M.sigmaEdited', len([k for k in edited if W3_L1M_SIGMA.match(k)]), 'BESIDE'),
            ('W3M.added', len(added), 'BESIDE:' + (','.join(sorted(added)) or '-'))]


# FINDINGS M-F6: the floor is every soundness repair, by ANCESTRY, never by a date or a single sha. A checkout missing one
# reads VOID on its floor row (an inconsistent theory proves every row). FRAMEWORK EDITS = files under theories/ outside
# theories/vir that differ from the pinned release: counted beside W1b, never in W1, and listed so each can be read.
L1M_PIN = os.environ.get('VIR_L1M_PIN', 'fb8e715')
L1M_FLOOR = os.environ.get('VIR_L1M_FLOOR', 'e0f16ac71,40a89d4fc,1b209a393,07d3b4537,80fca4bec').split(',')


def metaprll1_floor(repo):
    g = lambda *a: subprocess.run(['git', '-C', repo] + list(a), capture_output=True, text=True)
    if g('rev-parse', '--git-dir').returncode != 0:
        return [('L1M.floorMissing', len(L1M_FLOOR), 'VOID:not-a-git-checkout'), ('L1M.frameworkEdits', 0, 'EMPTY')]
    miss = [s for s in L1M_FLOOR if g('merge-base', '--is-ancestor', s, 'HEAD').returncode != 0]
    r = g('diff', '--name-only', L1M_PIN, 'HEAD', '--', 'theories', ':!theories/vir')
    if r.returncode != 0:
        return [('L1M.floorMissing', len(miss), 'VOID:' + ','.join(miss) if miss else 'MEASURED'),
                ('L1M.frameworkEdits', 0, 'EMPTY:pin-unreadable')]
    fe = r.stdout.split()
    return [('L1M.floorMissing', len(miss), ('VOID:' + ','.join(miss)) if miss else 'MEASURED'),
            ('L1M.frameworkEdits', len(fe), 'BESIDE:' + (','.join(fe) or '-'))]


# W8 at L2 (amend-13 W8, amend-16 Y2 draft; STATUS-vir row 104): how many L1 DEFINITIONS (def / inductive / structure /
# instance / abbrev, any modifier) differ between the arm's L1-closed sha (base) and its L2-closed sha (ext), over the files
# under prefix that exist at BASE. A vanished definition is an edit. A theorem edit is printed BESIDE, never in W8. New files
# are L2's own and are counted beside.
ISTHM = re.compile(r'(?:@\[[^\]]*\]\s*)?' + MODS + r'(?:theorem|lemma)\b')


# amend-19 on the MetaPRL arm (ARM40; STATUS-vir row 136). DIR is a clone of the arm's vir-l1 tree; --base the L1-closed sha,
# --ext the sha the arm named for its rule. Everything is read from git objects at those two shas.
# A .prla is a hash-consed term DAG (P params · O ops · T terms · B bterms; N lines name each local op). A stored proof step is
# Summary!ext_rule[text]{status; goal; subgoals; extras} (MetaPRL tactics/proof/proof_term_boot.ml, HeadRule): the
# DERIVATION is the text plus its SUBGOALS' derivations; EXTRAS are subtrees kept from earlier refinements that no longer
# match a subgoal, so they are NOT the proof and are printed beside (INDM.extras.*). C5 is whitespace tokens of step texts,
# with multiplicity over the tree (a shared DAG node used twice is two steps).
IND_M_U, IND_M_S = 'l1_op_induction', 'l1_induction'
PRLA_RULES = ('Summary!rule', 'Summary!rewrite', 'Summary!cond_rewrite')


def prla_rules(text):
    P, O, T, B, N = {}, {}, {}, {}, {}
    for ln in text.splitlines():
        f = ln.split('\t')
        if len(f) < 3:
            continue
        if f[0].startswith('N') and len(f[0]) > 1:
            N[f[1]] = f[0][1:]
        elif f[0] in ('P', 'O', 'T', 'B'):
            {'P': P, 'O': O, 'T': T, 'B': B}[f[0]][f[1]] = f[2] if f[0] == 'P' else f[2].split(' ')
    def sval(pid):
        m = re.fullmatch(r'String (?:"(.*)"|(\S+))', P.get(pid, ''))
        return (m.group(1) if m.group(1) is not None else m.group(2)) if m else None
    term = lambda b: B[b][-1] if b in B else b
    opn = lambda t: N.get(O.get(T[t][0], [''])[0], '') if t in T else ''
    def xlist(t):
        out = []
        while opn(t) == 'Perv!xcons':
            out.append(term(T[t][1])); t = term(T[t][2])
        return out
    memo = {}
    def proof(t):   # (steps, tokens, extraSteps, extraTokens, texts)
        if t in memo:
            return memo[t]
        o = opn(t); k = [term(b) for b in T.get(t, [''])[1:]]
        s = w = xs = xw = 0; tx = []
        if o == 'Summary!ext_rule':
            txt = sval(O[T[t][0]][1]) or ''
            s, w, tx = 1, len(txt.split()), [txt]
            for c in xlist(k[2]):
                a = proof(c); s += a[0]; w += a[1]; xs += a[2]; xw += a[3]; tx += a[4]
            for c in xlist(k[3]):
                a = proof(c); xs += a[0] + a[2]; xw += a[1] + a[3]  # EXTRAS
        elif o == 'Summary!compose':
            for c in [k[0]] + xlist(k[1]):
                a = proof(c); s += a[0]; w += a[1]; xs += a[2]; xw += a[3]; tx += a[4]
            for c in xlist(k[2]):
                a = proof(c); xs += a[0] + a[2]; xw += a[1] + a[3]
        elif o == 'Summary!wrapped':
            s, w, xs, xw, tx = proof(k[1])
        memo[t] = (s, w, xs, xw, tx)
        return memo[t]
    def first_extract(t, depth=0):
        if opn(t) in ('Summary!ext_rule', 'Summary!compose', 'Summary!wrapped'):
            return t
        for b in T.get(t, [''])[1:]:
            r = first_extract(term(b), depth + 1) if depth < 64 else None
            if r:
                return r
        return None
    out = {}
    for tid, row in T.items():
        op = O.get(row[0], [''])
        if N.get(op[0], '') in PRLA_RULES and len(op) > 1:
            e = first_extract(tid)
            out[sval(op[1])] = proof(e) if e else (0, 0, 0, 0, [])
    return out


def ind_shapes(sig):
    """L1's operator list (core_ops + sig1's three lists) and each operator's arity SHAPE (binders per slot)."""
    shape = {}
    for name, body in re.findall(r'define\s+unfold_(\w+)\s*:\s*\1\s*<-->\s*operator\[\(l1_\w+(?:\{([^}]*)\})?\):op\]', sig):
        shape[name] = tuple(len(sl.split('.')[0].split(',')) if '.' in sl else 0 for sl in body.split(';')) if body else ()
    lst = []
    for d in ('core_ops', 'sig1'):
        m = re.search(r'define\s+unfold_%s\s*:\s*%s\s*<-->([\s\S]*?)(?=\n\S|\Z)' % (d, d), sig)
        lst += re.findall(r'\b(\w+_op)\b', m.group(1)) if m else []
    return {n: shape.get(n) for n in lst}


def indm(repo, base, ext):
    g = lambda *a: subprocess.run(['git', '-C', repo] + list(a), capture_output=True, text=True)
    if not base or not ext or g('cat-file', '-e', ext + '^{commit}').returncode != 0:
        return [('INDM.src', 0, 'EMPTY')]
    ls = lambda sha: set(g('ls-tree', '--name-only', sha, 'theories/vir/').stdout.split())
    lb, le = ls(base), ls(ext)
    new = sorted(p for p in le - lb)
    def items(sha, p):
        t = strip_ml_comments(g('show', sha + ':' + p).stdout); out = {}
        for blk in MPL_ITEM_RE.split(t):
            m = re.match(r'(interactive|prim|define|declare)(?:_rw)?\s+(\S+)', blk)
            if m:
                out[m.group(1)[0] + ':' + m.group(2)] = ' '.join(blk.split())
        return out
    redit = dedit = 0
    for p in sorted(lb & le):
        if p.endswith('.ml'):
            b, a = items(base, p), items(ext, p)
            for k in b:
                if k in a and b[k] != a[k]:
                    if k[0] in 'ip':
                        redit += 1
                    else:
                        dedit += 1
                elif k not in a:
                    redit += 1
    prla = [p for p in g('diff', '--name-only', base, ext, '--', 'theories/vir').stdout.split() if p.endswith('.prla') and p in lb]
    fw = [p for p in g('diff', '--name-only', base, ext, '--', 'theories', ':!theories/vir').stdout.split()]
    nprim = sum(len(PRIM_RE.findall(strip_ml_comments(g('show', ext + ':' + p).stdout))) for p in new if p.endswith('.ml'))
    rows = [('INDM.newFiles', len(new), 'BESIDE:' + (','.join(os.path.basename(p) for p in new) or '-')),
            ('INDM.I1.rulesEdited', redit, 'MEASURED:pre-existing theories/vir/*.ml, rules edited or removed (comments stripped)'),
            ('INDM.I1.defsEdited', dedit, 'MEASURED'), ('INDM.I1.prlaChanged', len(prla), 'MEASURED:' + (','.join(os.path.basename(p) for p in prla) or '-')),
            ('INDM.I2.newPrims', nprim, 'MEASURED:prim/prim_rw in new files'),
            ('INDM.I2.frameworkFiles', len(fw), 'MEASURED:theories/ outside vir changed:' + (','.join(fw) or '-')),
            ('INDM.I2.grounded', 0, 'Q:the arm\'s REPLAY post (status_all, fresh session)')]
    sh = ind_shapes(g('show', base + ':theories/vir/virl1_sig.ml').stdout)
    shapes = {s for s in sh.values() if s is not None}
    unpack, cov, unames = 0, set(), []
    for p in new:
        if not p.endswith('.ml'):
            continue
        for blk in MPL_ITEM_RE.split(strip_ml_comments(g('show', ext + ':' + p).stdout)):
            if not re.match(r'interactive\s', blk):
                continue
            m = re.search(r"compatible_shapes\{'\w+;\s*((?:\d+\s*::\s*)*nil)\s*;", blk)
            if m:
                unpack += 1; cov.add(tuple(int(x) for x in re.findall(r'\d+', m.group(1))))
                unames.append(re.match(r'interactive\s+(\S+)', blk).group(1))
    rows += [('INDM.I4a.operators', len(sh), 'MEASURED:core_ops + sig1 at base' + ('' if None not in sh.values() else ':UNSHAPED-OP')),
             ('INDM.I4a.arityShapes', len(shapes), 'MEASURED:' + ' '.join('[' + ','.join(map(str, s)) + ']' for s in sorted(shapes))),
             ('INDM.I4a.unpackLemmas', unpack, 'MEASURED:new rules with a literal compatible_shapes premise'),
             ('INDM.I4a.shapesCovered', len(cov & shapes), 'BESIDE:' + ('ALL' if cov == shapes else 'missing ' + str(sorted(shapes - cov)) + ' extra ' + str(sorted(cov - shapes))))]
    R = {}
    for p in new:
        if p.endswith('.prla'):
            R.update(prla_rules(g('show', ext + ':' + p).stdout))
    def uses(n):
        t = ' '.join(R[n][4])
        return {m for m in R if m != n and re.search(r"(?<![A-Za-z0-9_'])%s(?![A-Za-z0-9_'])" % re.escape(m), t)}
    def clos(n):
        seen, todo = set(), [n] if n in R else []
        while todo:
            x = todo.pop()
            if x not in seen:
                seen.add(x); todo += list(uses(x))
        return seen
    U = clos(IND_M_U); S = clos(IND_M_S) - U
    tok = lambda ns: sum(R[n][1] for n in ns)
    stage = lambda n: 'U' if n in U else 'S' if n in S else '?'
    rows += [('INDM.I4a.unpack.U', len([n for n in unames if n in U]), 'BESIDE:' + (','.join(n for n in unames if n in U) or '-')),
             ('INDM.I4a.unpack.notU', len([n for n in unames if n not in U]), 'BESIDE:' + (','.join('%s(%s)' % (n, stage(n)) for n in unames if n not in U) or '-'))]
    rows += [('INDM.rules', len(R), 'MEASURED:rules with a stored proof in new .prla'),
             ('INDM.I4b.C5tok', tok(R), 'MEASURED:whitespace tokens, every new rule, subgoal tree'),
             ('INDM.I4b.C5steps', sum(R[n][0] for n in R), 'MEASURED'),
             ('INDM.I5.U.rules', len(U), 'MEASURED:closure of %s by name in its derivation' % IND_M_U),
             ('INDM.I5.U.C5tok', tok(U), 'MEASURED'),
             ('INDM.I5.S.rules', len(S), 'MEASURED:closure of %s minus U' % IND_M_S),
             ('INDM.I5.S.C5tok', tok(S), 'MEASURED'),
             ('INDM.I5.neither', len(set(R) - U - S), 'BESIDE:' + (','.join(sorted(set(R) - U - S)) or '-')),
             ('INDM.top.' + IND_M_U, R.get(IND_M_U, (0, 0))[1], 'BESIDE'), ('INDM.top.' + IND_M_S, R.get(IND_M_S, (0, 0))[1], 'BESIDE'),
             ('INDM.extras.steps', sum(R[n][2] for n in R), 'BESIDE:stale subtrees, NOT the proof'),
             ('INDM.extras.C5tok', sum(R[n][3] for n in R), 'BESIDE:stale subtrees, NOT the proof')]
    lc = os.environ.get('VIR_IND_LEAN', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'l1', 'out', 'counts-ind.tsv'))
    lt = next((int(f[2]) for f in (l.split('\t') for l in (read(lc).splitlines() if os.path.isfile(lc) else [])) if len(f) > 2 and f[1] == 'IND.I3.proofTokens'), 0)
    rows.append(('INDM.I4b.ratioX100', tok(R) * 100 // lt if lt else 0, ('MEASURED:vs Lean IND.I3.proofTokens %d' % lt) if lt else 'EMPTY:no Lean counts'))
    return rows


def mpl_refs(n, text, names):
    """The rule names a derivation's text names, as whole identifiers (ARM41: `ty_rx_note` does not name `ty_r`)."""
    return {m for m in names if m != n and re.search(r"(?<![A-Za-z0-9_'])%s(?![A-Za-z0-9_'])" % re.escape(m), text)}  # REFS


# The MetaPRL L2 column (ARM41; STATUS-vir rows 122/134). DIR is a clone of the arm's tree, --base its L1-closed sha
# (ec912bd80), --ext the sha it names when it posts L2 CLOSED. Its DECLARATIONS-L2-METAPRL D0 fixes the reading: every L2
# module is `virl2_*`, ⊢₂ lives in `virl2_typing`, the frame rule is `triple_frame` (D6), and partiality's framework file
# `itt_bar_list` sits beside Y1 (its D1), never in it.
L2M_FRAME, L2M_TYPING = 'triple_frame', 'virl2_typing'
L2M_CARVE = ('wfs2', 'isNum2')  # D8 at mojave 9065db501
L2M_SCOPE = ('scoped2', 'scoped')  # D9 (mojave @97,494,337): the name as committed is re-read at D9's sha


def metaprll2(repo, base, ext):
    g = lambda *a: subprocess.run(['git', '-C', repo] + list(a), capture_output=True, text=True)
    if not base or not ext or g('cat-file', '-e', ext + '^{commit}').returncode != 0:
        return [('L2M.src', 0, 'EMPTY')]
    ls = lambda sha: set(g('ls-tree', '--name-only', sha, 'theories/vir/').stdout.split())
    lb, le = ls(base), ls(ext)
    show = lambda sha, p: strip_ml_comments(g('show', sha + ':' + p).stdout)
    l2 = sorted(p for p in le if os.path.basename(p).startswith('virl2_') and p.endswith('.ml'))
    prims = sum(len(PRIM_RE.findall(show(ext, p))) for p in l2)
    fw = [p for p in sorted(le) if os.path.basename(p).startswith('itt_bar') and p.endswith('.ml')
          and (p not in lb or show(base, p) != show(ext, p))]
    # Y1's FIGURE counts a framework prim as VIR-SPECIFIC when its OWN TEXT names a term that a virl1_*/virl2_* module defines or
    # declares (the CONTENT test, mojave 2026-11-04 00:50 fork (B), adopted by vir). It replaced an `extends Virl2_` test, which
    # read the name a file IMPORTS rather than what the prim is OVER (a label, not the instrument). Generic prims stay BESIDE.
    vterms = set()
    for p in le:
        b = os.path.basename(p)
        if (b.startswith('virl1_') or b.startswith('virl2_')) and b.endswith('.ml'):
            vterms |= set(re.findall(r"^(?:define\s+unfold_|declare\s+)([A-Za-z_][A-Za-z0-9_]*)", show(ext, p), re.M))
    vre = re.compile(r"(?<![A-Za-z0-9_'])(?:%s)(?![A-Za-z0-9_'])" % '|'.join(map(re.escape, sorted(vterms)))) if vterms else None
    fwp = vdp = 0; vnames = []
    MLI_RULE = re.compile(r'^[ \t]*(?=(?:rule|prim|rewrite|val|topval|declare|define|extends|open|doc|dform)\b)', re.M)
    for p in fw:
        # the prim's OWN TEXT is its .ml block AND its .mli declaration (`rule <name>`); sixth pass 2026-11-04: an .mli
        # still naming Store while the .ml was restated, invisible to an .ml-only reader
        mli = {}
        if p[:-3] + '.mli' in le:
            for b2 in MLI_RULE.split(show(ext, p[:-3] + '.mli')):
                m2 = re.match(r'\s*(?:rule|prim)\s+(\S+)', b2)
                if m2:
                    mli[m2.group(1)] = b2
        for blk in MPL_ITEM_RE.split(show(ext, p)):
            if PRIM_RE.match(blk):
                blk = blk + '\n' + mli.get(re.match(r'\s*prim(?:_rw)?\s+(\S+)', blk).group(1), '')
                if vre and vre.search(blk):
                    vdp += 1; vnames.append(re.match(r'\s*prim(?:_rw)?\s+(\S+)', blk).group(1))
                else:
                    fwp += 1
    def items(sha, p):
        out = {}
        for blk in MPL_ITEM_RE.split(show(sha, p)):
            m = re.match(r'(interactive|prim|define|declare)(?:_rw)?\s+(\S+)', blk)
            if m:
                out[m.group(1)[0] + ':' + m.group(2)] = ' '.join(blk.split())
        return out
    redit = dedit = 0
    for p in sorted(lb & le):
        if os.path.basename(p).startswith('virl1_') and p.endswith('.ml'):
            b, a = items(base, p), items(ext, p)
            for k in b:
                if k not in a or b[k] != a[k]:
                    if k[0] in 'ip':
                        redit += 1
                    else:
                        dedit += 1
    newl1 = sorted(os.path.basename(p) for p in le - lb if os.path.basename(p).startswith('virl1_') and p.endswith('.ml'))
    # TRUSTED BASE (STATUS-vir 145): the prims L2 RESTS ON are those of every non-virl theories/vir module in the `extends`
    # closure of the virl2_* modules (.ml and .mli), CHANGED OR NOT since base. A file unchanged since L1 but newly in L2's
    # ancestry (Itt_bar_bset via CONS clause 3 (ii)) is invisible to the added-or-changed row above.
    def ext_of(p):
        t = show(ext, p) + '\n' + (show(ext, p[:-3] + '.mli') if p[:-3] + '.mli' in le else '')
        return ['theories/vir/' + m[0].lower() + m[1:] + '.ml' for m in re.findall(r'^extends\s+([A-Z][A-Za-z0-9_]*)', t, re.M)]
    seen, todo = set(), list(l2)
    while todo:
        x = todo.pop()
        if x in seen or x not in le:
            continue
        seen.add(x); todo += ext_of(x)
    tb = sorted(p for p in seen if not re.match(r'virl[12]_', os.path.basename(p)))
    tbp = [(os.path.basename(p)[:-3], len(PRIM_RE.findall(show(ext, p)))) for p in tb]
    rows = [('L2M.files', len(l2), 'MEASURED:virl2_*.ml at ext'),
            ('L2M.trustedBase.files', len(tb), 'MEASURED:non-virl theories/vir modules in the extends closure of virl2_*'),
            ('L2M.trustedBase.prims', sum(n for _, n in tbp), 'MEASURED:' + (','.join('%s=%d' % x for x in tbp) or '-') + ':LIMIT theories/itt release prims not included (L1M.pinReflection)'),
            ('L2M.Y1.prims', prims, 'MEASURED:prim/prim_rw in virl2_*, comments stripped'),
            ('L2M.Y1.frameworkPrims', fwp, 'BESIDE:generic prims in itt_bar* added or changed since base:' + (','.join(os.path.basename(p) for p in fw) or '-')),
            ('L2M.Y1.virDependentPrims', vdp, 'MEASURED:framework prims whose text names a virl1_/virl2_ term:' + (','.join(vnames) or '-')),
            ('L2M.Y1.primFigure', prims + vdp, 'MEASURED:Y1 figure = virl2_* prims + VIR-dependent framework prims'),
            ('L2M.Y2.defsEdited', dedit, 'MEASURED:virl1_* at base vs ext'), ('L2M.Y2.rulesEdited', redit, 'BESIDE'),
            ('L2M.Y2.newL1Files', len(newl1), 'BESIDE:' + (','.join(newl1) or '-'))]
    # keyed MODULE:NAME — a rule name may recur across modules (two of virl2_rules' do), and a bare-name key drops one
    R, mod, byname = {}, {}, {}
    for p in sorted(le):
        b = os.path.basename(p)
        if b.startswith('virl2_') and b.endswith('.prla'):
            for n, v in prla_rules(g('show', ext + ':' + p).stdout).items():
                k = b[:-5] + ':' + n
                R[k] = v; mod[k] = b[:-5]; byname.setdefault(n, set()).add(k)
    names = set(byname)
    # the reference graph, read ONCE (STATUS-vir 153: per-rule regex over every name took ~55 min on 934 rules). A name made
    # only of identifier characters is found as a whole token, which is what mpl_refs' boundary regex means; any other name
    # keeps the regex.
    plain = {m for m in names if re.fullmatch(r"[A-Za-z0-9_']+", m)}
    odd = names - plain
    refs = {}
    for x in R:
        n, text = x.split(':', 1)[1], ' '.join(R[x][4])
        refs[x] = ((set(re.findall(r"[A-Za-z0-9_']+", text)) & plain) | mpl_refs(n, text, odd)) - {n}  # REFS2
    def clos(k0):
        seen, todo = set(), [k0] if k0 in R else []
        while todo:
            x = todo.pop()
            if x not in seen:
                seen.add(x)
                for n in refs[x]:
                    todo += list(byname[n])
        return seen
    typing = {k for k in R if mod[k] == L2M_TYPING}
    fk = sorted(byname.get(L2M_FRAME, ()))
    fc = clos(fk[0]) if fk else set()
    ctrl = len([n for n in R if (clos(n) - {n}) & typing])
    # the STATEMENT axis: a rule applied by resolution (autoT, dT) is never NAMED, so the name closure cannot see it; its
    # goal must still mention the judgement. Typing terms = what virl2_typing defines or declares.
    stm = {}
    for p in l2:
        for blk in MPL_ITEM_RE.split(show(ext, p)):
            m = re.match(r'interactive(?:_rw)?\s+(\S+)', blk)
            if m:
                stm[os.path.basename(p)[:-3] + ':' + m.group(1)] = blk
    tt = set(re.findall(r"^(?:define\s+unfold_|declare\s+)([A-Za-z_][A-Za-z0-9_]*)", show(ext, 'theories/vir/%s.ml' % L2M_TYPING), re.M))
    has_tt = lambda n: bool(tt) and bool(re.search(r"(?<![A-Za-z0-9_'])(?:%s)\{" % '|'.join(map(re.escape, sorted(tt))), stm.get(n, '')))
    tctrl = len([k for k in stm if not k.startswith(L2M_TYPING + ':') and has_tt(k)])
    stmt = stm.get(fk[0], '') if fk else ''
    rows += [('L2M.rules', len(R), 'MEASURED:rules with a stored proof in virl2_*.prla'),
             ('L2M.Y3.frameClosure', len(fc), ('MEASURED:%s and every rule its derivation names, transitively' % L2M_FRAME + (':AMBIGUOUS %d' % len(fk) if len(fk) > 1 else '')) if fc else 'EMPTY:no %s' % L2M_FRAME),
             ('L2M.Y3.frameTyping', len(fc & typing), ('MEASURED:' if ctrl else 'VOID:name control 0, a 0 here is not a pass:') + '%s rules in the closure:' % L2M_TYPING + (','.join(sorted(fc & typing)) or '-')),
             ('L2M.Y3.control', ctrl, 'BESIDE:rules whose closure, less themselves, names a typing rule (the name reader can see one)'),
             ('L2M.Y3.frameTypingTerms', len([k for k in fc if has_tt(k)]), ('MEASURED:' if tctrl else 'VOID:term control 0:') + 'closure rules whose STATEMENT names a %s term' % L2M_TYPING),
             ('L2M.Y3.termControl', tctrl, 'BESIDE:non-typing rules whose statement names a typing term (0 = nothing outside %s consumes it yet)' % L2M_TYPING),
             ('L2M.Y3.limit', 0, 'LIMIT:a typing rule applied by resolution whose name and judgement appear in no closure statement or text is invisible to both axes'),
             ('L2M.Y4.framePremises', stmt.count('-->'), 'MEASURED:premises of %s as stated' % L2M_FRAME if stmt else 'EMPTY')]
    # GRAMMAR CARVING (STATUS-vir 151, mojave's D8): the cost of carving grammar terms out of raw HOAS BTerm. Its predicates
    # are what D8 names, read by CONTENT: a rule counts iff its STATEMENT names one (the definitions, their rewrites and wf
    # rules, preservation, and any motive or hypothesis that carries one). Counted in Y5's C5 too; this line is the beside.
    # SCOPING (STATUS-vir 155, mojave's D9) is the same reading over L2M_SCOPE, on its OWN sub-line so the scoping cost is
    # never read as grammar cost; a rule naming both is in both lines and named once more on carvingOverlap.
    def carve(names, pre, what):
        defs = sum(len(re.findall(r"^define\s+unfold_(?:%s)\b" % '|'.join(names), show(ext, p), re.M)) for p in l2)
        hit = lambda k: bool(re.search(r"(?<![A-Za-z0-9_'])(?:%s)\{" % '|'.join(names), stm.get(k, '')))
        rs = sorted(k for k in stm if hit(k))
        return rs, [(pre + 'Defs', defs, 'MEASURED:define unfold_ of %s in virl2_*' % '/'.join(names) if defs else 'EMPTY:no %s predicate defined' % what),
                    (pre + 'Rules', len(rs), ('MEASURED:rules whose statement names %s:' % '/'.join(names) + (','.join(rs) or '-')) if defs else 'EMPTY'),
                    (pre + 'C5tok', sum(R[k][1] for k in rs if k in R), ('BESIDE:stored-proof tokens of those rules (%d of %d stored)' % (len([k for k in rs if k in R]), len(rs))) if defs else 'EMPTY')]
    cv, crow = carve(L2M_CARVE, 'L2M.Y5.carving', 'carving')
    sv, srow = carve(L2M_SCOPE, 'L2M.Y5.scoping', 'scoping')
    ov = sorted(set(cv) & set(sv))
    rows += crow + srow + [('L2M.Y5.carvingOverlap', len(ov), 'BESIDE:rules in BOTH lines (a sum of the two lines counts them twice):' + (','.join(ov) or '-'))]
    for m in sorted(set(mod.values())):
        ns = [n for n in R if mod[n] == m]
        rows.append(('L2M.C5tok.' + m, sum(R[n][1] for n in ns), 'BESIDE:%d rules; extras %d tok kept out' % (len(ns), sum(R[n][3] for n in ns))))
    rows += [('L2M.Y5', 0, 'Q:owed until the arm\'s semantic typing lands'), ('L2M.Y6', 0, 'Q:owed (M1-M5)'),
             ('L2M.Y8', 0, 'Q:owed (read at L2 CLOSED)')]
    return rows


def w8(repo, base, ext, prefix):
    ls = lambda sha: [x for x in subprocess.run(['git', '-C', repo, 'ls-tree', '-r', '--name-only', sha, prefix],
                                                 capture_output=True, text=True).stdout.split() if x.endswith('.lean')]
    old, new = ls(base), ls(ext)
    if not old:
        return [('W8.defsEdited', 0, 'EMPTY')]
    before, after = {}, {}
    for p in old:
        before.update(lean_decls_mod(git_show(repo, base, p) or ''))
        a = git_show(repo, ext, p)
        if a is not None:
            after.update(lean_decls_mod(a))
    defs, thms = [], []
    for n in before:
        if after.get(n) == before[n]:
            continue
        if not ISTHM.match(before[n]):
            defs.append(n)
        else:
            thms.append(n)
    return [('W8.defsEdited', len(defs), 'MEASURED:' + (','.join(defs) or '-')),
            ('W8.thmEdited', len(thms), 'BESIDE:' + (','.join(thms) or '-')),
            ('W8.newFiles', len([p for p in new if p not in old]), 'BESIDE')]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--arm', required=True, choices=['lean', 'metaprl', 'compiler', 'leanbp', 'metaprlbp', 'leanp', 'v3', 'l1', 'v3l1', 'metaprll1', 'w8', 'v3l1m', 'l2', 'ind', 'indm', 'metaprll2'])
    ap.add_argument('--sha')
    ap.add_argument('--compose')
    ap.add_argument('--compose-sha')
    ap.add_argument('--program', default='1', choices=['1', '2', '3'])
    ap.add_argument('--base'); ap.add_argument('--ext'); ap.add_argument('--prefix', default='virp/VIRP')
    ap.add_argument('dir')
    a = ap.parse_args()
    if a.arm == 'v3':
        rows = v3(a.dir, a.base, a.ext, a.prefix)
    elif a.arm == 'v3l1':
        rows = v3l1(a.dir, a.base, a.ext, a.prefix)
    elif a.arm == 'leanp':
        rows = leanp(a.dir)
    elif a.arm == 'l1':
        rows = leanl1(a.dir)
    elif a.arm == 'leanbp':
        rows = leanbp(a.dir)
    elif a.arm == 'w8':
        rows = w8(a.dir, a.base, a.ext, a.prefix)
    elif a.arm == 'l2':
        rows = leanl2(a.dir)
    elif a.arm == 'ind':
        rows = leanind(a.dir)
    elif a.arm == 'metaprll2':
        rows = metaprll2(a.dir, a.base, a.ext)
    elif a.arm == 'indm':
        rows = indm(a.dir, a.base, a.ext)
    elif a.arm == 'v3l1m':
        rows = v3l1m(a.dir, a.base, a.ext)
    elif a.arm == 'metaprll1':
        rows = metaprll1(a.dir)
    elif a.arm == 'metaprlbp':
        rows = metaprlbp(a.dir)
    elif a.arm == 'compiler':
        rows = compiler(a.dir, a.sha or 'HEAD', a.compose, a.compose_sha)
    else:
        rows = lean(a.dir, a.program) if a.arm == 'lean' else metaprl(a.dir, '' if a.program == '1' else a.program)
    for c, v, s in rows:
        print(f'{a.arm}\t{c}\t{v}\t{s}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
