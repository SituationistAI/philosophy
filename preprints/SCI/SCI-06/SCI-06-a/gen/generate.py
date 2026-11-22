#!/usr/bin/env python3
"""Translation manuals and computed statistics for SCI-06-a, Part II.

Reads the hand-curated manuals in data1.py ... data4.py (eight revolutions),
computes for every term its translation status, inferential weight and
translation score (Definitions 3.5--3.8 of the manuscript), for every
inference its verdict class, and for every revolution the translation index,
the comparability index, the untranslatable cluster and the outcome on the
five shared criteria.  It checks, with assertions:

  C1  integrity of the manuals (identifiers, token readings, images);
  C2  the verdict U is recorded exactly for inferences containing a reading
      with no referent in the successor theory;
  C3  every term figures in at least one inference (positive weight);
  C4  every revolution has translation index strictly between 0 and 1;
  C5  in every revolution at least one shared criterion favoured the successor;
  C6  the untranslatable cluster is a proper part of the vocabulary;
  C7  every revolution contains at least one translated and denied inference
      (genuine disagreement);
  C9  every criterion recorded as favouring the successor is supported by an
      evidential claim stated with term readings that all have referents in
      the successor (evidence.py);
  C8  the inequalities of C4 hold under the alternative scoring schemes
      S1, S3 and S4 (S2, the most generous, is reported but not checked).

Writes gen/manuals.tex, gen/inferences.tex, gen/evidence.tex, gen/summary.tex,
gen/stats.tex.
Python 3 standard library only; deterministic output.
"""
import os
import sys
from fractions import Fraction

GENDIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, GENDIR)
from data1 import CHEM, ASTR          # noqa: E402
from data2 import MECH, HEAT          # noqa: E402
from data3 import QUAN, BIOL          # noqa: E402
from data4 import PHYS, OPTI          # noqa: E402
from renderings1 import R1            # noqa: E402
from renderings2 import R2            # noqa: E402
from data5 import MIAS, HERE          # noqa: E402
from renderings3 import R3            # noqa: E402
from evidence import EVID             # noqa: E402

RENDER = dict(R1, **R2, **R3)

REVS = [CHEM, ASTR, MECH, HEAT, QUAN, BIOL, PHYS, OPTI, MIAS, HERE]
CRITERIA = ['accuracy', 'consistency', 'scope', 'simplicity', 'fruitfulness']
VERDICTS = 'HRXU'
STATUS_ORDER = ['exact', 'partial', 'token-dependent', 'none']
STATUS_ABBR = {'exact': 'E', 'partial': 'P', 'token-dependent': 'T', 'none': 'N'}

# ------------------------------------------------------------------ helpers

def tex(s):
    """Escape the LaTeX specials that occur in the data, leaving $...$ math alone."""
    out, math = [], False
    i = 0
    while i < len(s):
        c = s[i]
        if c == '$':
            math = not math
            out.append(c)
        elif c == '\\':
            # pass through control sequences already written in the data
            j = i + 1
            while j < len(s) and s[j].isalpha():
                j += 1
            if j == i + 1:
                j += 1
            out.append(s[i:j])
            i = j
            continue
        elif not math and c in '&%#_':
            out.append('\\' + c)
        elif not math and c == '~':
            out.append('~')
        else:
            out.append(c)
        i += 1
    return ''.join(out)


def fmt(x, nd=3):
    return f'{float(x):.{nd}f}'


def prefix(rev):
    return rev['terms'][0]['id'][:2]


def iid(rev, i):
    return f"{prefix(rev)}.{i}"


def parse_ref(ref, terms):
    """'CH01a' -> ('CH01', 'a'); 'CH05' -> ('CH05', None)."""
    if ref in terms:
        return ref, None
    tid, letter = ref[:-1], ref[-1]
    assert tid in terms, f'C1: unknown term in {ref}'
    return tid, letter


# ---------------------------------------------------------------- analysis

def analyse(rev):
    terms = {t['id']: t for t in rev['terms']}
    assert len(terms) == len(rev['terms']), f"C1: duplicate term id in {rev['id']}"
    p = prefix(rev)
    for t in rev['terms']:
        assert t['id'].startswith(p), f"C1: prefix of {t['id']}"
        letters = [k[0] for k in t['tokens']]
        assert letters == sorted(set(letters)) and letters, f"C1: token letters of {t['id']}"
        if t['image'] is not None:
            for k in t['tokens']:
                assert k[2] is not None, f"C1: {t['id']}{k[0]} lacks a referent although the term has a type-level image"
    infs = rev['infs']
    assert len({i[0] for i in infs}) == len(infs), f"C1: duplicate inference id in {rev['id']}"

    # readings and verdict check (C1, C2)
    occ = {tid: [] for tid in terms}          # term -> list of (inference index, token letter)
    for n, (i, text, refs, v) in enumerate(infs):
        assert v in VERDICTS, f'C1: verdict {v}'
        untrans = False
        for ref in refs:
            tid, letter = parse_ref(ref, terms)
            t = terms[tid]
            if t['image'] is None:
                assert letter is not None, f"C1: {rev['id']}.{i}: term {tid} has no type-level image, so a token reading is required"
                tok = [k for k in t['tokens'] if k[0] == letter]
                assert tok, f"C1: {rev['id']}.{i}: no token {ref}"
                if tok[0][2] is None:
                    untrans = True
            else:
                assert letter is None, f"C1: {rev['id']}.{i}: {tid} has a type-level image; no token reading allowed"
            occ[tid].append((n, letter))
        assert (v == 'U') == untrans, f"C2: {rev['id']}.{i}: verdict {v} but untranslatable reading present = {untrans}"

    # statuses, weights, scores
    res = {}
    for t in rev['terms']:
        tid = t['id']
        w = len(occ[tid])
        assert w >= 1, f'C3: {tid} figures in no inference'
        vs = [infs[n][3] for n, _ in occ[tid]]
        nref = sum(1 for k in t['tokens'] if k[2] is not None)
        ntok = len(t['tokens'])
        if t['image'] is None:
            status = 'token-dependent' if nref else 'none'
        elif isinstance(t['image'], list):
            status = 'partial'
        else:
            status = 'exact' if all(v == 'H' for v in vs) else 'partial'
        res[tid] = dict(status=status, w=w, nref=nref, ntok=ntok, vs=vs, occ=occ[tid])
    return terms, res


def score(status, nref, ntok, scheme):
    """Translation score of a term under a scoring scheme.
    S0 (standard): exact 1, partial 1, token-dependent nref/ntok, none 0.
    S1: token-dependent scored 0 (only type-level translation counts).
    S2: token-dependent scored 1 if any token refers.
    S3: partial scored 1/2.
    S4: as S0 but unweighted (weights set to 1; handled by caller)."""
    if status == 'exact':
        return Fraction(1)
    if status == 'partial':
        return Fraction(1, 2) if scheme == 'S3' else Fraction(1)
    if status == 'token-dependent':
        if scheme == 'S1':
            return Fraction(0)
        if scheme == 'S2':
            return Fraction(1)
        return Fraction(nref, ntok)
    return Fraction(0)


def index(rev, res, scheme='S0'):
    num = den = Fraction(0)
    for t in rev['terms']:
        r = res[t['id']]
        w = 1 if scheme == 'S4' else r['w']
        num += w * score(r['status'], r['nref'], r['ntok'], scheme)
        den += w
    return num / den


def stats_for(rev):
    terms, res = analyse(rev)
    infs = rev['infs']
    n = len(infs)
    vc = {v: sum(1 for i in infs if i[3] == v) for v in VERDICTS}
    ti = index(rev, res)
    sens = {s: index(rev, res, s) for s in ['S0', 'S1', 'S2', 'S3', 'S4']}
    # untranslatable cluster: terms with at least one token reading that has no referent in T2
    cluster = [t['id'] for t in rev['terms'] if any(k[2] is None for k in t['tokens'])]
    for t in rev['terms']:
        for (letter, _, ref) in t['tokens']:
            if ref is None:
                assert any(l == letter for (_, l) in res[t['id']]['occ']), \
                    f"C1: non-referring reading {t['id']}{letter} figures in no inference"
    # neutral core: inferences all of whose terms are exact
    core = [i[0] for i in infs
            if all(res[parse_ref(r_, terms)[0]]['status'] == 'exact' for r_ in i[2])]
    counts = {s: sum(1 for t in rev['terms'] if res[t['id']]['status'] == s) for s in STATUS_ORDER}
    ntok = sum(len(t['tokens']) for t in rev['terms'])
    nref = sum(res[t['id']]['nref'] for t in rev['terms'])
    crit = rev['crit']
    assert set(crit) == set(CRITERIA), f"C1: criteria of {rev['id']}"
    plus = [c for c in CRITERIA if crit[c][0] == '+']
    minus = [c for c in CRITERIA if crit[c][0] == '-']
    dominant = not minus
    st = dict(terms=terms, res=res, n=n, vc=vc, ti=ti, sens=sens, cluster=cluster, core=core,
              counts=counts, ntok=ntok, nref=nref, plus=plus, minus=minus,
              kappa=Fraction(n - vc['U'], n), ip=Fraction(vc['H'] + vc['R'], n),
              ti_unw=sens['S4'], dominant=dominant)
    # checks C4--C8
    assert 0 < ti < 1, f"C4 fails for {rev['id']}: index {ti}"
    assert plus, f"C5 fails for {rev['id']}: no shared criterion favoured the successor"
    assert 0 < len(cluster) < len(rev['terms']), f"C6 fails for {rev['id']}"
    assert vc['X'] > 0, f"C7 fails for {rev['id']}"
    for s, v in sens.items():
        if s == 'S2':
            continue          # S2 is the generous upper bound; reported, not checked
        assert 0 < v < 1, f"C8 fails for {rev['id']} under {s}: {v}"
    # C9: evidence for favourable outcomes is stated in translatable readings
    ev = EVID[rev['id']]
    for (eid, text, refs, crits) in ev:
        for c in crits:
            assert c in CRITERIA, f"C1: criterion {c} in {rev['id']}.{eid}"
        for ref in refs:
            tid, letter = parse_ref(ref, terms)
            t = terms[tid]
            if t['image'] is None:
                assert letter is not None, f"C1: {rev['id']}.{eid}: token reading required for {tid}"
                tok = [k for k in t['tokens'] if k[0] == letter]
                assert tok and tok[0][2] is not None, f"C9 fails: {rev['id']}.{eid} uses non-referring reading {ref}"
            else:
                assert letter is None, f"C1: {rev['id']}.{eid}: no token reading allowed for {tid}"
    for c in plus:
        assert any(c in e[3] for e in ev), f"C9 fails: {rev['id']} criterion {c} has no evidential claim"
    for e in ev:
        for c in e[3]:
            assert crit[c][0] == '+', f"C1: {rev['id']}.{e[0]} cited for {c}, which is not recorded as +"
    st['evid'] = ev
    return st


# ------------------------------------------------------------------ output

def inf_list(rev, st, occ_items):
    """Group inference ids by verdict: 'H: I03 I05; X: I19'."""
    groups = {v: [] for v in VERDICTS}
    for n, _ in occ_items:
        i = rev['infs'][n]
        groups[i[3]].append(i[0])
    parts = []
    for v in VERDICTS:
        if groups[v]:
            parts.append(v + ': ' + ' '.join(sorted(set(groups[v]))))
    return '; '.join(parts)


def image_str(img):
    if img is None:
        return '---'
    if isinstance(img, list):
        return ' $\\mid$ '.join(tex(x) for x in img) + ' (pd)'
    return tex(img)


def write_manuals(path, stats):
    L = []
    for rev in REVS:
        st = stats[rev['id']]
        L.append(f"\\Needspace{{10\\baselineskip}}\\subsection*{{{rev['id']}: {tex(rev['short'])}}}")
        L.append(f"\\addcontentsline{{toc}}{{subsection}}{{{rev['id']}: {tex(rev['short'])}}}")
        L.append(f"\\noindent\\textit{{Predecessor}} $T_1$: {tex(rev['t1'])}.\\\\")
        L.append(f"\\textit{{Successor}} $T_2$: {tex(rev['t2'])}.\\par\\smallskip")
        L.append('\\begin{manualtable}')
        for t in rev['terms']:
            r = st['res'][t['id']]
            stat = f"\\textbf{{{STATUS_ABBR[r['status']]}}} {r['status']}"
            sc = score(r['status'], r['nref'], r['ntok'], 'S0')
            scs = '1' if sc == 1 else ('0' if sc == 0 else f"{sc.numerator}/{sc.denominator}")
            infcol = inf_list(rev, st, r['occ']) if t['image'] is not None else 'by token'
            L.append(f"\\textbf{{{t['id']}}} & \\textbf{{{tex(t['term'])}}}. {tex(t['role'])} & "
                     f"{image_str(t['image'])} & {stat}; $w$\\,=\\,{r['w']}; $s$\\,=\\,{scs} & {infcol} \\\\")
            for (letter, ctx, ref) in t['tokens']:
                if t['image'] is None:
                    occ = [(n, l) for (n, l) in r['occ'] if l == letter]
                    tinf = inf_list(rev, st, occ) if occ else '(none listed)'
                else:
                    tinf = 'as term'
                refs = tex(ref) if ref is not None else '\\textit{no referent}'
                L.append(f"\\quad {t['id']}{letter} & {tex(ctx)} & {refs} & "
                         f"{'refers' if ref is not None else 'fails'} & {tinf} \\\\")
            L.append('\\midrule')
        L[-1] = '\\bottomrule'
        L.append('\\end{manualtable}')
        L.append('')
    open(path, 'w').write('\n'.join(L) + '\n')


def write_inferences(path, stats):
    L = []
    for rev in REVS:
        st = stats[rev['id']]
        L.append(f"\\Needspace{{10\\baselineskip}}\\subsection*{{{rev['id']}: inferences}}")
        L.append(f"\\addcontentsline{{toc}}{{subsection}}{{{rev['id']}: inferences}}")
        L.append('\\begin{inftable}')
        for (i, text, refs, v) in rev['infs']:
            readings = []
            for ref in refs:
                tid, letter = parse_ref(ref, st['terms'])
                t = st['terms'][tid]
                if letter is not None:
                    tok = [k for k in t['tokens'] if k[0] == letter][0]
                    mark = '' if tok[2] is not None else '$^{\\ast}$'
                else:
                    mark = '' if st['res'][tid]['status'] == 'exact' else '$^{\\circ}$'
                readings.append(ref + mark)
            L.append(f"{iid(rev, i)} & {tex(text)} & {tex(RENDER[iid(rev, i)])} & {', '.join(readings)} & \\textbf{{{v}}} \\\\")
        L.append('\\bottomrule')
        L.append('\\end{inftable}')
        L.append('')
    open(path, 'w').write('\n'.join(L) + '\n')


def frac(x):
    return fmt(x)


def write_summary(path, stats):
    L = []
    # Table A: per-revolution statistics
    L.append('\\begin{table}[!htb]\\centering\\footnotesize\\setlength{\\tabcolsep}{3.2pt}')
    L.append('\\caption{Per-revolution statistics computed from the manuals.}\\label{tab:stats}')
    L.append('\\begin{tabular}{@{}lrrrrrrrrrrrrr@{}}\\toprule')
    L.append('Rev. & terms & tok. & E & P & T & N & inf. & H & R & X & U & $\\tau$ & $\\kappa$\\\\\\midrule')
    tot = dict(terms=0, tok=0, E=0, P=0, T=0, N=0, inf=0, H=0, R=0, X=0, U=0)
    for rev in REVS:
        st = stats[rev['id']]
        c = st['counts']
        row = [rev['id'], len(rev['terms']), st['ntok'], c['exact'], c['partial'], c['token-dependent'], c['none'],
               st['n'], st['vc']['H'], st['vc']['R'], st['vc']['X'], st['vc']['U']]
        for k, v in zip(['terms', 'tok', 'E', 'P', 'T', 'N', 'inf', 'H', 'R', 'X', 'U'], row[1:]):
            tot[k] += v
        L.append(' & '.join(str(x) for x in row) + f" & {frac(st['ti'])} & {frac(st['kappa'])}\\\\")
    L.append('\\midrule')
    L.append('All & ' + ' & '.join(str(tot[k]) for k in ['terms', 'tok', 'E', 'P', 'T', 'N', 'inf', 'H', 'R', 'X', 'U'])
             + ' & & \\\\\\bottomrule\\end{tabular}\\end{table}')
    L.append('')
    # Table B: further indices
    L.append('\\begin{table}[!htb]\\centering\\footnotesize')
    L.append('\\caption{Further indices: unweighted translation share, inferential preservation $\\pi$, disagreement share $\\delta$, the untranslatable cluster and the neutral core.}\\label{tab:further}')
    L.append('\\begin{tabular}{@{}lrrrp{6.2cm}r@{}}\\toprule')
    L.append('Rev. & $\\tau_{\\mathrm{unw}}$ & $\\pi$ & $\\delta$ & untranslatable cluster $C$ & core\\\\\\midrule')
    for rev in REVS:
        st = stats[rev['id']]
        cl = ', '.join(f"{c} ({tex(st['terms'][c]['term'])})" for c in st['cluster'])
        L.append(f"{rev['id']} & {frac(st['ti_unw'])} & {frac(st['ip'])} & {frac(Fraction(st['vc']['X'], st['n']))} & "
                 f"{cl} & {len(st['core'])}\\\\")
    L.append('\\bottomrule\\end{tabular}\\end{table}')
    L.append('')
    # Table C: sensitivity
    L.append('\\begin{table}[!htb]\\centering\\footnotesize')
    L.append('\\caption{Translation index under the standard scoring S0 and the alternative schemes S1--S4.}\\label{tab:sens}')
    L.append('\\begin{tabular}{@{}lrrrrrc@{}}\\toprule')
    L.append('Rev. & S0 & S1 & S2 & S3 & S4 & C8\\\\\\midrule')
    for rev in REVS:
        st = stats[rev['id']]
        s = st['sens']
        ok = all(0 < s[k] < 1 for k in s if k != 'S2')
        L.append(f"{rev['id']} & " + ' & '.join(frac(s[k]) for k in ['S0', 'S1', 'S2', 'S3', 'S4'])
                 + f" & {'pass' if ok else 'FAIL'}\\\\")
    L.append('\\bottomrule\\end{tabular}\\end{table}')
    L.append('')
    open(path, 'w').write('\n'.join(L) + '\n')


def write_criteria(path, stats):
    sym = {'+': '$+$', '-': '$-$', '~': '$\\pm$', '?': '?'}
    L = []
    L.append('\\begin{table}[!htb]\\centering\\footnotesize')
    L.append('\\caption{Outcome of each revolution on the five shared criteria ($+$ favoured the successor, $-$ the predecessor, $\\pm$ mixed or contested, ? no claim made), with the mechanical checks C4 and C5.}\\label{tab:crit}')
    L.append('\\begin{tabular}{@{}lcccccccc@{}}\\toprule')
    L.append('Rev. & acc. & cons. & scope & simp. & fruit. & C4: $0<\\tau<1$ & C5: some $+$ & no $-$\\\\\\midrule')
    for rev in REVS:
        st = stats[rev['id']]
        cells = [sym[rev['crit'][c][0]] for c in CRITERIA]
        L.append(f"{rev['id']} & " + ' & '.join(cells)
                 + f" & {'pass' if 0 < st['ti'] < 1 else 'FAIL'} ({frac(st['ti'])}) & {'pass' if st['plus'] else 'FAIL'} ({len(st['plus'])}) & {'yes' if st['dominant'] else 'no'}\\\\")
    L.append('\\bottomrule\\end{tabular}\\end{table}')
    L.append('')
    L.append('\\begin{crittable}')
    for rev in REVS:
        for c in CRITERIA:
            o, note = rev['crit'][c]
            if o == '?':
                continue
            L.append(f"{rev['id']} & {c} & {sym[o]} & {tex(note)}\\\\")
        L.append('\\midrule')
    L[-1] = '\\bottomrule'
    L.append('\\end{crittable}')
    open(path, 'a').write('\n'.join(L) + '\n')


def write_evidence(path, stats):
    L = ['\\begin{evidtable}']
    for rev in REVS:
        for (eid, text, refs, crits) in stats[rev['id']]['evid']:
            L.append(f"{prefix(rev)}.{eid} & {tex(text)} & {', '.join(refs)} & {', '.join(crits)}\\\\")
        L.append('\\midrule')
    L[-1] = '\\bottomrule'
    L.append('\\end{evidtable}')
    open(path, 'w').write('\n'.join(L) + '\n')


def write_stats(path, stats):
    M = []

    def mac(name, val):
        M.append(f'\\newcommand{{\\{name}}}{{{val}}}')
    words = {'CHEM': 'Chem', 'ASTR': 'Astr', 'MECH': 'Mech', 'HEAT': 'Heat',
             'QUAN': 'Quan', 'BIOL': 'Biol', 'PHYS': 'Phys', 'OPTI': 'Opti',
             'MIAS': 'Mias', 'HERE': 'Here'}
    tot_terms = sum(len(r['terms']) for r in REVS)
    tot_tok = sum(stats[r['id']]['ntok'] for r in REVS)
    tot_inf = sum(stats[r['id']]['n'] for r in REVS)
    tot_ref = sum(stats[r['id']]['nref'] for r in REVS)
    mac('nrevs', len(REVS))
    mac('ntermsall', tot_terms)
    mac('ntokensall', tot_tok)
    mac('nrefall', tot_ref)
    mac('ninfall', tot_inf)
    for s in STATUS_ORDER:
        mac('nstat' + {'exact': 'E', 'partial': 'P', 'token-dependent': 'T', 'none': 'N'}[s],
            sum(stats[r['id']]['counts'][s] for r in REVS))
    for v in VERDICTS:
        mac('nverd' + v, sum(stats[r['id']]['vc'][v] for r in REVS))
    mac('ndominant', sum(1 for r in REVS if stats[r['id']]['dominant']))
    mac('nevidall', sum(len(stats[r['id']]['evid']) for r in REVS))
    mac('nclusterall', sum(len(stats[r['id']]['cluster']) for r in REVS))
    mac('ncoreall', sum(len(stats[r['id']]['core']) for r in REVS))
    tis = [stats[r['id']]['ti'] for r in REVS]
    mac('timin', fmt(min(tis)))
    mac('timax', fmt(max(tis)))
    ks = [stats[r['id']]['kappa'] for r in REVS]
    mac('kappamin', fmt(min(ks)))
    mac('kappamax', fmt(max(ks)))
    allsens = [v for r in REVS for k, v in stats[r['id']]['sens'].items() if k != 'S2']
    mac('sensmin', fmt(min(allsens)))
    mac('sensmax', fmt(max(allsens)))
    for r in REVS:
        st = stats[r['id']]
        w = words[r['id']]
        mac('ti' + w, fmt(st['ti']))
        mac('kappa' + w, fmt(st['kappa']))
        mac('pi' + w, fmt(st['ip']))
        mac('nterms' + w, len(r['terms']))
        mac('ninf' + w, st['n'])
        mac('ncl' + w, len(st['cluster']))
        mac('nX' + w, st['vc']['X'])
        mac('nU' + w, st['vc']['U'])
        mac('nplus' + w, len(st['plus']))
    open(path, 'w').write('\n'.join(M) + '\n')


def main():
    stats = {rev['id']: stats_for(rev) for rev in REVS}
    ids = {iid(rev, i[0]) for rev in REVS for i in rev['infs']}
    assert ids == set(RENDER), f'C1: renderings missing {sorted(ids - set(RENDER))} or extra {sorted(set(RENDER) - ids)}'
    for k, v in RENDER.items():
        verdict = [i[3] for rev in REVS for i in rev['infs'] if iid(rev, i[0]) == k][0]
        assert v.startswith('Interpretation:') == (verdict == 'U'), f'C1: rendering type of {k}'
    write_manuals(os.path.join(GENDIR, 'manuals.tex'), stats)
    write_inferences(os.path.join(GENDIR, 'inferences.tex'), stats)
    write_summary(os.path.join(GENDIR, 'summary.tex'), stats)
    write_criteria(os.path.join(GENDIR, 'summary.tex'), stats)
    write_stats(os.path.join(GENDIR, 'stats.tex'), stats)
    write_evidence(os.path.join(GENDIR, 'evidence.tex'), stats)
    # console report
    for rev in REVS:
        st = stats[rev['id']]
        print(f"{rev['id']}: terms {len(rev['terms'])} tokens {st['ntok']} infs {st['n']} "
              f"status {st['counts']} verdicts {st['vc']} tau {fmt(st['ti'])} kappa {fmt(st['kappa'])} "
              f"pi {fmt(st['ip'])} cluster {st['cluster']} core {len(st['core'])} plus {st['plus']} "
              f"sens {[fmt(v) for v in st['sens'].values()]}")
    print('All checks C1--C9 passed.')


if __name__ == '__main__':
    main()
