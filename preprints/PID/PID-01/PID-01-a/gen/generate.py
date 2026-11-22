#!/usr/bin/env python3
"""Exhaustive enumeration of case structures for PID-01-a (Appendix A).

A case structure is a finite layered directed acyclic graph of person-stages
issuing from one original stage o at time 0.  Every stage at time t >= 1 has
one or two parents at time t-1.  Each stage has a realizer kind: H (living
human neural tissue, the kind of the original) or M (another kind, e.g. a
computer).  Each edge carries (a) a degree of psychological connectedness in
{0, 1, 2} (0: no strong connection; 1: strong but partial; 2: full, as over
an ordinary day), and (b) whether the later stage continues the life of the
earlier stage's organism (L).  The realizer-kind label of an edge (same /
other) is derived from the kinds of its endpoints.

Constraints: an L edge joins two H stages; an edge of degree 0 is an L edge
(an edge carries psychology, life, or both); a stage has at most one incoming
L edge (a human life is the continuation of at most one earlier life) and a
stage has at most one outgoing L edge (human lives do not divide).

Bound: at most 3 times after the original, at most 2 stages per time, at most
4 stages after the original, at most 2 parents per stage, at most one stage
realized in a thing of another kind.  Cases are counted up to isomorphism
(time-preserving relabelling of stages); each class is represented by its
canonical form (lexicographically least level-by-level encoding).

The program computes, for every stage, the verdict of the PID-01 criterion and
of four rival criteria, and checks the numbered results of the manuscript.
It writes:
  cases.tex   the tables (longtable rows, grouped by height and size)
  stats.tex   macros with the summary statistics used in the preface
Python 3 standard library only; output is deterministic.
"""
import itertools
import os
import sys
from collections import Counter, defaultdict

MAX_T, MAX_W, MAX_S, MAX_PAR, MAX_M = 3, 2, 4, 2, 1
HERE = os.path.dirname(os.path.abspath(__file__))

# ---------------------------------------------------------------- enumeration

def edge_labels(kp, kc):
    if kp == 'H' and kc == 'H':
        return [(0, 1), (1, 0), (1, 1), (2, 0), (2, 1)]
    return [(1, 0), (2, 0)]


def stage_options(prev):
    n = len(prev)
    opts = []
    for k in 'HM':
        for r in range(1, MAX_PAR + 1):
            for ps in itertools.combinations(range(n), r):
                for labs in itertools.product(*[edge_labels(prev[p], k) for p in ps]):
                    if sum(l for _, l in labs) > 1:
                        continue
                    opts.append((k, tuple((p, d, l) for p, (d, l) in zip(ps, labs))))
    return opts


def next_levels(prev):
    opts = stage_options(prev)
    for w in range(1, MAX_W + 1):
        for combo in itertools.combinations_with_replacement(range(len(opts)), w):
            st = [opts[i] for i in combo]
            out = [0] * len(prev)
            for _, ps in st:
                for p, _, l in ps:
                    out[p] += l
            if max(out) > 1:
                continue
            yield tuple(st)


def canon(levels):
    maps = [(0,)]
    res = []
    for lev in levels:
        best, newmaps = None, []
        for m in maps:
            enc = [(k, tuple(sorted((m[p], d, l) for p, d, l in ps))) for k, ps in lev]
            order = sorted(range(len(lev)), key=lambda i: enc[i])
            e = tuple(enc[i] for i in order)
            if best is None or e < best:
                best, newmaps = e, []
            if e == best:
                groups = [list(g) for _, g in itertools.groupby(order, key=lambda i: enc[i])]
                for perms in itertools.product(*[itertools.permutations(g) for g in groups]):
                    flat = [i for g in perms for i in g]
                    nm = [0] * len(lev)
                    for newi, oldi in enumerate(flat):
                        nm[oldi] = newi
                    newmaps.append(tuple(nm))
        maps = sorted(set(newmaps))
        res.append(best)
    return tuple(res)


def n_machine(c):
    return sum(s[0] == 'M' for lev in c for s in lev)


def enumerate_cases():
    allc, frontier = set(), {()}
    for _ in range(MAX_T):
        nf = set()
        for c in frontier:
            prev = [s[0] for s in c[-1]] if c else ['H']
            used = sum(len(l) for l in c)
            for lev in next_levels(prev):
                if used + len(lev) > MAX_S:
                    continue
                nc = canon(list(c) + [lev])
                if n_machine(nc) > MAX_M:
                    continue
                nf.add(nc)
        allc |= nf
        frontier = nf
    return allc

# ---------------------------------------------------------------- semantics

LETTERS = 'ab'


def stages_of(c):
    """List of stage keys (t, i); root is (0, 0)."""
    out = [(0, 0)]
    for t, lev in enumerate(c, 1):
        out += [(t, i) for i in range(len(lev))]
    return out


def kind(c, s):
    return 'H' if s[0] == 0 else c[s[0] - 1][s[1]][0]


def parents(c, s):
    if s[0] == 0:
        return []
    return [((s[0] - 1, p), d, l) for p, d, l in c[s[0] - 1][s[1]][1]]


def children(c, x):
    t = x[0]
    if t >= len(c):
        return []
    out = []
    for i, (_, ps) in enumerate(c[t]):
        for p, d, l in ps:
            if p == x[1]:
                out.append(((t + 1, i), d, l))
    return out


def level(c, t):
    return [(0, 0)] if t == 0 else [(t, i) for i in range(len(c[t - 1]))]


def candidates(c, x):
    """Children of x psychologically continuous with it through a cause of the
    right kind in one step (degree >= 1, realized in kind H)."""
    if kind(c, x) != 'H':
        return []
    return [(y, d, l) for y, d, l in children(c, x) if d >= 1 and kind(c, y) == 'H']


def contested(c, x, y):
    cand = candidates(c, x)
    if len(cand) >= 2:
        return True
    for z, d, _ in parents(c, y):
        if z != x and d >= 1 and kind(c, z) == 'H':
            return True
    return False


def pid01(c):
    """Forward computation of the criterion (Definition 4.3 in the text).
    Returns dict stage -> code in {O, I, L, E, D, U, N}."""
    orig = {(0, 0)}
    verdict = {(0, 0): 'O'}
    for t in range(1, len(c) + 1):
        new = set()
        info = {}
        for x in [s for s in level(c, t - 1) if s in orig]:
            cand = candidates(c, x)
            winners = [y for y, d, l in cand if (not contested(c, x, y)) or l]
            for y, d, l in cand:
                info[y] = 'I' if y in winners else ('L' if winners else 'E')
            new |= set(winners)
        orig = new
        R, P = rk_cont(c), psy_cont(c)
        for y in level(c, t):
            if y in info:
                verdict[y] = info[y]
            elif R[y]:
                verdict[y] = 'D'
            elif P[y]:
                verdict[y] = 'U'
            else:
                verdict[y] = 'N'
    return verdict


def rk_cont(c):
    R = {(0, 0): True}
    for s in stages_of(c)[1:]:
        R[s] = kind(c, s) == 'H' and any(R[p] and d >= 1 for p, d, _ in parents(c, s))
    return R


def psy_cont(c):
    P = {(0, 0): True}
    for s in stages_of(c)[1:]:
        P[s] = any(P[p] and d >= 1 for p, d, _ in parents(c, s))
    return P


def bio(c):
    B = {(0, 0): True}
    for s in stages_of(c)[1:]:
        B[s] = any(B[p] and l for p, _, l in parents(c, s))
    return B


def pid01_paths(c):
    """Independent path characterization (Proposition 4.4): y is the original
    iff some path from o to y consists of admissible steps, a step x->y being
    admissible iff y is a candidate of x and the step is uncontested or
    continues x's life."""
    res = {(0, 0): True}
    def adm(x):
        return [y for y, d, l in candidates(c, x) if (not contested(c, x, y)) or l]
    reach = {(0, 0)}
    frontier = [(0, 0)]
    while frontier:
        x = frontier.pop()
        for y in adm(x):
            if y not in reach:
                reach.add(y)
                frontier.append(y)
    for s in stages_of(c):
        res[s] = s in reach
    return res


def rival_pb(c):
    """Non-branching criterion with kind condition and no tie-breaker."""
    orig, res = {(0, 0)}, {(0, 0): True}
    for t in range(1, len(c) + 1):
        new = set()
        for x in [s for s in level(c, t - 1) if s in orig]:
            for y, d, l in candidates(c, x):
                if not contested(c, x, y):
                    new.add(y)
        for y in level(c, t):
            res[y] = y in new
        orig = new
    return res


def rival_cc(c):
    """Closest continuer by degree of psychological connectedness: in a
    contest the candidate strictly closest wins, otherwise none."""
    orig, res = {(0, 0)}, {(0, 0): True}
    for t in range(1, len(c) + 1):
        new = set()
        for x in [s for s in level(c, t - 1) if s in orig]:
            cand = candidates(c, x)
            for y, d, l in cand:
                rivals = [d2 for y2, d2, _ in cand if y2 != y]
                rivals += [d2 for z, d2, _ in parents(c, y)
                           if z != x and d2 >= 1 and kind(c, z) == 'H']
                if all(d > r for r in rivals):
                    new.add(y)
        for y in level(c, t):
            res[y] = y in new
        orig = new
    return res


def rival_wide(c):
    """Wide non-branching criterion, branching read globally: y is the
    original iff y is psychologically continuous with o by any reliable cause
    and at no time in the whole case are two stages so continuous."""
    P = psy_cont(c)
    branches = any(sum(P[s] for s in level(c, t)) >= 2 for t in range(1, len(c) + 1))
    return {s: (s == (0, 0)) or (P[s] and not branches) for s in stages_of(c)}


def name(s):
    return 'o' if s[0] == 0 else f"{s[0]}{LETTERS[s[1]]}"


def notation(c):
    levs = []
    for t, lev in enumerate(c, 1):
        items = []
        for i, (k, ps) in enumerate(lev):
            ed = ','.join(f"{name((t - 1, p)) if t > 1 else 'o'}{d}{'L' if l else ''}" for p, d, l in ps)
            items.append(f"{t}{LETTERS[i]}{'*' if k == 'M' else ''}<{ed}")
        levs.append(' '.join(items))
    return ' / '.join(levs)

# ---------------------------------------------------------------- analysis

def contests(c, orig_set):
    out = []
    for t in range(1, len(c) + 1):
        for x in level(c, t - 1):
            if x not in orig_set:
                continue
            cand = candidates(c, x)
            con = [y for y, _, _ in cand if contested(c, x, y)]
            if con:
                out.append((x, cand, con))
    return out


def analyse(c):
    v = pid01(c)
    I = {s for s, code in v.items() if code in 'OI'}
    B, R, P = bio(c), rk_cont(c), psy_cont(c)
    pb, cc, wide = rival_pb(c), rival_cc(c), rival_wide(c)
    path = pid01_paths(c)
    st = stages_of(c)
    a = {'v': v, 'I': I, 'B': B}
    # Check 1 (Theorem 4.6): at most one original stage at each time.
    for t in range(0, len(c) + 1):
        assert sum(s in I for s in level(c, t)) <= 1, ('uniqueness', c)
    # Check 2 (Corollary 4.7): the original's stages form one unbroken chain
    # from o: each original stage at t >= 1 has an original parent, and the
    # times at which the original exists form an initial segment.
    for s in I - {(0, 0)}:
        assert any(p in I for p, _, _ in parents(c, s)), ('chain', c)
    times = sorted({s[0] for s in I})
    assert times == list(range(len(times))), ('segment', c)
    # Check 3 (Proposition 4.4): forward and path characterizations agree.
    for s in st:
        assert (s in I) == path[s], ('paths', c)
    # Check 4 (Theorem 5.3, tie-breaker): in every contest at an original
    # stage, a candidate is the original iff it is uncontested or continues
    # the life; if some contested candidate continues the life it alone is
    # the original among the contested; if none does, no contested
    # candidate is the original ("neither").
    cts = contests(c, I)
    kinds = []
    for x, cand, con in cts:
        lifers = [y for y, d, l in cand if l]
        winners = [y for y, _, _ in cand if y in I]
        assert len(winners) <= 1
        if len(cand) >= 2:
            if lifers:
                assert winners == lifers, ('tie', c)
                kinds.append('B')
            else:
                assert winners == [], ('neither', c)
                kinds.append('E')
        else:
            y = cand[0][0]
            assert (y in I) == bool(cand[0][2]), ('fusion', c)
            kinds.append('F')
    a['contests'] = kinds
    # Check 5 (Proposition 5.6, kind condition): no stage that is continuous
    # with o only through a realizer of another kind, or that is realized in
    # another kind, is the original.
    for s in st:
        if s in I:
            assert R[s] and kind(c, s) == 'H', ('kind', c)
    # Ordinary stages (Definition 6.1): reached from o by a path of life
    # edges of degree >= 1 none of whose steps is contested.
    ordin = {(0, 0)}
    for t in range(1, len(c) + 1):
        for y in level(c, t):
            for p, d, l in parents(c, y):
                if p in ordin and l and d >= 1 and not contested(c, p, y):
                    ordin.add(y)
    a['ordinary'] = ordin
    # Check 6 (Theorem 6.2): at every ordinary stage, the criterion, the
    # biological criterion and the bodily criterion all give identity.
    for s in ordin:
        assert s in I and B[s], ('ordinary', c)
    # Check 7 (Proposition 6.4): in a case with no contest, the criterion
    # and the biological criterion disagree at a stage only if the stage is
    # not ordinary, i.e. the psychology has left the organism or the organism
    # has lost the psychology somewhere on the way.
    if not cts:
        for s in st:
            if (s in I) != B[s]:
                assert s not in ordin
    # Check 8 (Theorem 6.6, temporal locality): verdicts on stages up to time
    # h' do not change when the case is truncated at h'.
    for h in range(1, len(c)):
        tv = pid01(c[:h])
        for s in stages_of(c[:h]):
            assert tv[s] == v[s], ('locality', c)
    a['wide_nonlocal'] = False
    for h in range(1, len(c)):
        tw = rival_wide(c[:h])
        if any(tw[s] != wide[s] for s in stages_of(c[:h])):
            a['wide_nonlocal'] = True
    # Disagreements with rivals.
    dis = {}
    for lab, r in (('C', cc), ('P', pb), ('W', wide)):
        ds = [name(s) for s in st if r[s] != (s in I)]
        if ds:
            dis[lab] = ds
    a['dis'] = dis
    a['bio_dis'] = [s for s in st if B[s] != (s in I)]
    # classification
    if not cts:
        cl = 'N'
    else:
        cl = ''.join(sorted(set(kinds), key='BEF'.index))
    a['class'] = cl
    a['machine'] = any(kind(c, s) == 'M' for s in st)
    return a

# ---------------------------------------------------------------- named cases

def lev(*stages):
    return tuple(stages)


NAMED = {
    'Ordinary': [lev(('H', ((0, 2, 1),)))],
    'Disrupted': [lev(('H', ((0, 0, 1),)))],
    'Teleport': [lev(('H', ((0, 2, 0),)))],
    'BranchLine': [lev(('H', ((0, 2, 0),)), ('H', ((0, 2, 1),)))],
    'BranchLineLate': [lev(('H', ((0, 2, 0),)), ('H', ((0, 2, 1),))),
                       lev(('H', ((0, 2, 1),)),)],
    'Fission': [lev(('H', ((0, 2, 0),)), ('H', ((0, 2, 0),)))],
    'FissionUneven': [lev(('H', ((0, 1, 0),)), ('H', ((0, 2, 0),)))],
    'BranchLineWeak': [lev(('H', ((0, 2, 0),)), ('H', ((0, 1, 1),)))],
    'UploadD': [lev(('M', ((0, 2, 0),)))],
    'UploadN': [lev(('H', ((0, 2, 1),)), ('M', ((0, 2, 0),)))],
    'UploadDownload': [lev(('M', ((0, 2, 0),))), lev(('H', ((0, 2, 0),)))],
    'TeleBranch': [lev(('H', ((0, 2, 0),))),
                   lev(('H', ((0, 2, 0),)), ('H', ((0, 2, 1),)))],
    'FusionLife': [lev(('H', ((0, 2, 0),)), ('H', ((0, 2, 1),))),
                   lev(('H', ((0, 2, 0), (1, 2, 1))),)],
    'FusionNone': [lev(('H', ((0, 2, 0),)), ('H', ((0, 2, 1),))),
                   lev(('H', ((0, 2, 0), (1, 2, 0))),)],
    'Transplant': [lev(('H', ((0, 2, 0),)), ('H', ((0, 0, 1),)))],
    'BranchLineTele': [lev(('H', ((0, 2, 0),)), ('H', ((0, 2, 1),))),
                       lev(('H', ((0, 2, 0),)), ('H', ((1, 2, 1),)))],
    'FissionLater': [lev(('H', ((0, 2, 0),)), ('H', ((0, 2, 0),))),
                     lev(('H', ((0, 2, 1),)), ('H', ((1, 2, 1),)))],
    'BranchLineThenTele': [lev(('H', ((0, 2, 0),)), ('H', ((0, 2, 1),))),
                           lev(('H', ((0, 2, 1),)), ('H', ((1, 2, 0),)))],
    'SleepLong': [lev(('H', ((0, 2, 1),))), lev(('H', ((0, 1, 1),))),
                  lev(('H', ((0, 1, 1),)))],
}

# ---------------------------------------------------------------- output

VERD = {'O': 'o', 'I': 'I', 'L': 'L', 'E': 'E', 'D': 'D', 'U': 'U', 'N': 'N'}


def macro_name(k):
    return 'case' + k


def main():
    cases = enumerate_cases()
    def key(c):
        return (len(c), sum(len(l) for l in c), n_machine(c),
                sum(len(s[1]) for l in c for s in l), c)
    order = sorted(cases, key=key)
    ids = {}
    counters = Counter()
    pref = {1: 'A', 2: 'B', 3: 'C'}
    for c in order:
        counters[len(c)] += 1
        ids[c] = f"{pref[len(c)]}{counters[len(c)]:04d}"
    stats = Counter()
    by_group = defaultdict(list)
    for c in order:
        a = analyse(c)
        by_group[(len(c), sum(len(l) for l in c))].append((c, a))
        stats['cases'] += 1
        stats['stages'] += sum(len(l) for l in c)
        stats['h%d' % len(c)] += 1
        stats['cls' + a['class']] += 1
        if a['machine']:
            stats['machine'] += 1
        if any(len(s[1]) > 1 for l in c for s in l):
            stats['fusionstruct'] += 1
        for code in a['v'].values():
            stats['v' + code] += 1
        stats['ordstages'] += len(a['ordinary']) - 1
        for lab in 'CPW':
            if lab in a['dis']:
                stats['dis' + lab] += 1
        if a['wide_nonlocal']:
            stats['widenonlocal'] += 1
        if a['bio_dis']:
            stats['biodis'] += 1
            if a['class'] == 'N':
                stats['biodisN'] += 1
        if a['class'] == 'N':
            stats['nonbranching'] += 1
        # Branch-Line defect of the pure non-branching criterion: a stage
        # that continues the original's life and is the original by PID-01
        # is denied identity by the criterion without tie-breaker.
        if 'P' in a['dis']:
            stats['pbdefect'] += 1
        for k in a['contests']:
            stats['contest' + k] += 1
    # named cases
    named = {}
    for k, levs in NAMED.items():
        cc_ = canon(levs)
        assert cc_ in ids, k
        named[k] = ids[cc_]
    # write tables
    rows = []
    hnames = {1: 'one', 2: 'two', 3: 'three'}
    for (h, s), items in sorted(by_group.items()):
        rows.append(f"\\subsection*{{Height {h}, {s} stage{'s' if s > 1 else ''} after the original "
                    f"({len(items)} case{'s' if len(items) > 1 else ''})}}")
        rows.append("\\begin{casetable}")
        for c, a in items:
            st = stages_of(c)[1:]
            ver = ''
            bio_s = ''
            prev_t = 1
            for s in st:
                if s[0] != prev_t:
                    ver += '/'
                    bio_s += '/'
                    prev_t = s[0]
                ver += VERD[a['v'][s]]
                bio_s += '+' if a['B'][s] else '{-}'  # braces block the -- ligature
            grouped = {}
            for lab, v in a['dis'].items():
                grouped.setdefault(tuple(v), []).append(lab)
            dis = ' '.join(f"{''.join(labs)}:{','.join(v)}" for v, labs in grouped.items())
            cls = a['class']
            rows.append(f"{ids[c]} & {notation(c)} & {ver} & {bio_s} & {cls} & {dis} \\\\")
        rows.append("\\end{casetable}")
    with open(os.path.join(HERE, 'cases.tex'), 'w') as f:
        f.write("% Generated by generate.py; do not edit.\n")
        f.write('\n'.join(rows) + '\n')
    with open(os.path.join(HERE, 'stats.tex'), 'w') as f:
        f.write("% Generated by generate.py; do not edit.\n")
        def mac(n, v):
            f.write(f"\\newcommand{{\\{n}}}{{{v}}}\n")
        def fmt(n):
            return f"{n:,}".replace(',', '{,}')
        keys = ['cases', 'stages', 'h1', 'h2', 'h3', 'clsN', 'clsB', 'clsE', 'clsF', 'clsBE', 'clsBF',
                'clsEF', 'clsBEF', 'machine', 'fusionstruct', 'vI', 'vL', 'vE', 'vD', 'vU', 'vN',
                'ordstages', 'disC', 'disP', 'disW', 'widenonlocal', 'biodis', 'biodisN',
                'nonbranching', 'pbdefect', 'contestB', 'contestE', 'contestF']
        digits = {'1': 'one', '2': 'two', '3': 'three'}
        for k in keys:
            mac('st' + ''.join(digits.get(ch, ch) for ch in k), fmt(stats[k]))
        for k, v in named.items():
            mac(macro_name(k), v)
    for k in sorted(stats):
        print(k, stats[k])
    for k, v in named.items():
        print(k, v)


if __name__ == '__main__':
    main()
