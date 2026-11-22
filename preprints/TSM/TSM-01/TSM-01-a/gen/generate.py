#!/usr/bin/env python3
"""Generator for the computed part of TSM-01-a ("On the Reality of Time").

Enumerates every finite branching-time frame (a finite tree of moments ordered
by earlier-than: a finite partial order with a least moment in which the
predecessors of each moment are linearly ordered) with at most NMAX moments, one
representative per isomorphism class, and for each frame computes and checks:

  * the histories (maximal chains), their number and the length of the longest;
  * the automorphism group order, the orbits on moments and on histories;
  * for EVERY valuation V of one atom p (all 2^n subsets of the moments) and
    every moment m, the moment-relative settledness of F p ("it will be that p")
    at m: settled true, settled false, or open;
  * Check M (Theorem 6.6 of the manuscript): if the tenseless proposition
    expressed by F p at m is settled at m, it is settled, with the same value,
    at every moment m' later than m;
  * Check B (Proposition 6.7): truth relative to a history is bivalent, and
    F p is open at m for some valuation iff more than one history passes
    through m; profiles of h(m) along each history are non-increasing
    (Corollary 6.8); reversals (Proposition 6.9) and resolutions are counted;
  * automorphism orbits on moments and histories (Propositions 4.8, 6.10);
  * Check A (Theorem 4.4, Proposition 4.6): the moment-relative A-assignments
    recover the earlier-than order exactly and commute with every automorphism,
    while no single (monadic) A-assignment gives every moment the
    determination "present" unless the frame has one moment.

Python 3 standard library only; output is deterministic.
Usage: python3 generate.py   (writes the .tex files next to this script)
"""

import os
from math import factorial
from itertools import combinations

NMAX_DETAIL = 10    # frames up to this size get per-moment rows
NMAX_HIST = 9       # frames up to this size get per-history rows
NMAX = 11           # frames of size NMAX get one summary row each
NCROSS = 10         # independent labelled enumeration up to this size
NBRUTE = 6          # brute-force recomputation of settledness up to this size

HERE = os.path.dirname(os.path.abspath(__file__))

# Otter (1948): numbers of rooted unlabelled trees, n = 1..11
OTTER = [1, 1, 2, 4, 9, 20, 48, 115, 286, 719, 1842]


# ---------------------------------------------------------------- canonical forms
def canon_from_parents(par):
    """Canonical level sequence of the rooted tree given by a parent array
    (par[0] = -1). Children are ordered by their own canonical sequence,
    largest first, so isomorphic trees get the same sequence."""
    n = len(par)
    ch = [[] for _ in range(n)]
    for v in range(1, n):
        ch[par[v]].append(v)

    def rec(v):
        subs = sorted((rec(c) for c in ch[v]), reverse=True)
        out = [0]
        for s in subs:
            out.extend(x + 1 for x in s)
        return tuple(out)

    return rec(0)


def parents_from_levels(lv):
    par = [-1] * len(lv)
    stack = []
    for i, l in enumerate(lv):
        while len(stack) > l:
            stack.pop()
        par[i] = stack[-1] if stack else -1
        stack.append(i)
    return par


def enumerate_trees(nmax):
    """All canonical level sequences with n <= nmax moments, by adding a leaf
    in every possible place to every tree with one moment fewer."""
    by_n = {1: {(0,)}}
    for n in range(2, nmax + 1):
        s = set()
        for lv in by_n[n - 1]:
            par = parents_from_levels(lv)
            for v in range(n - 1):
                s.add(canon_from_parents(par + [v]))
        by_n[n] = s
    return {n: sorted(by_n[n], reverse=True) for n in by_n}


def cross_check(nmax):
    """Independent count: canonicalize every parent array with par[i] < i
    (every rooted tree has such a labelling, e.g. in breadth-first order)."""
    res = {}
    for n in range(1, nmax + 1):
        seen = set()
        par = [-1] + [0] * (n - 1)

        def go(i):
            if i == n:
                seen.add(canon_from_parents(par))
                return
            for p in range(i):
                par[i] = p
                go(i + 1)
        go(1)
        res[n] = (factorial(n - 1), seen)
    return res


# ---------------------------------------------------------------- one frame
def ALLMASK(n):
    return (1 << (1 << n)) - 1


def atom_pattern(x, n):
    """Bitset over the 2^n valuations: bit V is set iff moment x is in V."""
    N = 1 << n
    blk = 1 << x
    unit = ((1 << blk) - 1) << blk
    return ((1 << N) - 1) // ((1 << (2 * blk)) - 1) * unit


def analyse(lv):
    n = len(lv)
    par = parents_from_levels(lv)
    ch = [[] for _ in range(n)]
    for v in range(1, n):
        ch[par[v]].append(v)
    # subtree spans in preorder
    size = [1] * n
    for v in range(n - 1, 0, -1):
        size[par[v]] += size[v]
    below = [0] * n          # bitmask of moments strictly earlier
    for v in range(1, n):
        below[v] = below[par[v]] | (1 << par[v])
    above = [0] * n          # strictly later
    for v in range(n):
        for w in range(v + 1, v + size[v]):
            above[v] |= 1 << w
    leaves = [v for v in range(n) if not ch[v]]
    chain = {l: below[l] | (1 << l) for l in leaves}   # history through leaf l
    hist_through = [[l for l in leaves if chain[l] >> m & 1] for m in range(n)]

    # Lemma 6.5: every history through a later moment passes through the earlier
    for m in range(n):
        for mp in range(n):
            if above[m] >> mp & 1:
                assert set(hist_through[mp]) <= set(hist_through[m])
    # histories are exactly the maximal chains: pairwise incomparable leaves,
    # and every chain extends to one through a leaf
    for a, b in combinations(leaves, 2):
        assert not (above[a] >> b & 1) and not (above[b] >> a & 1)

    # automorphisms
    sub = [None] * n

    def subcanon(v):
        s = sorted((subcanon(c) for c in ch[v]), reverse=True)
        out = [0]
        for t in s:
            out.extend(x + 1 for x in t)
        sub[v] = tuple(out)
        return sub[v]
    subcanon(0)
    aut = 1
    for v in range(n):
        cnt = {}
        for c in ch[v]:
            cnt[sub[c]] = cnt.get(sub[c], 0) + 1
        for k in cnt.values():
            aut *= factorial(k)
    orbit = [None] * n
    lab = {}
    for v in range(n):
        key = (orbit[par[v]] if v else -1, sub[v])
        orbit[v] = lab.setdefault(key, len(lab))
    osize = {}
    for v in range(n):
        osize[orbit[v]] = osize.get(orbit[v], 0) + 1
    n_orb = len(osize)
    fixed_m = sum(1 for v in range(n) if osize[orbit[v]] == 1)
    leaf_orbits = {orbit[l] for l in leaves}
    fixed_h = sum(1 for l in leaves if osize[orbit[l]] == 1)
    # generators: swaps of adjacent identical sibling subtrees (preorder is canonical)
    gens = []
    for v in range(n):
        cs = ch[v]
        for a, b in zip(cs, cs[1:]):
            if sub[a] == sub[b]:
                g = list(range(n))
                for j in range(size[a]):
                    g[a + j], g[b + j] = b + j, a + j
                gens.append(g)
    # sanity: generated group order equals product formula (small cases)
    if aut <= 5040 and gens:
        grp = {tuple(range(n))}
        frontier = [tuple(range(n))]
        while frontier:
            nf = []
            for h in frontier:
                for g in gens:
                    k = tuple(g[h[i]] for i in range(n))
                    if k not in grp:
                        grp.add(k)
                        nf.append(k)
            frontier = nf
        assert len(grp) == aut
        for g in grp:   # each is an order automorphism
            for x in range(n):
                for y in range(n):
                    assert (above[x] >> y & 1) == (above[g[x]] >> g[y] & 1)

    # ---- Check A: A-assignments (Definition 4.2)
    def A(m, x):
        if x == m:
            return 'N'
        if above[x] >> m & 1:
            return 'P'      # x earlier than m
        if above[m] >> x & 1:
            return 'F'
        return 'O'
    for m in range(n):
        for x in range(n):
            # stage order recovers earlier-than (Proposition 4.6 (a), (b))
            assert (A(m, x) == 'P') == bool(above[x] >> m & 1)
            assert (A(m, x) == 'F') == (A(x, m) == 'P')
            for g in gens:   # equivariance (Proposition 4.6 (c))
                assert A(g[m], g[x]) == A(m, x)
    # monadic A-assignments: each coherent one has exactly one present
    # moment, so it gives "present" to every moment iff n == 1 (Proposition 4.6 (d), Theorem 4.4)
    monadic_ok = [all(A(m, x) == 'N' for x in range(n)) for m in range(n)]
    assert any(monadic_ok) == (n == 1)

    # ---- settledness over all valuations
    ALL = ALLMASK(n)
    B = [atom_pattern(x, n) for x in range(n)]

    def T(m, l):        # valuations making "F p at m" true on history l
        s = 0
        bits = above[m] & chain[l]
        x = 0
        while bits:
            if bits & 1:
                s |= B[x]
            bits >>= 1
            x += 1
        return s

    Tml = {(m, l): T(m, l) for m in range(n) for l in hist_through[m]}
    ST, SF, OP = [], [], []
    for m in range(n):
        st, anyt = ALL, 0
        for l in hist_through[m]:
            st &= Tml[(m, l)]
            anyt |= Tml[(m, l)]
        sf = ALL & ~anyt
        ST.append(st)
        SF.append(sf)
        OP.append(ALL & ~st & ~sf)
        # Check B: bivalence relative to a history (true/false partition),
        # and the openness criterion
        for l in hist_through[m]:
            t = Tml[(m, l)]
            assert (t | (ALL & ~t)) == ALL and (t & (ALL & ~t)) == 0
        assert (OP[m] != 0) == (len(hist_through[m]) >= 2)
        assert (st & sf) == 0

    # ---- Check M: monotonicity (Theorem 6.6), resolutions and reversals
    mono_pairs = 0
    resolutions = 0
    reversals = 0
    for m in range(n):
        for mp in range(n):
            if not (above[m] >> mp & 1):
                continue
            mono_pairs += 1
            st2, anyt2 = ALL, 0
            for l in hist_through[mp]:
                st2 &= Tml[(m, l)]
                anyt2 |= Tml[(m, l)]
            sf2 = ALL & ~anyt2
            assert ST[m] & ~st2 == 0 and SF[m] & ~sf2 == 0      # Theorem 6.6
            resolutions += (OP[m] & (st2 | sf2)).bit_count()
            reversals += (ST[m] & SF[mp]).bit_count()          # Prop. 6.9

    # single-point valuations p = {x}: settledness of F p at m
    vec = []
    for m in range(n):
        s = []
        for x in range(n):
            if not (above[m] >> x & 1):
                s.append('-')
            elif len(hist_through[x]) == len(hist_through[m]):
                s.append('+')
            else:
                s.append('?')
        vec.append(''.join(s))
        # consistency with the bitset computation
        for x in range(n):
            V = 1 << x
            bit = lambda S: S >> V & 1
            c = '+' if bit(ST[m]) else '-' if bit(SF[m]) else '?'
            assert c == vec[m][x]

    # histories: chain, profile of h(m) along it, settling moment, orbit size
    hrows = []
    for i, l in enumerate(leaves):
        ms = [v for v in range(n) if chain[l] >> v & 1]       # preorder = earlier first
        prof = [len(hist_through[v]) for v in ms]
        assert all(a >= b for a, b in zip(prof, prof[1:]))    # Corollary 6.8
        assert prof[0] == len(leaves) and prof[-1] == 1
        settle = next(v for v in ms if len(hist_through[v]) == 1)
        hrows.append(dict(i=i, chain=ms, prof=prof, settle=settle,
                          orb=osize[orbit[l]]))

    height = max(lv) + 1
    branching = sum(1 for v in range(n) if len(ch[v]) >= 2)
    rows = []
    for m in range(n):
        rows.append(dict(m=m, par=par[m], lvl=lv[m], h=len(hist_through[m]),
                         orb=osize[orbit[m]], st=ST[m].bit_count(),
                         sf=SF[m].bit_count(), op=OP[m].bit_count(), vec=vec[m]))
    return dict(lv=lv, n=n, H=len(leaves), height=height, branching=branching,
                aut=aut, n_orb=n_orb, fixed_m=fixed_m, h_orb=len(leaf_orbits),
                fixed_h=fixed_h, mono=mono_pairs * (1 << n), pairs=mono_pairs,
                res=resolutions, rev=reversals, rows=rows, hrows=hrows,
                open_total=sum(r['op'] for r in rows))


def brute(lv):
    """Direct recomputation of settled-true/false/open counts (no bitsets)."""
    n = len(lv)
    par = parents_from_levels(lv)
    earlier = lambda a, b: a != b and _anc(par, a, b)
    leaves = [v for v in range(n) if all(par[w] != v for w in range(n))]
    hist = [[w for w in range(n) if w == l or earlier(w, l)] for l in leaves]
    out = []
    for m in range(n):
        hs = [h for h in hist if m in h]
        st = sf = op = 0
        for V in range(1 << n):
            vals = {any(V >> x & 1 and earlier(m, x) for x in h) for h in hs}
            if vals == {True}:
                st += 1
            elif vals == {False}:
                sf += 1
            else:
                op += 1
        out.append((st, sf, op))
    return out


def _anc(par, a, b):
    while b != -1:
        b = par[b]
        if b == a:
            return True
    return False


# ---------------------------------------------------------------- output
def levstr(lv):
    return ''.join('0123456789ab'[x] for x in lv)


def fid(n, k):
    return "T%d.%0*d" % (n, len(str(OTTER[n - 1])), k)


def main():
    trees = enumerate_trees(NMAX)
    for n in range(1, NMAX + 1):
        assert len(trees[n]) == OTTER[n - 1], (n, len(trees[n]))
    cc = cross_check(NCROSS)
    for n in range(1, NCROSS + 1):
        assert cc[n][1] == set(trees[n])

    stats = []
    detail = []
    summary11 = []
    named = {}
    for n in range(1, NMAX + 1):
        agg = dict(n=n, frames=0, H=0, rigid=0, nofixh=0, mono=0, res=0,
                   rev=0, open=0, maxaut=0, lin=0)
        for k, lv in enumerate(trees[n], 1):
            d = analyse(lv)
            d['id'] = fid(n, k)
            named[levstr(lv)] = d['id']
            if n <= NBRUTE:
                b = brute(lv)
                for r, (st, sf, op) in zip(d['rows'], b):
                    assert (r['st'], r['sf'], r['op']) == (st, sf, op)
            agg['frames'] += 1
            agg['H'] += d['H']
            agg['rigid'] += d['aut'] == 1
            agg['nofixh'] += d['fixed_h'] == 0
            agg['mono'] += d['mono']
            agg['res'] += d['res']
            agg['rev'] += d['rev']
            agg['open'] += d['open_total']
            agg['maxaut'] = max(agg['maxaut'], d['aut'])
            agg['lin'] += d['H'] == 1
            if n <= NMAX_DETAIL:
                detail.append(d)
            else:
                summary11.append(d)
        agg['labelled'] = factorial(n - 1) if n <= NCROSS else None
        stats.append(agg)

    # ---- detailed table
    def head(d):
        return (r"\multicolumn{9}{@{}l@{}}{\rule{0pt}{2.6ex}\textbf{%s}\enspace "
                r"\texttt{%s}\enspace $n{=}%d$, $|H|{=}%d$, len %d, br %d, "
                r"$|\mathrm{Aut}|{=}%d$, orb %d/%d, hist-orb %d/%d; "
                r"M %d, res %d, rev %d: ok}\\*" % (
                    d['id'], levstr(d['lv']), d['n'], d['H'], d['height'],
                    d['branching'], d['aut'], d['n_orb'], d['fixed_m'],
                    d['h_orb'], d['fixed_h'], d['mono'], d['res'], d['rev']))

    with open(os.path.join(HERE, 'frames_detail.tex'), 'w') as f:
        f.write("% generated by gen/generate.py -- do not edit\n")
        f.write("{\\scriptsize\\setlength{\\tabcolsep}{4pt}\n")
        f.write("\\begin{longtable}{@{}rrrrrrrrl@{}}\n")
        hdr = ("$m$ & par & lvl & $h(m)$ & orb & st & sf & op & "
               "single-point vector $x=0,\\dots,n-1$\\\\\n\\midrule\n")
        f.write("\\toprule\n" + hdr + "\\endfirsthead\n")
        f.write("\\toprule\n" + hdr + "\\endhead\n")
        last_n = None
        for d in detail:
            if d['n'] != last_n:
                last_n = d['n']
                f.write("\\multicolumn{9}{@{}l@{}}{\\rule{0pt}{3.4ex}\\normalsize"
                        "\\bfseries Frames with %d moment%s (%d classes)}\\\\*\n"
                        % (d['n'], '' if d['n'] == 1 else 's', OTTER[d['n'] - 1]))
            f.write(head(d) + "\n")
            rs = d['rows']
            for i, r in enumerate(rs):
                end = "\\\\*" if i < len(rs) - 1 and i < 1 else "\\\\"
                f.write("%d & %s & %d & %d & %d & %d & %d & %d & \\texttt{%s}%s\n" % (
                    r['m'], '--' if r['par'] < 0 else str(r['par']), r['lvl'],
                    r['h'], r['orb'], r['st'], r['sf'], r['op'], r['vec'], end))
        f.write("\\bottomrule\n\\end{longtable}}\n")

    with open(os.path.join(HERE, 'histories.tex'), 'w') as f:
        f.write("% generated by gen/generate.py -- do not edit\n")
        f.write("{\\scriptsize\\setlength{\\tabcolsep}{4pt}\n")
        f.write("\\begin{longtable}{@{}llrlllr@{}}\n")
        hdr = ("frame & level sequence & $h$ & moments of $h$ & profile $h(m)$ along $h$ "
               "& settles at & orb\\\\\n\\midrule\n")
        f.write("\\toprule\n" + hdr + "\\endfirsthead\n\\toprule\n" + hdr + "\\endhead\n")
        for d in detail:
            if d['n'] > NMAX_HIST:
                continue
            for j, h in enumerate(d['hrows']):
                first = j == 0
                f.write("%s & %s & %d & \\texttt{%s} & \\texttt{%s} & %d & %d\\\\%s\n" % (
                    d['id'] if first else '', '\\texttt{%s}' % levstr(d['lv']) if first else '',
                    h['i'], '.'.join(str(v) for v in h['chain']),
                    '.'.join(str(v) for v in h['prof']), h['settle'], h['orb'],
                    '*' if j < len(d['hrows']) - 1 and j < 1 else ''))
        f.write("\\bottomrule\n\\end{longtable}}\n")

    with open(os.path.join(HERE, 'frames_eleven.tex'), 'w') as f:
        f.write("% generated by gen/generate.py -- do not edit\n")
        f.write("{\\scriptsize\\setlength{\\tabcolsep}{3.2pt}\n")
        f.write("\\begin{longtable}{@{}llrrrrrrrrrrr@{}}\n")
        hdr = ("id & level sequence & $|H|$ & len & br & $|\\mathrm{Aut}|$ & orb & fix "
               "& h-orb & h-fix & M & res & rev\\\\\n\\midrule\n")
        f.write("\\toprule\n" + hdr + "\\endfirsthead\n\\toprule\n" + hdr + "\\endhead\n")
        for d in summary11:
            f.write("%s & \\texttt{%s} & %d & %d & %d & %d & %d & %d & %d & %d & %d & %d & %d\\\\\n" % (
                d['id'], levstr(d['lv']), d['H'], d['height'], d['branching'],
                d['aut'], d['n_orb'], d['fixed_m'], d['h_orb'], d['fixed_h'],
                d['mono'], d['res'], d['rev']))
        f.write("\\bottomrule\n\\end{longtable}}\n")

    tot = {k: sum(a[k] for a in stats) for k in
           ('frames', 'H', 'rigid', 'nofixh', 'mono', 'res', 'rev', 'open', 'lin')}
    with open(os.path.join(HERE, 'stats.tex'), 'w') as f:
        f.write("% generated by gen/generate.py -- do not edit\n")
        f.write("{\\small\\setlength{\\tabcolsep}{4pt}\n\\begin{tabular}{@{}rrrrrrrrrr@{}}\n\\toprule\n")
        f.write("$n$ & frames & labelled & $\\sum|H|$ & linear & rigid & no fixed $h$ "
                "& M checks & resolutions & reversals\\\\\n\\midrule\n")
        for a in stats:
            f.write("%d & %d & %s & %d & %d & %d & %d & %d & %d & %d\\\\\n" % (
                a['n'], a['frames'], str(a['labelled']) if a['labelled'] else '--',
                a['H'], a['lin'], a['rigid'], a['nofixh'], a['mono'], a['res'], a['rev']))
        f.write("\\midrule\n all & %d & & %d & %d & %d & %d & %d & %d & %d\\\\\n" % (
            tot['frames'], tot['H'], tot['lin'], tot['rigid'], tot['nofixh'],
            tot['mono'], tot['res'], tot['rev']))
        f.write("\\bottomrule\n\\end{tabular}}\n")

    # macros with headline numbers for the prose
    with open(os.path.join(HERE, 'numbers.tex'), 'w') as f:
        f.write("% generated by gen/generate.py -- do not edit\n")
        f.write("\\newcommand{\\NFrames}{%d}\n" % tot['frames'])
        f.write("\\newcommand{\\NFramesDetail}{%d}\n" % len(detail))
        f.write("\\newcommand{\\NFramesEleven}{%d}\n" % len(summary11))
        f.write("\\newcommand{\\NMoments}{%d}\n" % sum(d['n'] for d in detail))
        f.write("\\newcommand{\\NMonoChecks}{%d}\n" % tot['mono'])
        f.write("\\newcommand{\\NResolutions}{%d}\n" % tot['res'])
        f.write("\\newcommand{\\NReversals}{%d}\n" % tot['rev'])
        f.write("\\newcommand{\\NRigid}{%d}\n" % tot['rigid'])
        f.write("\\newcommand{\\NNoFixH}{%d}\n" % tot['nofixh'])
        f.write("\\newcommand{\\NHist}{%d}\n" % tot['H'])
        f.write("\\newcommand{\\NHistRows}{%d}\n" % sum(d['H'] for d in detail if d['n'] <= NMAX_HIST))
        f.write("\\newcommand{\\NLabelled}{%d}\n" % sum(factorial(n - 1) for n in range(1, NCROSS + 1)))

    # a lookup for the author: interesting entries
    with open(os.path.join(HERE, 'index.txt'), 'w') as f:
        for d in detail + summary11:
            f.write("%s %s H=%d len=%d br=%d aut=%d orb=%d fix=%d horb=%d hfix=%d M=%d res=%d rev=%d\n" % (
                d['id'], levstr(d['lv']), d['H'], d['height'], d['branching'], d['aut'],
                d['n_orb'], d['fixed_m'], d['h_orb'], d['fixed_h'], d['mono'], d['res'], d['rev']))
    print("frames", tot['frames'], "detail", len(detail), "rows",
          sum(d['n'] for d in detail), "mono", tot['mono'], "rev", tot['rev'])


if __name__ == '__main__':
    main()
