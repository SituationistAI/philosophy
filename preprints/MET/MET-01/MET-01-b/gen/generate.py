#!/usr/bin/env python3
"""Generator for the computed part of MET-01-b, "The Instability of the Empty World".

Standard library only. All measures are computed and checked in exact rational
arithmetic (fractions.Fraction); decimals in the tables are display roundings of
exact values. Output: tab_*.tex in this directory, included by ../main.tex.

A world of W_n is an integer 0 <= w < 2^n; bit i-1 is set iff object a_i exists.
"""
import os
import random
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
NMAX_A = 12          # Volume A: families of admissible measures, n = 1..12
NMAX_UP = 5          # Volume C: exhaustive enumeration of up-sets, n = 1..5
NMAX_E = 12          # Volume E: perturbations, n = 2..10


def popcount(w):
    return bin(w).count("1")


def edges(n):
    """All pairs (w, w + a_i) with a_i absent in w."""
    for w in range(1 << n):
        for i in range(n):
            if not (w >> i) & 1:
                yield w, w | (1 << i)


def wstr(w, n):
    """World as a string a_1 ... a_n of 1 (exists) and 0 (does not)."""
    return "".join("1" if (w >> i) & 1 else "0" for i in range(n))


def fr(x):
    """Exact fraction in compact text."""
    if x.denominator == 1:
        return str(x.numerator)
    return f"{x.numerator}/{x.denominator}"


def sci(x, digits=4):
    """Decimal display of an exact non-negative rational."""
    if x == 0:
        return "0"
    return f"{float(x):.{digits}e}".replace("e-0", "e-").replace("e+0", "e+")


def tex_sci(x, digits=4):
    s = sci(x, digits)
    if "e" not in s:
        return s
    m, e = s.split("e")
    if int(e) == 0:
        return m
    return f"${m}\\cdot 10^{{{int(e)}}}$"


# ---------------------------------------------------------------------------
# Families of measures.  Each family maps n to a weight function on worlds;
# the measure is the normalized weight.
# ---------------------------------------------------------------------------

def fam_weights(code, n):
    if code == "U":
        return lambda w: F(1)
    if code == "G2":
        return lambda w: F(2) ** popcount(w)
    if code == "G32":
        return lambda w: F(3, 2) ** popcount(w)
    if code == "G3":
        return lambda w: F(3) ** popcount(w)
    if code == "L":
        return lambda w: F(popcount(w) + 1)
    if code == "T":
        return lambda w: F(2) if 2 * popcount(w) >= n else F(1)
    if code == "P":
        def wt(w):
            r = F(1)
            for i in range(n):
                if (w >> i) & 1:
                    r *= F(i + 2, i + 1)     # lambda_i = (i+1)/i for object a_i
            return r
        return wt
    if code == "S1":
        return lambda w: F(1) if w & 1 else F(0)
    if code == "H":
        return lambda w: F(1, 2) ** popcount(w)
    raise ValueError(code)


FAMS = [
    ("U", "uniform"),
    ("G2", "weight $2^{|w|}$"),
    ("G32", "weight $(3/2)^{|w|}$"),
    ("G3", "weight $3^{|w|}$"),
    ("L", "weight $|w|+1$"),
    ("T", "threshold"),
    ("P", "product"),
    ("S1", "up-set of $a_1$"),
    ("H", "weight $2^{-|w|}$"),
]


def measure(code, n):
    wt = fam_weights(code, n)
    ws = [wt(w) for w in range(1 << n)]
    z = sum(ws)
    return [x / z for x in ws], z


def addition_profile(mu, n):
    """Number of edges and the maximal ratio mu(w)/mu(w+a) over edges
    (0 if mu(w) = 0 throughout).  Addition holds iff the ratio is <= 1."""
    cnt, worst = 0, F(0)
    for w, v in edges(n):
        cnt += 1
        if mu[w] == 0:
            continue
        if mu[v] == 0:
            worst = None  # infinite violation
            continue
        if worst is not None:
            worst = max(worst, mu[w] / mu[v])
    return cnt, worst


def tolerance_bound(eps, n):
    return ((1 + eps) / (2 + eps)) ** n


# ---------------------------------------------------------------------------
# Volume A
# ---------------------------------------------------------------------------

def vol_a():
    rows = []
    stats = {"rows": 0, "add": 0, "tol": 0, "edges": 0}
    for n in range(1, NMAX_A + 1):
        for code, _ in FAMS:
            mu, z = measure(code, n)
            cnt, worst = addition_profile(mu, n)
            stats["edges"] += cnt
            me = mu[0]
            minimal = all(me <= x for x in mu)
            bound = F(1, 2 ** n)
            if worst is not None and worst <= 1:
                adm = "yes"
                ok = me <= bound and minimal
                verdict = "bound holds" if ok else "FAILS"
                stats["add"] += 1
                assert ok
            else:
                # the family is eps-admissible with 1+eps = worst
                eps = worst - 1
                tb = tolerance_bound(eps, n)
                adm = f"no ($1{{+}}\\varepsilon={fr(worst)}$)"
                ok = me <= tb
                verdict = "tol.\\ bound holds" if ok else "FAILS"
                stats["tol"] += 1
                assert ok and me == tb   # the tilted measure attains the bound
                verdict = "tol.\\ bound attained"
            stats["rows"] += 1
            rid = f"A{n:02d}.{code}"
            rows.append(
                f"{rid} & {n} & {code} & {fr(z)} & {cnt} & {adm} & {fr(me)} & "
                f"{float(me * 2 ** n):.6f} & {'yes' if minimal else 'no'} & {verdict} \\\\")
    head = (r"\begin{longtable}{@{}llllrlllll@{}}" "\n"
            r"\toprule" "\n"
            r"Id & $n$ & Fam. & $Z$ & Edges & Addition & $\mu(e)$ & $2^n\mu(e)$ & $e$ min. & Verdict \\" "\n"
            r"\midrule\endhead" "\n"
            r"\bottomrule\endfoot" "\n")
    body = "\n".join(rows)
    open(os.path.join(HERE, "tab_a.tex"), "w").write(
        "{\\scriptsize\\setlength{\\tabcolsep}{3pt}\n" + head + body + "\n\\end{longtable}}\n")
    return stats


# ---------------------------------------------------------------------------
# Up-sets of the Boolean lattice
# ---------------------------------------------------------------------------

def upsets(n):
    """All up-sets of W_n as bitmasks over the 2^n worlds (bit w set iff w in U).
    Recursion: an up-set of W_n is a pair (U0, U1) of up-sets of W_{n-1} with
    U0 contained in U1, where U0 collects the worlds without a_n and U1 those
    with a_n."""
    if n == 0:
        return [0, 1]
    prev = upsets(n - 1)
    half = 1 << (n - 1)
    out = []
    for u0 in prev:
        for u1 in prev:
            if u0 & ~u1 == 0:
                out.append(u0 | (u1 << half))
    return out


def members(mask, n):
    return [w for w in range(1 << n) if (mask >> w) & 1]


def is_upset(mask, n):
    for w, v in edges(n):
        if (mask >> w) & 1 and not (mask >> v) & 1:
            return False
    return True


def minimal_elements(ms, n):
    s = set(ms)
    mins = []
    for w in ms:
        if not any((w >> i) & 1 and (w & ~(1 << i)) in s for i in range(n)):
            mins.append(w)
    return mins


def setstr(w, n):
    objs = [str(i + 1) for i in range(n) if (w >> i) & 1]
    return "\\{" + ",".join(objs) + "\\}"


DEDEKIND = {0: 2, 1: 3, 2: 6, 3: 20, 4: 168, 5: 7581}


def vol_c():
    """Exhaustive list of non-empty up-sets for n <= 4, summary for n = 5."""
    rows = []
    stats = {}
    sup_tab = {}
    for n in range(1, NMAX_UP + 1):
        ups = upsets(n)
        assert len(ups) == DEDEKIND[n]
        assert all(is_upset(u, n) for u in ups)
        full = (1 << n) - 1
        nonempty = [u for u in ups if u]
        count_e_pos = 0
        sup = [F(0)] * (1 << n)
        inf = [F(1)] * (1 << n)
        by_size = {}
        idx = 0
        for u in sorted(nonempty, key=lambda m: (bin(m).count("1"), m)):
            ms = members(u, n)
            size = len(ms)
            mu_e = F(1, size) if 0 in ms else F(0)
            mu_f = F(1, size)  # the full world belongs to every non-empty up-set
            assert full in ms
            # mechanical checks: Addition for the uniform measure on U
            mu = [F(1, size) if (u >> w) & 1 else F(0) for w in range(1 << n)]
            cnt, worst = addition_profile(mu, n)
            assert worst is not None and worst <= 1
            assert mu_e <= F(1, 2 ** n)
            if mu_e > 0:
                count_e_pos += 1
            for w in range(1 << n):
                sup[w] = max(sup[w], mu[w])
                inf[w] = min(inf[w], mu[w])
            by_size[size] = by_size.get(size, 0) + 1
            idx += 1
            if n <= 4:
                mins = minimal_elements(ms, n)
                gens = " ".join(setstr(m, n) for m in mins)
                rows.append(f"C{n}.{idx:03d} & {n} & {gens} & {size} & {fr(mu_e)} & {fr(mu_f)} & "
                            f"{cnt} & yes & {'yes' if mu_e <= F(1, 2 ** n) else 'NO'} \\\\")
        sup_tab[n] = (sup, inf)
        stats[n] = {"total": len(ups), "nonempty": len(nonempty), "e_pos": count_e_pos,
                    "by_size": by_size}
    head = (r"\begin{longtable}{@{}llp{6.2cm}rllrll@{}}" "\n"
            r"\toprule" "\n"
            r"Id & $n$ & Minimal elements of $U$ & $|U|$ & $\mu_U(e)$ & $\mu_U(f)$ & Edges & Add. & $\mu_U(e)\le 2^{-n}$ \\" "\n"
            r"\midrule\endhead" "\n"
            r"\bottomrule\endfoot" "\n")
    open(os.path.join(HERE, "tab_c.tex"), "w").write(
        "{\\scriptsize\\setlength{\\tabcolsep}{3pt}\n" + head + "\n".join(rows) + "\n\\end{longtable}}\n")
    # summary for n = 5 by size of the up-set
    st5 = stats[5]["by_size"]
    srows = []
    sizes = sorted(st5)
    half = (len(sizes) + 1) // 2
    for k in range(half):
        a = sizes[k]
        left = f"{a} & {st5[a]} & {fr(F(1, a))}"
        if k + half < len(sizes):
            b = sizes[k + half]
            right = f"{b} & {st5[b]} & {fr(F(1, b))}"
        else:
            right = "& &"
        srows.append(left + " & " + right + " \\\\")
    open(os.path.join(HERE, "tab_c5.tex"), "w").write(
        "{\\small\n\\begin{tabular}{@{}rrl@{\\qquad}rrl@{}}\n\\toprule\n"
        "$|U|$ & Up-sets & $\\mu_U(f)$ & $|U|$ & Up-sets & $\\mu_U(f)$ \\\\\n\\midrule\n"
        + "\n".join(srows) + "\n\\bottomrule\n\\end{tabular}}\n")
    return stats, sup_tab


# ---------------------------------------------------------------------------
# Volume B: the worlds of W_n, n <= 5
# ---------------------------------------------------------------------------

def vol_b(sup_tab):
    rows = []
    checks = 0
    for n in range(1, NMAX_UP + 1):
        mus = {c: measure(c, n)[0] for c in ("U", "G2", "L", "P")}
        sup, inf = sup_tab[n]
        full = (1 << n) - 1
        for w in sorted(range(1 << n), key=lambda x: (popcount(x), x)):
            k = popcount(w)
            formula = F(2) ** (k - n) if k >= n else F(1, 2 ** (n - k))
            inf_formula = F(1, 2 ** n) if w == full else F(0)
            ok = sup[w] == formula and inf[w] == inf_formula
            assert ok
            # every admissible family respects 0 <= mu(w) <= sup
            for c in mus:
                assert inf[w] <= mus[c][w] <= sup[w]
            checks += 1
            nb = sum(1 for i in range(n) if popcount(w ^ (1 << i)) > 0)
            rows.append(
                f"B{n}.{wstr(w, n)} & {wstr(w, n)} & {k} & {fr(mus['U'][w])} & {fr(mus['G2'][w])} & "
                f"{fr(mus['L'][w])} & {fr(mus['P'][w])} & {fr(inf[w])} & {fr(sup[w])} & {nb} & "
                f"{'yes' if ok else 'NO'} \\\\")
        rows.append(r"\midrule")
    rows.pop()
    head = (r"\begin{longtable}{@{}lllllllllll@{}}" "\n"
            r"\toprule" "\n"
            r"Id & $w$ & $|w|$ & $\mu_{U}$ & $\mu_{G2}$ & $\mu_{L}$ & $\mu_{P}$ & $\inf_{\mathcal{A}_n}$ & $\sup_{\mathcal{A}_n}$ & n.-e. nbrs & Prop.~3.2 \\" "\n"
            r"\midrule\endhead" "\n"
            r"\bottomrule\endfoot" "\n")
    open(os.path.join(HERE, "tab_b.tex"), "w").write(
        "{\\scriptsize\\setlength{\\tabcolsep}{3pt}\n" + head + "\n".join(rows) + "\n\\end{longtable}}\n")
    return checks


# ---------------------------------------------------------------------------
# Volume D: tolerance bounds
# ---------------------------------------------------------------------------

EPS_D = [F(1, 10), F(1, 4), F(1, 2), F(1), F(2), F(4)]


def vol_d():
    # tightness: the tilted measure mu(w) ~ (1+eps)^(-|w|) is eps-admissible
    # and attains the bound, for n <= 10
    verified = 0
    for eps in EPS_D:
        for n in range(1, 11):
            wt = [(1 + eps) ** (-popcount(w)) for w in range(1 << n)]
            z = sum(wt)
            mu = [x / z for x in wt]
            cnt, worst = addition_profile(mu, n)
            assert worst == 1 + eps
            assert mu[0] == tolerance_bound(eps, n)
            verified += 1
    rows = []
    for n in range(1, 31):
        cells = []
        for eps in EPS_D:
            cells.append(tex_sci(tolerance_bound(eps, n), 3))
        mark = "exact, attained" if n <= 10 else "formula"
        rows.append(f"D{n:02d} & {n} & " + " & ".join(cells) + f" & {tex_sci(F(1, 2 ** n), 3)} & {mark} \\\\")
    head = (r"\begin{longtable}{@{}ll" + "l" * len(EPS_D) + r"ll@{}}" "\n"
            r"\toprule" "\n"
            r"Id & $n$ & " + " & ".join(f"$\\varepsilon={fr(e)}$" for e in EPS_D) +
            r" & $2^{-n}$ & Status \\" "\n"
            r"\midrule\endhead" "\n"
            r"\bottomrule\endfoot" "\n")
    open(os.path.join(HERE, "tab_d.tex"), "w").write(
        "{\\scriptsize\\setlength{\\tabcolsep}{3pt}\n" + head + "\n".join(rows) + "\n\\end{longtable}}\n")
    # thresholds: least n with bound < 1/k
    trows = []
    for eps in EPS_D + [F(0)]:
        cells = []
        for k in (10, 100, 1000, 10 ** 6, 10 ** 9):
            n = 0
            while tolerance_bound(eps, n) >= F(1, k):
                n += 1
            cells.append(str(n))
        label = "$0$ (Addition)" if eps == 0 else f"${fr(eps)}$"
        trows.append(f"{label} & {fr((1 + eps) / (2 + eps))} & " + " & ".join(cells) + " \\\\")
    open(os.path.join(HERE, "tab_d2.tex"), "w").write(
        "{\\small\n\\begin{tabular}{@{}llrrrrr@{}}\n\\toprule\n"
        "$\\varepsilon$ & ratio $\\frac{1+\\varepsilon}{2+\\varepsilon}$ & $k=10$ & $10^2$ & $10^3$ & $10^6$ & $10^9$ \\\\\n\\midrule\n"
        + "\n".join(trows) + "\n\\bottomrule\n\\end{tabular}}\n")
    return verified


# ---------------------------------------------------------------------------
# Volume E: perturbations
# ---------------------------------------------------------------------------

EPS_E = [F(1, 100), F(1, 10), F(1, 2), F(1)]
BASES_E = ["U", "G2", "L", "T", "P"]


def vol_e():
    rng = random.Random(20261006)
    rows = []
    stats = {"rows": 0, "still_add": 0, "adv_eq": 0, "max_ratio": F(0)}
    for n in range(2, NMAX_E + 1):
        for code in BASES_E:
            mu, _ = measure(code, n)
            for eps in EPS_E:
                for kind in ("adv", "rnd"):
                    if kind == "adv":
                        f = [1 + eps] + [1 / (1 + eps)] * ((1 << n) - 1)
                    else:
                        # factors 1 + eps*j/8 with j in -4..8: all lie in [1/(1+eps), 1+eps] for eps <= 1
                        f = [1 + eps * F(rng.randint(-4, 8), 8) for _ in range(1 << n)]
                    assert all(1 / (1 + eps) <= x <= 1 + eps for x in f)
                    raw = [mu[w] * f[w] for w in range(1 << n)]
                    z = sum(raw)
                    nu = [x / z for x in raw]
                    cnt, worst = addition_profile(nu, n)
                    tol = (1 + eps) ** 2
                    bound = tol * F(1, 2 ** n)
                    assert worst <= tol
                    ok = nu[0] <= bound
                    assert ok
                    tb = tolerance_bound(tol - 1, n)
                    assert nu[0] <= tb
                    still = worst <= 1
                    stats["rows"] += 1
                    stats["still_add"] += still
                    key = (code, kind)
                    stats.setdefault("by", {}).setdefault(key, [0, 0])
                    stats["by"][key][0] += 1
                    stats["by"][key][1] += still
                    stats["max_ratio"] = max(stats["max_ratio"], nu[0] / bound)
                    rid = f"E{n:02d}.{code}.{'abcd'[EPS_E.index(eps)]}{kind[0]}"
                    rows.append(
                        f"{rid} & {n} & {code} & {fr(eps)} & {kind} & {tex_sci(nu[0])} & {tex_sci(bound)} & "
                        f"{float(nu[0] / bound):.4f} & {float(worst):.4f} & {'yes' if still else 'no'} & "
                        f"{tex_sci(tb)} & {'yes' if ok else 'NO'} \\\\")
    head = (r"\begin{longtable}{@{}lllllllllll l@{}}" "\n"
            r"\toprule" "\n"
            r"Id & $n$ & Base & $\varepsilon$ & Kind & $\nu(e)$ & $(1{+}\varepsilon)^2 2^{-n}$ & Ratio & Max.\ $\frac{\nu(w)}{\nu(w+a)}$ & Add. & Tol.\ bound & Holds \\" "\n"
            r"\midrule\endhead" "\n"
            r"\bottomrule\endfoot" "\n")
    open(os.path.join(HERE, "tab_e.tex"), "w").write(
        "{\\scriptsize\\setlength{\\tabcolsep}{2.5pt}\n" + head + "\n".join(rows) + "\n\\end{longtable}}\n")
    print(sorted(stats["by"].items()))
    return stats


# ---------------------------------------------------------------------------
# Volume F: neighborhood isolation
# ---------------------------------------------------------------------------

def vol_f():
    rows = []
    for n in range(1, 17):
        iso = 0
        min_ne = None
        for w in range(1 << n):
            status = popcount(w) > 0
            same = sum(1 for i in range(n) if (popcount(w ^ (1 << i)) > 0) == status)
            if same == 0:
                iso += 1
            if status:
                ne = sum(1 for i in range(n) if popcount(w ^ (1 << i)) > 0)
                min_ne = ne if min_ne is None else min(min_ne, ne)
        e_nb = n
        if n >= 2:
            assert iso == 1 and min_ne == n - 1
        rows.append(f"F{n:02d} & {n} & {1 << n} & {iso} & {e_nb} & {min_ne} & "
                    f"{fr(1 - F(1, 2 ** n))} \\\\")
    open(os.path.join(HERE, "tab_f.tex"), "w").write(
        "{\\small\n\\begin{longtable}{@{}lrrrrrl@{}}\n\\toprule\n"
        "Id & $n$ & $|W_n|$ & Isolated & Nbrs of $e$ & Min.\\ n.-e.\\ nbrs & $\\inf_{\\mathcal{A}_n}\\mu(S_n)$ \\\\\n"
        "\\midrule\\endhead\n\\bottomrule\\endfoot\n"
        + "\n".join(rows) + "\n\\end{longtable}}\n")


# ---------------------------------------------------------------------------
# Volume G: down-sets (sets of worlds closed under subtraction)
# ---------------------------------------------------------------------------

def independent(mask, n):
    """True iff no two members of the set are neighbors."""
    for w, v in edges(n):
        if (mask >> w) & 1 and (mask >> v) & 1:
            return False
    return True


def vol_g():
    from math import comb
    rows = []
    for n in range(1, NMAX_UP + 1):
        ups = upsets(n)
        N = 1 << n
        allw = (1 << N) - 1
        cnt = [u.bit_count() for u in ups]
        pairs = viol = attained = iso = 0
        downs = [allw ^ u for u in ups]          # complements of up-sets
        for d in downs:
            cd = d.bit_count()
            best_num, best_den = 0, 1
            for u, cu in zip(ups, cnt):
                if not u:
                    continue
                pairs += 1
                m = (u & d).bit_count()
                if m * N > cu * cd:               # Kleitman: |U n D| 2^n <= |U||D|
                    viol += 1
                if m * best_den > best_num * cu:
                    best_num, best_den = m, cu
            if best_num * N == cd * best_den:
                attained += 1
            if d and independent(d, n):
                iso += 1
                assert d == 1                      # only the set {e}
        assert viol == 0 and attained == len(downs)
        rows.append(f"GD{n} & {n} & {len(downs)} & {pairs} & {viol} & {attained} & {iso} \\\\")
    open(os.path.join(HERE, "tab_g1.tex"), "w").write(
        "{\\small\n\\begin{tabular}{@{}lrrrrrr@{}}\n\\toprule\n"
        "Id & $n$ & Down-sets & Pairs $(U, D)$ & Violations & $\\sup = |D|/2^n$ & Isolated, non-empty \\\\\n\\midrule\n"
        + "\n".join(rows) + "\n\\bottomrule\n\\end{tabular}}\n")
    rows = []
    for n in range(1, 31):
        cells = []
        for k in range(0, 7):
            if k > n:
                cells.append("--")
            else:
                cells.append(tex_sci(F(sum(comb(n, j) for j in range(k + 1)), 2 ** n), 3))
        rows.append(f"GK{n:02d} & {n} & " + " & ".join(cells) +
                    f" & {'exhaustive' if n <= NMAX_UP else 'formula'} \\\\")
    open(os.path.join(HERE, "tab_g2.tex"), "w").write(
        "{\\scriptsize\\setlength{\\tabcolsep}{3pt}\n\\begin{longtable}{@{}ll" + "l" * 7 + "l@{}}\n\\toprule\n"
        "Id & $n$ & " + " & ".join(f"$k={k}$" for k in range(7)) + " & Status \\\\\n"
        "\\midrule\\endhead\n\\bottomrule\\endfoot\n" + "\n".join(rows) + "\n\\end{longtable}}\n")


def main():
    sa = vol_a()
    sc, sup_tab = vol_c()
    nb = vol_b(sup_tab)
    nd = vol_d()
    se = vol_e()
    vol_f()
    vol_g()
    lines = [
        f"% Volume A: {sa['rows']} rows, {sa['add']} admissible, {sa['tol']} tolerance-only, {sa['edges']} edge checks",
        f"% Volume B: {nb} worlds checked against Prop. 3.2",
        "% Volume C: " + ", ".join(f"n={n}: {s['total']} up-sets, {s['nonempty']} non-empty, {s['e_pos']} with mu(e)>0"
                                     for n, s in sc.items()),
        f"% Volume D: {nd} tightness checks",
        f"% Volume E: {se['rows']} rows, {se['still_add']} still satisfy Addition, max nu(e)/bound = {float(se['max_ratio']):.6f}",
    ]
    open(os.path.join(HERE, "summary.tex"), "w").write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
