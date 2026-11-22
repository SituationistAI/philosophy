#!/usr/bin/env python3
"""Generator for the computed part of POL-01-c,
"Justice as Entitlement and Its Equivalence Under Lump-Sum Transfers".

Standard library only.  Each economy has I agents, two goods and Cobb-Douglas
utilities u_i(x) = x_1^{a_i} x_2^{1-a_i} with rational a_i and rational
endowments.  Prices of equilibria from given holdings are computed exactly
(fractions.Fraction); quantities that involve fractional powers are computed in
decimal arithmetic with 60 significant digits (decimal module).  The price of
the allocation selected by the modified difference principle is the root of a
monotone equation, found by bisection to 60 digits.  Output: tab_*.tex here.
"""
import os
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from itertools import product

getcontext().prec = 60
HERE = os.path.dirname(os.path.abspath(__file__))
TOL = D("1e-45")            # tolerance for equalities checked in 60-digit arithmetic

# (id, a_i list, endowments list of (good 1, good 2))
ECONOMIES = [
    ("E01", ["1/2", "1/2"], [(4, 4), (4, 4)]),
    ("E02", ["1/2", "1/2"], [(9, 3), (1, 1)]),
    ("E03", ["1/3", "2/3"], [(6, 1), (1, 6)]),
    ("E04", ["1/2", "1/2"], [(8, 8), (0, 0)]),
    ("E05", ["1/4", "3/4"], [(0, 10), (5, 0)]),
    ("E06", ["2/3", "1/2"], [(3, 7), (2, 2)]),
    ("E07", ["3/4", "1/4"], [(10, 1), (1, 1)]),
    ("E08", ["1/5", "4/5"], [(2, 2), (6, 6)]),
    ("E09", ["1/2", "1/2", "1/2"], [(6, 6), (2, 2), (1, 1)]),
    ("E10", ["1/3", "1/2", "2/3"], [(5, 1), (1, 5), (1, 1)]),
    ("E11", ["1/2", "1/2", "1/2"], [(10, 0), (0, 10), (0, 0)]),
    ("E12", ["1/4", "1/2", "3/4"], [(0, 8), (4, 4), (8, 0)]),
    ("E13", ["2/3", "2/3", "1/3"], [(6, 2), (3, 3), (0, 1)]),
    ("E14", ["1/2", "1/3", "1/4"], [(12, 12), (1, 0), (0, 1)]),
    ("E15", ["3/5", "2/5", "1/2"], [(4, 9), (7, 2), (1, 1)]),
    ("E16", ["1/2", "3/4", "1/4"], [(3, 3), (3, 3), (3, 3)]),
    ("E17", ["1/2", "1/2", "1/2", "1/2"], [(8, 8), (4, 4), (2, 2), (1, 1)]),
    ("E18", ["1/4", "1/3", "2/3", "3/4"], [(6, 1), (1, 6), (3, 3), (0, 2)]),
    ("E19", ["1/2", "1/2", "1/3", "2/3"], [(20, 0), (0, 20), (1, 1), (0, 0)]),
    ("E20", ["1/5", "2/5", "3/5", "4/5"], [(1, 4), (2, 3), (3, 2), (4, 1)]),
    ("E21", ["1/2", "2/3", "1/3", "1/2"], [(5, 5), (5, 0), (0, 5), (1, 0)]),
    ("E22", ["3/4", "3/4", "1/4", "1/4"], [(10, 2), (0, 1), (2, 10), (1, 0)]),
    ("E23", ["1/3", "1/2", "2/3", "1/2"], [(2, 2), (2, 2), (2, 2), (2, 2)]),
    ("E24", ["1/2", "1/4", "3/4", "1/2"], [(16, 0), (0, 16), (4, 4), (0, 1)]),
    ("E25", ["1/2", "1/3"], [(1, 0), (0, 1)]),
    ("E26", ["9/10", "1/10"], [(5, 5), (5, 5)]),
    ("E27", ["1/2", "1/2", "1/2"], [(30, 30), (1, 1), (1, 1)]),
    ("E28", ["1/10", "1/2", "9/10"], [(4, 4), (0, 8), (8, 0)]),
    ("E29", ["1/3", "1/3", "2/3"], [(0, 9), (9, 0), (1, 1)]),
    ("E30", ["1/2", "1/2", "1/2", "1/2"], [(10, 0), (0, 10), (0, 0), (0, 0)]),
    ("E31", ["1/6", "1/3", "1/2", "2/3"], [(3, 3), (0, 6), (6, 0), (1, 1)]),
    ("E32", ["1/2", "1/2", "1/2", "1/2", "1/2"], [(16, 16), (8, 8), (4, 4), (2, 2), (1, 1)]),
    ("E33", ["1/6", "1/3", "1/2", "2/3", "5/6"], [(5, 1), (4, 2), (3, 3), (2, 4), (1, 5)]),
    ("E34", ["1/2", "1/4", "3/4", "1/2", "1/2"], [(20, 0), (0, 20), (2, 2), (0, 0), (1, 0)]),
    ("E35", ["1/3", "2/3", "1/3", "2/3", "1/2"], [(2, 2), (2, 2), (2, 2), (2, 2), (2, 2)]),
    ("E36", ["3/4", "1/4", "1/2", "1/2", "1/2"], [(12, 0), (0, 12), (0, 1), (1, 0), (0, 0)]),
]

MENU_K = {2: 48, 3: 24, 4: 12, 5: 8}     # lattice for the self-ownership menus
GRID_G = {2: 400, 3: 40, 4: 16, 5: 10}    # lattice of wealth shares for the frontier check


def dec(x):
    if isinstance(x, F):
        return D(x.numerator) / D(x.denominator)
    return D(x)


def util(a, x1, x2):
    a = dec(a)
    x1, x2 = dec(x1), dec(x2)
    if x1 == 0 or x2 == 0:
        if a == 0:
            return x2
        if a == 1:
            return x1
        return D(0)
    return (x1 ** a) * (x2 ** (1 - a))


def fmt(x, sig=6):
    """Decimal display with `sig` significant digits."""
    x = dec(x)
    if abs(x) < D("1e-15"):
        return "0"
    s = f"{x:.{sig}g}"
    if "e" in s or "E" in s:
        m, e = s.lower().split("e")
        return f"${m}\\cdot 10^{{{int(e)}}}$"
    return s


def ffr(x):
    x = F(x)
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def tiny(x):
    """Display of a residual."""
    x = abs(dec(x))
    if x == 0:
        return "0"
    e = x.adjusted()
    return f"$<10^{{{e + 1}}}$"


def eq_price(a, w):
    """Exact equilibrium price of good 1 (good 2 is numeraire) from holdings w."""
    num = sum(ai * wi[1] for ai, wi in zip(a, w))
    den = sum((1 - ai) * wi[0] for ai, wi in zip(a, w))
    return num / den


def demand(ai, p, m):
    return (ai * m / p, (1 - ai) * m)


def equilibrium(a, w):
    p = eq_price(a, w)
    ms = [p * wi[0] + wi[1] for wi in w]
    xs = [demand(ai, p, mi) for ai, mi in zip(a, ms)]
    us = [util(ai, *xi) for ai, xi in zip(a, xs)]
    return p, ms, xs, us


def cconst(a):
    a = dec(a)
    return (a ** a) * ((1 - a) ** (1 - a))


def mdp_solution(a, E):
    """Equal-utility efficient allocation: price p, incomes m_i (Decimal)."""
    E1, E2 = dec(E[0]), dec(E[1])
    ad = [dec(x) for x in a]
    cs = [cconst(x) for x in a]

    def shares(p):
        raw = [(p ** ai) / ci for ai, ci in zip(ad, cs)]
        z = sum(raw)
        return [r / z for r in raw]

    def h(p):
        s = shares(p)
        A = sum(ai * si for ai, si in zip(ad, s))
        return (E2 / E1) * A / (1 - A) - p

    lo, hi = D("1e-12"), D("1e12")
    assert h(lo) > 0 and h(hi) < 0
    for _ in range(400):
        mid = (lo * hi).sqrt()
        if h(mid) > 0:
            lo = mid
        else:
            hi = mid
        if hi / lo - 1 < D("1e-58"):
            break
    p = (lo * hi).sqrt()
    s = shares(p)
    M = p * E1 + E2
    ms = [si * M for si in s]
    return p, ms


def post_transfer_holdings(e, p, ms):
    """Numeraire transfers tau_i = m_i - p.e_i, realized in goods: payers give
    good 2 first, then good 1; the pool is divided among receivers in
    proportion to what they receive."""
    tau = [mi - (p * dec(ei[0]) + dec(ei[1])) for ei, mi in zip(e, ms)]
    pool1 = pool2 = D(0)
    hold = []
    for ei, ti in zip(e, tau):
        w1, w2 = dec(ei[0]), dec(ei[1])
        if ti < 0:
            pay = -ti
            g2 = min(pay, w2)
            g1 = (pay - g2) / p
            w1, w2 = w1 - g1, w2 - g2
            pool1 += g1
            pool2 += g2
        hold.append([w1, w2])
    gains = sum(t for t in tau if t > 0)
    for i, ti in enumerate(tau):
        if ti > 0:
            hold[i][0] += pool1 * ti / gains
            hold[i][1] += pool2 * ti / gains
    return tau, hold


def envy_pairs(a, xs):
    n = len(a)
    cnt = 0
    for i in range(n):
        ui = util(a[i], *xs[i])
        for j in range(n):
            if i != j and util(a[i], *xs[j]) > ui + TOL:
                cnt += 1
    return cnt


def compositions(K, n):
    if n == 1:
        yield (K,)
        return
    for j in range(K + 1):
        for rest in compositions(K - j, n - 1):
            yield (j,) + rest


def lex_better(x, y):
    """Modified difference principle on (min, total) with tolerance TOL."""
    if x[0] > y[0] + TOL:
        return True
    if abs(x[0] - y[0]) <= TOL and x[1] > y[1] + TOL:
        return True
    return False


def self_ownership_optimum(a, e, E):
    """Largest worst-off level reachable when only good 1 is redistributed and
    each agent keeps her good-2 endowment.  For a price p, the holdings of good 1
    that support p as the equilibrium price form the polytope
      sum_i w_i = E1,  sum_i (1-a_i) w_i = B(p) = sum_i a_i e_i2 / p,  w >= 0,
    and level t is reachable at p iff the minimal holdings r_i(p,t) =
    max(0, (t p^{a_i}/c_i - e_i2)/p) fit into this polytope; the extra good 1
    can be placed on any agent, which gives a closed-form test.  Outer search
    over log p (grid, then golden section), inner bisection on t."""
    ad = [dec(x) for x in a]
    om = [1 - x for x in ad]
    e2 = [dec(x[1]) for x in e]
    E1 = dec(E[0])
    cs = [cconst(x) for x in a]
    S = sum(ai * ei for ai, ei in zip(ad, e2))
    lo_p, hi_p = S / (E1 * max(om)), S / (E1 * min(om))

    def feasible(p, t, pa):
        r = []
        for ai, ci, ei, pai in zip(ad, cs, e2, pa):
            need = (t * pai / ci - ei) / p
            r.append(need if need > 0 else D(0))
        rest = E1 - sum(r)
        if rest < 0:
            return None
        B = S / p
        base = sum(o * ri for o, ri in zip(om, r))
        if not (base + rest * min(om) - D("1e-30") <= B <= base + rest * max(om) + D("1e-30")):
            return None
        # place the rest on two agents (cheapest and dearest in (1-a)) to hit B
        w = list(r)
        i_lo = min(range(len(om)), key=lambda i: om[i])
        i_hi = max(range(len(om)), key=lambda i: om[i])
        if om[i_hi] == om[i_lo]:
            w[i_lo] += rest
        else:
            lam = (B - base - rest * om[i_lo]) / (rest * (om[i_hi] - om[i_lo])) if rest > 0 else D(0)
            lam = min(max(lam, D(0)), D(1))
            w[i_hi] += lam * rest
            w[i_lo] += (1 - lam) * rest
        return w

    def best_t(p):
        pa = [p ** ai for ai in ad]
        lo, hi = D(0), D(10) ** 6
        for _ in range(110):
            mid = (lo + hi) / 2
            if feasible(p, mid, pa) is not None:
                lo = mid
            else:
                hi = mid
        return lo, feasible(p, lo, pa)

    ln_lo, ln_hi = lo_p.ln(), hi_p.ln()
    N = 240
    grid = [(ln_lo + (ln_hi - ln_lo) * D(k) / D(N)) for k in range(N + 1)]
    vals = [best_t(x.exp())[0] for x in grid]
    k = max(range(N + 1), key=lambda i: vals[i])
    a_, b_ = grid[max(k - 1, 0)], grid[min(k + 1, N)]
    g = (D(5).sqrt() - 1) / 2
    for _ in range(90):
        c_, d_ = b_ - g * (b_ - a_), a_ + g * (b_ - a_)
        if best_t(c_.exp())[0] >= best_t(d_.exp())[0]:
            b_ = d_
        else:
            a_ = c_
    x = (a_ + b_) / 2
    cand = [(best_t(x.exp())[0], x), (vals[k], grid[k])]
    t, x = max(cand)
    p = x.exp()
    t, w = best_t(p)
    # certificate: the holdings w (good 1) with the good-2 endowments form an
    # equilibrium whose worst-off level is computed directly
    hold = [(wi, ei) for wi, ei in zip(w, e2)]
    pp = sum(ai * h[1] for ai, h in zip(ad, hold)) / sum(o * h[0] for o, h in zip(om, hold))
    us = [util(ai, *demand(ai, pp, pp * h[0] + h[1])) for ai, h in zip(ad, hold)]
    return min(us), sum(us), w, us, pp


def solve(eid, a_s, e_s):
    a = [F(x) for x in a_s]
    e = [(F(x), F(y)) for x, y in e_s]
    n = len(a)
    E = (sum(x for x, _ in e), sum(y for _, y in e))
    out = {"id": eid, "n": n, "a": a, "e": e, "E": E}

    # (i) equilibrium without transfers
    p0, m0, x0, u0 = equilibrium(a, e)
    out.update(p0=p0, x0=x0, u0=u0)
    out["ce0"] = (min(u0), sum(u0))

    # (ii) allocation selected by the modified difference principle
    ps, ms = mdp_solution(a, E)
    xs = [demand(dec(ai), ps, mi) for ai, mi in zip(a, ms)]
    us = [util(ai, *xi) for ai, xi in zip(a, xs)]
    tau, hold = post_transfer_holdings(e, ps, ms)
    out.update(ps=ps, xs=xs, us=us, tau=tau, hold=hold)
    out["mdp"] = (min(us), sum(us))

    # checks
    chk = {}
    chk["budget"] = abs(sum(tau))
    chk["holdings_nonneg"] = all(h[0] >= -TOL and h[1] >= -TOL for h in hold)
    chk["holdings_sum"] = max(abs(sum(h[0] for h in hold) - dec(E[0])), abs(sum(h[1] for h in hold) - dec(E[1])))
    chk["income"] = max(abs(ps * h[0] + h[1] - mi) for h, mi in zip(hold, ms))
    chk["clear"] = max(abs(sum(x[0] for x in xs) - dec(E[0])), abs(sum(x[1] for x in xs) - dec(E[1])))
    chk["mrs"] = max(abs(dec(ai) * x[1] / ((1 - dec(ai)) * x[0]) - ps) for ai, x in zip(a, xs))
    chk["equal"] = max(us) - min(us)
    # local optimality on the budget line: moving along it lowers utility
    worst_local = D(0)
    for ai, x in zip(a, xs):
        for h in (D("1e-6"), D("-1e-6")):
            y = (x[0] + h, x[1] - ps * h)
            worst_local = max(worst_local, util(ai, *y) - util(ai, *x))
    chk["local"] = worst_local
    # frontier check: no equilibrium after lump-sum transfers on a lattice of
    # wealth shares gives every agent more than the selected level
    G = GRID_G[n]
    best_grid = D(0)
    pts = 0
    for comp in compositions(G, n):
        s = [F(c, G) for c in comp]
        A = sum(ai * si for ai, si in zip(a, s))
        if A == 1:
            continue
        p = (E[1] / E[0]) * A / (1 - A)
        M = p * E[0] + E[1]
        uu = [util(ai, *demand(ai, p, si * M)) for ai, si in zip(a, s)]
        best_grid = max(best_grid, min(uu))
        pts += 1
    chk["grid_pts"] = pts
    chk["grid_best"] = best_grid
    chk["grid_ok"] = best_grid <= min(us) + TOL
    ok = (chk["budget"] < TOL and chk["holdings_nonneg"] and chk["holdings_sum"] < TOL
          and chk["income"] < TOL and chk["clear"] < TOL and chk["mrs"] < TOL
          and chk["equal"] < TOL and chk["local"] <= 0 and chk["grid_ok"])
    chk["ok"] = ok
    assert ok, (eid, chk)
    out["chk"] = chk
    out["envy_mdp"] = envy_pairs(a, xs)

    # (iii) equal-division equilibrium
    ed = [(E[0] / n, E[1] / n)] * n
    ped, _, xed, ued = equilibrium(a, ed)
    out.update(ped=ped, ued=ued)
    out["ed"] = (min(ued), sum(ued))
    out["envy_ed"] = envy_pairs(a, xed)

    # (iv) self-ownership menu: only good 1 is redistributed
    K = MENU_K[n]
    best = None
    best_tot = None
    options = []
    for comp in compositions(K, n):
        w = [(E[0] * F(c, K), ei[1]) for c, ei in zip(comp, e)]
        if sum((1 - ai) * wi[0] for ai, wi in zip(a, w)) == 0:
            continue
        p, _, xx, uu = equilibrium(a, w)
        key = (min(uu), sum(uu))
        options.append((comp, key))
        if best is None or lex_better(key, best[1]):
            best = (comp, key, p)
        if best_tot is None or key[1] > best_tot[1][1] + TOL:
            best_tot = (comp, key)
    maxmin = best[1][0]
    ties = [o for o in options if abs(o[1][0] - maxmin) <= TOL]
    # every MDP choice is undominated in the menu (POL-01-a, Theorem 5.4)
    assert not any(lex_better(o[1], best[1]) for o in options)
    out["menu"] = {"K": K, "size": len(options), "best": best, "ties": len(ties),
                   "ties_total_distinct": len({round(float(o[1][1]), 30) for o in ties}),
                   "tot": best_tot}

    so = self_ownership_optimum(a, e, E)
    assert so[0] <= min(us) + TOL and so[0] >= best[1][0] - D("1e-20"), (eid, so[0], best[1][0])
    out["so"] = so

    # (v) exchange forbidden: value-neutral rearrangement of the CE0 allocation
    out["wilt"] = None
    if n >= 3:
        order = sorted(range(n), key=lambda i: u0[i])
        w_, j, k = order[0], order[-1], order[-2]
        if u0[k] > u0[w_] + TOL:
            delta = min(x0[k][0], x0[j][1] / p0) / 2
            for _ in range(80):
                xb = [list(x) for x in x0]
                xb[j] = [x0[j][0] + delta, x0[j][1] - p0 * delta]
                xb[k] = [x0[k][0] - delta, x0[k][1] + p0 * delta]
                ub = [util(ai, *xi) for ai, xi in zip(a, xb)]
                if min(ub) == u0[w_] and ub[j] > u0[w_] and ub[k] > u0[w_]:
                    break
                delta /= 2
            else:
                raise RuntimeError(eid)
            # trading from xb at the equilibrium price returns to x0
            pb = eq_price(a, [tuple(x) for x in xb])
            assert pb == p0
            out["wilt"] = {"w": w_, "j": j, "k": k, "delta": delta, "ub": ub,
                           "min_b": min(ub), "tot_b": sum(ub)}
    return out


# ---------------------------------------------------------------------------
# Output
# ---------------------------------------------------------------------------

def bundle(x):
    return f"({fmt(x[0])}, {fmt(x[1])})"


def write_block(r):
    n = r["n"]
    L = []
    L.append(f"\\subsection*{{Economy {r['id']}}}")
    L.append(f"\\label{{ec:{r['id']}}}")
    L.append("{\\scriptsize\\setlength{\\tabcolsep}{3pt}")
    L.append("\\begin{tabular}{@{}llllllll@{}}")
    L.append("\\toprule")
    L.append("$i$ & $a_i$ & $e_i$ & $x^0_i$ & $u^0_i$ & $\\tau_i$ & $\\omega_i$ & $x^*_i$ \\\\")
    L.append("\\midrule")
    for i in range(n):
        ei = r["e"][i]
        L.append(f"{i + 1} & {ffr(r['a'][i])} & ({ffr(ei[0])}, {ffr(ei[1])}) & {bundle(r['x0'][i])} & "
                 f"{fmt(r['u0'][i])} & {fmt(r['tau'][i])} & {bundle(r['hold'][i])} & {bundle(r['xs'][i])} \\\\")
    L.append("\\bottomrule\\end{tabular}}")
    L.append("")
    c = r["chk"]
    m = r["menu"]
    comp = m["best"][0]
    shares = ", ".join(str(x) for x in comp)
    tcomp = ", ".join(str(x) for x in m["tot"][0])
    lines = [
        f"Prices: $p^0 = {ffr(r['p0'])}$ (exact); $p^* = {fmt(r['ps'], 12)}$; equal division $p = {ffr(r['ped'])}$.",
        f"Without transfers: worst-off {fmt(r['ce0'][0])}, total {fmt(r['ce0'][1])}. "
        f"Equal division: worst-off {fmt(r['ed'][0])}, total {fmt(r['ed'][1])}, envy pairs {r['envy_ed']}. "
        f"Modified difference principle: worst-off {fmt(r['mdp'][0], 10)}, total {fmt(r['mdp'][1], 10)}, envy pairs {r['envy_mdp']}.",
        f"Checks: $|\\sum_i\\tau_i|$ {tiny(c['budget'])}; holdings non-negative, summing to $E$ ({tiny(c['holdings_sum'])}); "
        f"$p^*\\cdot\\omega_i = m_i$ ({tiny(c['income'])}); market clearing {tiny(c['clear'])}; "
        f"$\\max_i|\\mathrm{{MRS}}_i - p^*|$ {tiny(c['mrs'])}; utility spread {tiny(c['equal'])}; "
        f"budget-line optimality yes; frontier lattice {c['grid_pts']} points, best worst-off {fmt(c['grid_best'], 10)} $\\leq$ {fmt(r['mdp'][0], 10)}. "
        f"Verdict: {'efficient equilibrium after transfers, MDP-selected' if c['ok'] else 'FAILS'}.",
        f"Self-ownership menu ({m['size']} options, good~1 shares in multiples of $1/{m['K']}$): "
        f"MDP choice $({shares})/{m['K']}$, worst-off {fmt(m['best'][1][0])}, total {fmt(m['best'][1][1])}; "
        f"options tied on the worst-off level: {m['ties']}; total-maximizing option $({tcomp})/{m['K']}$ with worst-off {fmt(m['tot'][1][0])}, total {fmt(m['tot'][1][1])}.",
    ]
    so = r["so"]
    above = [i + 1 for i in range(n) if so[3][i] > so[0] + D("1e-12")]
    lines.append(
        f"Self-ownership optimum (continuous): good~1 holdings ({', '.join(fmt(x, 5) for x in so[2])}), "
        f"price {fmt(so[4], 8)}, utilities ({', '.join(fmt(x, 6) for x in so[3])}); worst-off {fmt(so[0], 10)}, total {fmt(so[1], 8)}"
        + (f"; agents above the worst-off level: {', '.join(map(str, above))}." if above else "; all levels equal."))
    if r["wilt"]:
        w = r["wilt"]
        lines.append(
            f"Exchange forbidden: rearranging the bundles of agents {w['j'] + 1} and {w['k'] + 1} at $p^0$ "
            f"($\\delta = {fmt(w['delta'], 4)}$) leaves the worst-off (agent {w['w'] + 1}) at {fmt(w['min_b'])} and lowers the total "
            f"from {fmt(r['ce0'][1])} to {fmt(w['tot_b'])}; trade from it returns to $x^0$ at $p^0$.")
    L.append("\\begin{itemize}[leftmargin=1.2em,itemsep=0pt,topsep=2pt]\\footnotesize")
    for x in lines:
        L.append("\\item " + x)
    L.append("\\end{itemize}")
    return "\n".join(L)


def main():
    results = [solve(*ec) for ec in ECONOMIES]
    blocks = [write_block(r) for r in results]
    open(os.path.join(HERE, "tab_economies.tex"), "w").write("\n\n".join(blocks) + "\n")
    rows = []
    for r in results:
        m = r["menu"]
        gap = r["mdp"][0] - r["so"][0]
        rows.append(
            f"{r['id']} & {r['n']} & {fmt(r['ce0'][0], 5)} & {fmt(r['ce0'][1], 5)} & {fmt(r['ed'][0], 5)} & "
            f"{fmt(r['ed'][1], 5)} & {fmt(r['mdp'][0], 5)} & {fmt(r['mdp'][1], 5)} & "
            f"{fmt(r['so'][0], 5)} & {fmt(gap, 3) if gap > D('1e-12') else '0'} & {r['envy_mdp']} & "
            f"{'yes' if r['chk']['ok'] else 'NO'} \\\\")
    open(os.path.join(HERE, "tab_summary.tex"), "w").write(
        "{\\scriptsize\\setlength{\\tabcolsep}{3pt}\n\\begin{longtable}{@{}llllllllllll@{}}\n\\toprule\n"
        "Id & $I$ & \\multicolumn{2}{l}{No transfers} & \\multicolumn{2}{l}{Equal division} & "
        "\\multicolumn{2}{l}{MDP} & Self-own. & Gap & Envy & Checks \\\\\n"
        " & & min & total & min & total & min & total & min & & & \\\\\n"
        "\\midrule\\endhead\n\\bottomrule\\endfoot\n" + "\n".join(rows) + "\n\\end{longtable}}\n")
    # statistics for the preface
    st = []
    st.append(f"% economies: {len(results)}")
    st.append(f"% all checks ok: {all(r['chk']['ok'] for r in results)}")
    st.append(f"% CE0 already MDP (no transfers needed): {[r['id'] for r in results if max(abs(t) for t in r['tau']) < TOL]}")
    st.append(f"% MDP total below CE0 total: {[r['id'] for r in results if r['mdp'][1] < r['ce0'][1] - TOL]}")
    st.append(f"% MDP total above CE0 total: {[r['id'] for r in results if r['mdp'][1] > r['ce0'][1] + TOL]}")
    st.append(f"% envy in MDP allocation: {[(r['id'], r['envy_mdp']) for r in results if r['envy_mdp']]}")
    st.append(f"% envy in ED: {[(r['id'], r['envy_ed']) for r in results if r['envy_ed']]}")
    st.append(f"% ED min below MDP min: {sum(1 for r in results if r['ed'][0] < r['mdp'][0] - TOL)}")
    st.append(f"% self-ownership gap > 0: {[(r['id'], float(r['mdp'][0] - r['so'][0])) for r in results if r['mdp'][0] - r['so'][0] > D('1e-12')]}")
    st.append(f"% self-ownership unequal: {[r['id'] for r in results if max(r['so'][3]) - r['so'][0] > D('1e-12')]}")
    st.append(f"% menu ties >1: {[(r['id'], r['menu']['ties']) for r in results if r['menu']['ties'] > 1]}")
    st.append(f"% menu sizes: {[(r['id'], r['menu']['size']) for r in results]}")
    st.append(f"% wilt cases: {[r['id'] for r in results if r['wilt']]}")
    st.append(f"% menu total-max differs from MDP choice: {[r['id'] for r in results if r['menu']['tot'][0] != r['menu']['best'][0]]}")
    st.append(f"% grid points total: {sum(r['chk']['grid_pts'] for r in results)}")
    st.append(f"% menu options total: {sum(r['menu']['size'] for r in results)}")
    open(os.path.join(HERE, "summary.tex"), "w").write("\n".join(st) + "\n")
    print("\n".join(st))


if __name__ == "__main__":
    main()
