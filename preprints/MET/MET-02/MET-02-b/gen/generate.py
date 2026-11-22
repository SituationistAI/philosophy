#!/usr/bin/env python3
"""Generator for the computed volumes of MET-02-b.

Python 3, standard library only. Writes tab_*.tex and summary.tex in this
directory. All arithmetic on charges, exponents and anomaly coefficients is
exact (fractions.Fraction). Every check is an assert: the script halts if any
check fails. Output is deterministic.
"""
import os
from fractions import Fraction as F
from itertools import combinations_with_replacement as cwr
from math import gcd
from functools import reduce

HERE = os.path.dirname(os.path.abspath(__file__))
SUMMARY = {}
CHECKS = {"n": 0}


def check(cond, msg):
    assert cond, msg
    CHECKS["n"] += 1


def fr(x):
    x = F(x)
    if x.denominator == 1:
        return str(x.numerator)
    s = "-" if x < 0 else ""
    return "%s%d/%d" % (s, abs(x.numerator), x.denominator)


def frm(x):
    """Fraction in math mode with a true minus sign."""
    x = F(x)
    if x.denominator == 1:
        return "$%d$" % x.numerator
    s = "-" if x < 0 else ""
    return "$%s%d/%d$" % (s, abs(x.numerator), x.denominator)


def write(name, text):
    with open(os.path.join(HERE, name), "w", encoding="utf-8") as fh:
        fh.write(text)


def longtable(spec, header, rows, size="scriptsize", sep="3pt"):
    ncol = len(header)
    out = ["{\\%s\\setlength{\\tabcolsep}{%s}" % (size, sep),
           "\\begin{longtable}{%s}" % spec.replace("p{", ">{\\raggedright\\arraybackslash}p{"), "\\toprule",
           " & ".join(header) + " \\\\", "\\midrule\\endfirsthead",
           "\\toprule", " & ".join(header) + " \\\\", "\\midrule\\endhead",
           "\\midrule\\multicolumn{%d}{r}{\\emph{continued}}\\\\\\endfoot" % ncol,
           "\\bottomrule\\endlastfoot"]
    for r in rows:
        assert len(r) == ncol, (r, header)
        out.append(" & ".join(r) + " \\\\")
    out.append("\\end{longtable}}")
    return "\n".join(out) + "\n"


# ---------------------------------------------------------------------------
# Volume A. The Standard Model: multiplets, states, kinds.
# Convention: Q = T3 + Y/2 (so the left-handed quark doublet has Y = 1/3).
# ---------------------------------------------------------------------------

REP3 = {"1": 0, "3": 1, "3b": -1, "8": 0}          # triality
REPTEX = {"1": "$\\mathbf{1}$", "3": "$\\mathbf{3}$", "3b": "$\\bar{\\mathbf{3}}$", "8": "$\\mathbf{8}$"}
REPDIM = {"1": 1, "3": 3, "3b": 3, "8": 8}

GEN_NAMES = {
    1: {"u": "u", "d": "d", "n": "\\nu_e", "e": "e"},
    2: {"u": "c", "d": "s", "n": "\\nu_\\mu", "e": "\\mu"},
    3: {"u": "t", "d": "b", "n": "\\nu_\\tau", "e": "\\tau"},
}

# Chiral fermion multiplets in the physical-chirality basis:
# key, label, colour, SU(2) dim, Y, chirality, B, L, status
FERMION_MULTIPLETS = [
    ("QL", "Q_L", "3", 2, F(1, 3), "L", F(1, 3), 0, "established"),
    ("uR", "u_R", "3", 1, F(4, 3), "R", F(1, 3), 0, "established"),
    ("dR", "d_R", "3", 1, F(-2, 3), "R", F(1, 3), 0, "established"),
    ("LL", "L_L", "1", 2, F(-1), "L", 0, 1, "established"),
    ("eR", "e_R", "1", 1, F(-2), "R", 0, 1, "established"),
    ("nR", "\\nu_R", "1", 1, F(0), "R", 0, 1, "hypothetical"),
]
# components: multiplet key -> list of (flavour slot, T3)
COMPONENTS = {
    "QL": [("u", F(1, 2)), ("d", F(-1, 2))],
    "uR": [("u", F(0))], "dR": [("d", F(0))],
    "LL": [("n", F(1, 2)), ("e", F(-1, 2))],
    "eR": [("e", F(0))], "nR": [("n", F(0))],
}
# Independently entered electric charges of the flavour slots (in units of e)
DECLARED_Q = {"u": F(2, 3), "d": F(-1, 3), "n": F(0), "e": F(-1)}

BOSON_MULTIPLETS = [
    # key, label, colour, SU(2) dim, Y, spin, status
    ("G", "G", "8", 1, F(0), 1, "established"),
    ("W", "W", "1", 3, F(0), 1, "established"),
    ("B", "B", "1", 1, F(0), 1, "established"),
    ("H", "H", "1", 2, F(1), 0, "established"),
]


def vol_a():
    rows_m = []
    idx = 0
    weyl_per_gen = 0
    weyl_per_gen_nr = 0
    for key, lab, col, d2, Y, ch, B, L, st in FERMION_MULTIPLETS:
        idx += 1
        ncomp = REPDIM[col] * d2
        if key != "nR":
            weyl_per_gen += ncomp
        weyl_per_gen_nr += ncomp
        T = F(d2 - 1, 2)
        rows_m.append(["A.%02d" % idx, "$%s$" % lab, "1/2", ch, REPTEX[col], fr(T), frm(Y),
                       fr(B), fr(L), "1--3", str(ncomp), st])
    for key, lab, col, d2, Y, s, st in BOSON_MULTIPLETS:
        idx += 1
        T = F(d2 - 1, 2)
        rows_m.append(["A.%02d" % idx, "$%s$" % lab, str(s), "--", REPTEX[col], fr(T), frm(Y),
                       "0", "0", "--", str(REPDIM[col] * d2 * (1 if s == 1 else 2)),
                       st])
    check(weyl_per_gen == 15, "15 Weyl components per generation")
    check(weyl_per_gen_nr == 16, "16 with right-handed neutrino")
    SUMMARY["weylgen"] = weyl_per_gen
    tab1 = longtable("@{}llllllllllrl@{}",
                     ["Id", "Field", "Spin", "Chir.", "$SU(3)$", "$T$", "$Y$", "$B$", "$L$", "Gen.",
                      "Comp.", "Status"], rows_m)

    # A.2 states, with the check Q = T3 + Y/2 and the Z6 condition
    rows_s = []
    states = []
    sidx = 0
    nq = 0
    for gen in (1, 2, 3):
        for key, lab, col, d2, Y, ch, B, L, st in FERMION_MULTIPLETS:
            for slot, T3 in COMPONENTS[key]:
                for anti in (False, True):
                    sidx += 1
                    name = GEN_NAMES[gen][slot]
                    qd = DECLARED_Q[slot]
                    y, t3, b, l, c = Y, T3, F(B), F(L), col
                    nm = "{%s}_%s" % (name, ch)
                    if anti:
                        qd, y, t3, b, l = -qd, -y, -t3, -b, -l
                        c = {"3": "3b", "3b": "3", "1": "1"}[col]
                        nm = "\\overline{%s}_{%s}" % (name, "R" if ch == "L" else "L")
                    qc = t3 + y / 2
                    check(qc == qd, "Q = T3 + Y/2 for %s" % nm)
                    nq += 1
                    tri = REP3[c]
                    z6 = y / 2 + F(tri, 3) + F(d2 - 1, 2)
                    check(z6.denominator == 1, "Z6 condition for %s" % nm)
                    check(((qd - F(2 * tri, 3)) % 1) == 0, "charge-triality for %s" % nm)
                    states.append(dict(name=nm, gen=gen, Q=qd, Y=y, T3=t3, col=c, B=b, L=l, st=st,
                                       spin=F(1, 2), key=key, anti=anti, d2=d2))
                    rows_s.append(["A.2.%03d" % sidx, "$%s$" % nm, str(gen), "$%s$" % lab + ("$^{c}$" if anti else ""),
                                   REPTEX[c], frm(t3), frm(y), frm(qd), "ok", fr(z6), fr(b), fr(l),
                                   "hyp." if st == "hypothetical" else "est."])
    bos_states = [
        ("g", "G", "8", F(0), F(0), F(0), 1),
        ("W^+", "W", "1", F(1), F(0), F(1), 1), ("W^-", "W", "1", F(-1), F(0), F(-1), 1),
        ("W^3", "W", "1", F(0), F(0), F(0), 1), ("B", "B", "1", F(0), F(0), F(0), 1),
        ("H^+", "H", "1", F(1, 2), F(1), F(1), 0), ("H^0", "H", "1", F(-1, 2), F(1), F(0), 0),
        ("H^-", "H", "1", F(-1, 2), F(-1), F(-1), 0), ("\\overline{H^0}", "H", "1", F(1, 2), F(-1), F(0), 0),
    ]
    d2map = {"G": 1, "W": 3, "B": 1, "H": 2}
    for nm, mult, c, t3, y, qd, s in bos_states:
        sidx += 1
        qc = t3 + y / 2
        check(qc == qd, "Q = T3 + Y/2 for %s" % nm)
        nq += 1
        z6 = y / 2 + F(REP3[c], 3) + F(d2map[mult] - 1, 2)
        check(z6.denominator == 1, "Z6 condition boson")
        rows_s.append(["A.2.%03d" % sidx, "$%s$" % nm, "--", "$%s$" % mult, REPTEX[c], frm(t3), frm(y), frm(qd),
                       "ok", fr(z6), "0", "0", "est."])
    SUMMARY["nQcheck"] = nq
    tab2 = longtable("@{}llllllllllll l@{}".replace(" ", ""),
                     ["Id", "State", "Gen.", "Mult.", "$SU(3)$", "$T_3$", "$Y$", "$Q$", "$Q{=}T_3{+}Y/2$",
                      "$Z_6$", "$B$", "$L$", "St."], rows_s)

    # A.3 kinds: Dirac (or Weyl) particles as conjunctions of determinates
    kinds = []
    for gen in (1, 2, 3):
        for slot in ("u", "d", "n", "e"):
            name = GEN_NAMES[gen][slot]
            if slot in ("u", "d"):
                col, TL, YL, YR, B, L = "3", F(1, 2), F(1, 3), (F(4, 3) if slot == "u" else F(-2, 3)), F(1, 3), F(0)
            elif slot == "e":
                col, TL, YL, YR, B, L = "1", F(1, 2), F(-1), F(-2), F(0), F(1)
            else:
                col, TL, YL, YR, B, L = "1", F(1, 2), F(-1), None, F(0), F(1)
            Q = DECLARED_Q[slot]
            kinds.append(dict(name=name, gen=gen, Q=Q, spin="1/2", col=col, TL=TL, YL=YL, YR=YR, B=B, L=L,
                              mass="$m_{%s}$" % name))
            kinds.append(dict(name="\\bar{%s}" % name, gen=gen, Q=-Q, spin="1/2",
                              col={"3": "3b", "1": "1"}[col], TL=TL, YL=-YL, YR=(None if YR is None else -YR),
                              B=-B, L=-L, mass="$m_{%s}$" % name))
    for nm, Q, s, col, TL, YL in [("\\gamma", 0, "1", "1", None, F(0)), ("g", 0, "1", "8", None, F(0)),
                                  ("W^+", 1, "1", "1", F(1), F(0)), ("W^-", -1, "1", "1", F(1), F(0)),
                                  ("Z", 0, "1", "1", None, F(0)), ("h", 0, "0", "1", None, F(0))]:
        kinds.append(dict(name=nm, gen=0, Q=F(Q), spin=s, col=col, TL=TL, YL=YL, YR=None, B=F(0), L=F(0),
                          mass=("$m_{%s}$" % nm.replace("^", "").replace("\\", "").replace("+", "").replace("-", "")
                                if nm not in ("\\gamma", "g") else "$0$")))
    # indiscernibility classes under the gauge, Lorentz and charge determinates (no mass, no generation)
    def sig(k):
        return (k["Q"], k["spin"], k["col"], k["TL"], k["YL"], k["YR"], k["B"], k["L"])
    classes = {}
    for k in kinds:
        classes.setdefault(sig(k), []).append(k)
    cls_id = {}
    for i, (s, mem) in enumerate(sorted(classes.items(), key=lambda kv: [str(x) for x in kv[0]])):
        for k in mem:
            cls_id[id(k)] = (i + 1, len(mem))
    ferm_classes = [m for m in classes.values() if m[0]["gen"] > 0]
    check(all(len(m) == 3 for m in ferm_classes), "each fermion class has exactly three members")
    check(all(sorted(k["gen"] for k in m) == [1, 2, 3] for m in ferm_classes), "one per generation")
    SUMMARY["nkinds"] = len(kinds)
    SUMMARY["nfermclasses"] = len(ferm_classes)
    rows_k = []
    for i, k in enumerate(kinds):
        cid, csz = cls_id[id(k)]
        yr = "--" if k["YR"] is None else frm(k["YR"])
        tl = "--" if k["TL"] is None else fr(k["TL"])
        cons = "$s{=}%s \\wedge Q{=}%s \\wedge %s \\wedge (T,Y)_{\\mathrm{dbl}}{=}(%s,%s)$" % (
            k["spin"], fr(k["Q"]), REPTEX[k["col"]].strip("$"), tl, fr(k["YL"]))
        if k["YR"] is not None:
            cons += " $\\wedge\\ Y_{\\mathrm{sgl}}{=}%s$" % fr(k["YR"])
        cons += " $\\wedge$ " + k["mass"]
        rows_k.append(["A.3.%02d" % (i + 1), "$%s$" % k["name"], str(k["gen"]) if k["gen"] else "--",
                       frm(k["Q"]), k["spin"], REPTEX[k["col"]], frm(k["B"]), frm(k["L"]),
                       "%d (%d)" % (cid, csz), cons])
    tab3 = longtable("@{}lllllllllp{7.4cm}@{}",
                     ["Id", "Kind", "Gen.", "$Q$", "$s$", "Col.", "$B$", "$L$", "Class", "Construction (conjunction of determinates)"],
                     rows_k)
    write("tab_a1.tex", tab1)
    write("tab_a2.tex", tab2)
    write("tab_a3.tex", tab3)
    return states, kinds


# ---------------------------------------------------------------------------
# Volume B. Anomalies and the exhaustive hypercharge searches.
# Left-handed Weyl basis: Q, u^c, d^c, L, e^c (and n^c).
# ---------------------------------------------------------------------------

LH = [  # name, colour, SU(2) dim, Y, B, L
    ("Q", "3", 2, F(1, 3), F(1, 3), F(0)),
    ("u^c", "3b", 1, F(-4, 3), F(-1, 3), F(0)),
    ("d^c", "3b", 1, F(2, 3), F(-1, 3), F(0)),
    ("L", "1", 2, F(-1), F(0), F(1)),
    ("e^c", "1", 1, F(2), F(0), F(-1)),
    ("\\nu^c", "1", 1, F(0), F(0), F(-1)),
]


def anomaly_coeffs(f, charge):
    """Contributions of one left-handed multiplet to the anomaly coefficients.
    charge: function returning the U(1) charge used (Y, B, L or B-L)."""
    name, col, d2, Y, B, L = f
    q = charge(f)
    dc = REPDIM[col]
    t3 = F(1, 2) if col in ("3", "3b") else F(0)       # Dynkin index of 3, 3b
    t2 = F(1, 2) if d2 == 2 else F(0)
    return {
        "SU3^3": REP3[col] * d2,
        "SU3^2 X": t3 * d2 * q,
        "SU2^2 X": t2 * dc * q,
        "X Y^2": dc * d2 * q * Y * Y,
        "X^3": dc * d2 * q ** 3,
        "grav X": dc * d2 * q,
        "doublets": dc if d2 == 2 else 0,
    }


def coef(x, sym):
    if x == 1:
        return sym
    if x == -1:
        return "-" + sym
    return fr(x) + "\\," + sym


def lincomb(a, b, swap):
    ysym = "Y'" if swap else "Y"
    if a == 0 and b == 0:
        return "trivial"
    parts = []
    if a != 0:
        parts.append(coef(a, ysym))
    if b != 0:
        t = coef(b, "(B{-}L)")
        if parts and not t.startswith("-"):
            t = "+" + t
        parts.append(t)
    return "$" + "".join(parts) + "$"


def vol_b():
    keys = ["SU3^3", "SU3^2 X", "SU2^2 X", "X^3", "grav X", "doublets"]
    ktex = {"SU3^3": "$SU(3)^3$", "SU3^2 X": "$SU(3)^2\\,Y$", "SU2^2 X": "$SU(2)^2\\,Y$", "X^3": "$Y^3$",
            "grav X": "grav.$\\,Y$", "doublets": "doublets"}
    rows = []
    tot = {k: F(0) for k in keys}
    for i, f in enumerate(LH):
        c = anomaly_coeffs(f, lambda g: g[3])
        rows.append(["B.1.%d" % (i + 1), "$%s$" % f[0], "(%s, %d, %s)" % (REPTEX[f[1]], f[2], frm(f[3]))] +
                    [frm(c[k]) for k in keys])
        if i < 5:
            for k in keys:
                tot[k] += c[k]
    rows.append(["B.1.7", "sum, one generation", "without $\\nu^c$"] + [frm(tot[k]) for k in keys])
    for k in keys[:-1]:
        check(tot[k] == 0, "gauge anomaly %s cancels" % k)
    check(tot["doublets"] % 2 == 0, "even number of doublets (Witten)")
    tot3 = {k: 3 * tot[k] for k in keys}
    rows.append(["B.1.8", "sum, three generations", "without $\\nu^c$"] + [frm(tot3[k]) for k in keys])
    c6 = anomaly_coeffs(LH[5], lambda g: g[3])
    tot6 = {k: tot[k] + c6[k] for k in keys}
    rows.append(["B.1.9", "sum, one generation", "with $\\nu^c$"] + [frm(tot6[k]) for k in keys])
    tab1 = longtable("@{}lllllllll@{}", ["Id", "Multiplet", "$(SU(3),\\dim, Y)$"] + [ktex[k] for k in keys], rows)

    # B.2 global charges B, L, B-L: mixed anomalies with the gauge groups and gravity
    glob = [("B", lambda g: g[4]), ("L", lambda g: g[5]), ("B-L", lambda g: g[4] - g[5]),
            ("B+L", lambda g: g[4] + g[5])]
    rows2 = []
    res = {}
    j = 0
    for withn in (False, True):
        fl = LH if withn else LH[:5]
        for nm, ch in glob:
            j += 1
            t = {"SU3^2 X": F(0), "SU2^2 X": F(0), "X Y^2": F(0), "grav X": F(0), "X^3": F(0)}
            for f in fl:
                c = anomaly_coeffs(f, ch)
                for k in t:
                    t[k] += c[k]
            res[(nm, withn)] = t
            rows2.append(["B.2.%d" % j, "$%s$" % nm, "yes" if withn else "no", frm(t["SU3^2 X"]),
                          frm(t["SU2^2 X"]), frm(t["X Y^2"]), frm(t["grav X"]), frm(t["X^3"])])
    check(res[("B-L", False)]["SU2^2 X"] == 0 and res[("B-L", False)]["X Y^2"] == 0, "B-L electroweak anomaly-free")
    check(res[("B+L", False)]["SU2^2 X"] != 0, "B+L anomalous")
    check(res[("B", False)]["SU3^2 X"] == 0, "B has no QCD anomaly")
    check(all(v == 0 for v in res[("B-L", True)].values()), "B-L fully anomaly-free with nu^c")
    check(res[("B-L", False)]["grav X"] != 0, "B-L gravitationally anomalous without nu^c")
    tab2 = longtable("@{}llllllll@{}", ["Id", "Charge $X$", "$\\nu^c$", "$SU(3)^2X$", "$SU(2)^2X$", "$XY^2$",
                                         "grav.$\\,X$", "$X^3$"], rows2)

    # B.3 exhaustive search: 5 fields, Y in {k/6 : |k| <= 12}
    grid = [F(k, 6) for k in range(-12, 13)]
    sols = []
    for yQ in grid:
        for yL in grid:
            if 3 * yQ + yL != 0:
                continue
            for yu in grid:
                for yd in grid:
                    if 2 * yQ + yu + yd != 0:
                        continue
                    for ye in grid:
                        if 6 * yQ + 3 * yu + 3 * yd + 2 * yL + ye != 0:
                            continue
                        if 6 * yQ ** 3 + 3 * yu ** 3 + 3 * yd ** 3 + 2 * yL ** 3 + ye ** 3 != 0:
                            continue
                        sols.append((yQ, yu, yd, yL, ye))
    # classify
    def classify5(s):
        yQ, yu, yd, yL, ye = s
        if all(x == 0 for x in s):
            return "trivial"
        if yQ == 0:
            check(yL == 0 and ye == 0 and yu == -yd, "degenerate family")
            return "$y_Q=0$: vector-like on $u^c,d^c$"
        r = yQ / F(1, 3)
        if (yu, yd, yL, ye) == (r * F(-4, 3), r * F(2, 3), -r, 2 * r):
            return "SM, scale $%s$" % fr(r)
        if (yu, yd, yL, ye) == (r * F(2, 3), r * F(-4, 3), -r, 2 * r):
            return "SM with $u^c\\leftrightarrow d^c$, scale $%s$" % fr(r)
        return "other"
    rows3 = []
    for i, s in enumerate(sols):
        c = classify5(s)
        check(c != "other", "every solution is SM-proportional or degenerate")
        rows3.append(["B.3.%02d" % (i + 1)] + [frm(x) for x in s] + [c])
    SUMMARY["b3n"] = len(sols)
    SUMMARY["b3space"] = len(grid) ** 5
    SUMMARY["b3sm"] = sum(1 for s in sols if s[0] != 0)
    tab3 = longtable("@{}llllllp{6.5cm}@{}", ["Id", "$y_Q$", "$y_{u^c}$", "$y_{d^c}$", "$y_L$", "$y_{e^c}$",
                                              "Classification"], rows3)

    # B.4 exhaustive search: 6 fields with nu^c, Y in {k/3 : |k| <= 6}
    grid6 = [F(k, 3) for k in range(-6, 7)]
    sols6 = []
    for yQ in grid6:
        for yL in grid6:
            if 3 * yQ + yL != 0:
                continue
            for yu in grid6:
                for yd in grid6:
                    if 2 * yQ + yu + yd != 0:
                        continue
                    for ye in grid6:
                        for yn in grid6:
                            if 6 * yQ + 3 * yu + 3 * yd + 2 * yL + ye + yn != 0:
                                continue
                            if 6 * yQ ** 3 + 3 * yu ** 3 + 3 * yd ** 3 + 2 * yL ** 3 + ye ** 3 + yn ** 3 != 0:
                                continue
                            sols6.append((yQ, yu, yd, yL, ye, yn))
    # decompose each solution as a*Y + b*(B-L) where possible (with u/d possibly exchanged)
    Yv = (F(1, 3), F(-4, 3), F(2, 3), F(-1), F(2), F(0))
    Yv_sw = (F(1, 3), F(2, 3), F(-4, 3), F(-1), F(2), F(0))
    BLv = (F(1, 3), F(-1, 3), F(-1, 3), F(-1), F(1), F(1))

    def decomp(s):
        out = []
        for lab, base in (("", Yv), ("swap", Yv_sw)):
            # solve s = a*base + b*BL using components u^c and e^c, then verify all
            # from Q: a/3 + b/3 = yQ ; from nu^c: b = yn
            b = s[5]
            a = 3 * s[0] - b
            if all(a * base[i] + b * BLv[i] == s[i] for i in range(6)):
                out.append((lab, a, b))
        return out
    rows4 = []
    nlin = 0
    for i, s in enumerate(sols6):
        d = decomp(s)
        if d:
            lab, a, b = d[0]
            desc = lincomb(a, b, lab == "swap")
            nlin += 1
        else:
            check(s[0] == 0, "non-linear solutions have y_Q = 0")
            desc = "$y_Q=0$ family"
        rows4.append(["B.4.%03d" % (i + 1)] + [frm(x) for x in s] + [desc])
    SUMMARY["b4n"] = len(sols6)
    SUMMARY["b4space"] = len(grid6) ** 6
    SUMMARY["b4lin"] = nlin
    tab4 = longtable("@{}lllllllp{5.6cm}@{}", ["Id", "$y_Q$", "$y_{u^c}$", "$y_{d^c}$", "$y_L$", "$y_{e^c}$",
                                               "$y_{\\nu^c}$", "Decomposition"], rows4)
    write("tab_b1.tex", tab1)
    write("tab_b2.tex", tab2)
    write("tab_b3.tex", tab3)
    write("tab_b4.tex", tab4)


# ---------------------------------------------------------------------------
# Volume C. Gauge- and Lorentz-invariant field contents without derivatives.
# ---------------------------------------------------------------------------

DMAX_C = 12


def vol_c():
    base = [("Q", 1, 1, F(1, 3), F(1, 3), 0, "L"), ("u^c", -1, 0, F(-4, 3), F(-1, 3), 0, "L"),
            ("d^c", -1, 0, F(2, 3), F(-1, 3), 0, "L"), ("L", 0, 1, F(-1), 0, 1, "L"),
            ("e^c", 0, 0, F(2), 0, -1, "L"), ("H", 0, 1, F(1), 0, 0, "S")]
    fields = []
    for i, (n, c, dd, Y, B, Lp, ch) in enumerate(base):
        fields.append((n, c, dd, Y, F(B), F(Lp), ch, 2 * i))
        fields.append((n + "^\\dagger" if "^" not in n else n.replace("^c", "^{c\\dagger}"),
                       -c, dd, -Y, -F(B), -F(Lp), {"L": "R", "S": "S"}[ch], 2 * i + 1))
    ferm = [f for f in fields if f[6] != "S"]
    sc = [f for f in fields if f[6] == "S"]
    found = []
    tested = 0
    for nf in range(0, 2 * DMAX_C // 3 + 1):
        if F(3, 2) * nf > DMAX_C:
            break
        for fc in cwr(ferm, nf):
            for ns in range(0, DMAX_C + 1):
                if F(3, 2) * nf + ns > DMAX_C:
                    break
                for scc in cwr(sc, ns):
                    m = fc + scc
                    if not m:
                        continue
                    tested += 1
                    if sum(f[3] for f in m) != 0:
                        continue
                    if sum(f[1] for f in m) % 3:
                        continue
                    if sum(f[2] for f in m) % 2:
                        continue
                    if sum(1 for f in m if f[6] == "L") % 2 or sum(1 for f in m if f[6] == "R") % 2:
                        continue
                    found.append(m)
    # reduce modulo hermitian conjugation
    def code(m):
        return tuple(sorted(f[7] for f in m))

    def conj(m):
        return tuple(sorted(c ^ 1 for c in code(m)))
    seen = set()
    reps = []
    for m in found:
        c = code(m)
        if c in seen:
            continue
        cc = conj(m)
        seen.add(c)
        seen.add(cc)
        rep = min(c, cc)
        byc = {f[7]: f for f in fields}
        reps.append(([byc[x] for x in rep], c == cc))
    reps.sort(key=lambda r: (F(3, 2) * sum(1 for f in r[0] if f[6] != "S") + sum(1 for f in r[0] if f[6] == "S"),
                             [f[7] for f in r[0]]))
    rows = []
    stats = {}
    kob = 0
    for i, (m, sc_) in enumerate(reps):
        nf = sum(1 for f in m if f[6] != "S")
        d = F(3, 2) * nf + (len(m) - nf)
        check(d.denominator == 1, "integer dimension")
        B = sum(f[4] for f in m)
        L = sum(f[5] for f in m)
        if B < 0 or (B == 0 and L < 0):
            B, L = -B, -L        # report |Delta B| with sign convention of the conjugate pair
        check(((B - L) / 2 - d) % 2 == 0, "(dB - dL)/2 = d mod 2")
        kob += 1
        if d <= 4:
            check(B == 0 and L == 0, "B and L conserved at d <= 4")
        if d == 5:
            check(B == 0 and abs(L) == 2, "d=5 violates L by two units")
        if d == 6:
            check(B - L == 0, "d=6 conserves B-L")
        # display content with powers
        cnt = {}
        order = []
        for f in m:
            if f[0] not in cnt:
                order.append(f[0])
            cnt[f[0]] = cnt.get(f[0], 0) + 1
        disp = "\\,".join(("%s" % n) if cnt[n] == 1 else ("(%s)^{%d}" % (n, cnt[n]) if "^" in n else "%s^{%d}" % (n, cnt[n]))
                          for n in order)
        key = int(d)
        st = stats.setdefault(key, {"n": 0, "Bv": 0, "Lv": 0, "BLv": 0})
        st["n"] += 1
        st["Bv"] += B != 0
        st["Lv"] += L != 0
        st["BLv"] += (B - L) != 0
        rows.append(["C.%03d" % (i + 1), str(int(d)), "$%s$" % disp, str(nf), str(len(m) - nf), frm(B), frm(L),
                     frm((B - L) / 2), "s.c." if sc_ else "", "ok"])
    SUMMARY["c_tested"] = tested
    SUMMARY["c_found"] = len(found)
    SUMMARY["c_reps"] = len(reps)
    SUMMARY["c_stats"] = stats
    tab = longtable("@{}llp{6.4cm}rrllllr@{}", ["Id", "$d$", "Field content", "$n_\\psi$", "$n_H$", "$\\Delta B$",
                                                "$\\Delta L$", "$\\frac{\\Delta B-\\Delta L}{2}$", "Conj.", "Parity"], rows)
    write("tab_c.tex", tab)
    srows = []
    for d in sorted(stats):
        st = stats[d]
        srows.append([str(d), str(st["n"]), str(st["Bv"]), str(st["Lv"]), str(st["BLv"])])
    write("tab_c0.tex", longtable("@{}rrrrr@{}", ["$d$", "Contents (mod.\\ conj.)", "$\\Delta B\\neq 0$",
                                                    "$\\Delta L \\neq 0$", "$\\Delta(B{-}L)\\neq 0$"], srows,
                                  size="small", sep="6pt"))


# ---------------------------------------------------------------------------
# Volume D. Quark contents of hadrons; generalized Gell-Mann--Nishijima check.
# ---------------------------------------------------------------------------

QUARKS = {  # Q, I3, B, S, C, Bp, T
    "u": (F(2, 3), F(1, 2), F(1, 3), 0, 0, 0, 0), "d": (F(-1, 3), F(-1, 2), F(1, 3), 0, 0, 0, 0),
    "s": (F(-1, 3), F(0), F(1, 3), -1, 0, 0, 0), "c": (F(2, 3), F(0), F(1, 3), 0, 1, 0, 0),
    "b": (F(-1, 3), F(0), F(1, 3), 0, 0, -1, 0), "t": (F(2, 3), F(0), F(1, 3), 0, 0, 0, 1),
}
BARYON_NAMES = {"uud": "$p$", "udd": "$n$", "uuu": "$\\Delta^{++}$", "ddd": "$\\Delta^{-}$",
                "uds": "$\\Lambda^0$, $\\Sigma^0$", "uus": "$\\Sigma^{+}$", "dds": "$\\Sigma^{-}$",
                "uss": "$\\Xi^0$", "dss": "$\\Xi^-$", "sss": "$\\Omega^-$", "udc": "$\\Lambda_c^+$",
                "uuc": "$\\Sigma_c^{++}$", "ddc": "$\\Sigma_c^{0}$", "udb": "$\\Lambda_b^0$"}
MESON_NAMES = {("u", "d"): "$\\pi^+$", ("d", "u"): "$\\pi^-$", ("u", "s"): "$K^+$", ("d", "s"): "$K^0$",
               ("s", "u"): "$K^-$", ("s", "d"): "$\\bar K^0$", ("c", "d"): "$D^+$", ("c", "u"): "$D^0$",
               ("d", "c"): "$D^-$", ("u", "c"): "$\\bar D^0$", ("c", "s"): "$D_s^+$", ("s", "c"): "$D_s^-$",
               ("u", "b"): "$B^+$", ("d", "b"): "$B^0$", ("s", "b"): "$B_s^0$", ("b", "u"): "$B^-$",
               ("b", "d"): "$\\bar B^0$", ("b", "s"): "$\\bar B_s^0$", ("c", "b"): "$B_c^+$", ("b", "c"): "$B_c^-$",
               ("c", "c"): "charmonium", ("b", "b"): "bottomonium",
               ("u", "u"): "neutral mixtures", ("d", "d"): "neutral mixtures", ("s", "s"): "neutral mixtures"}


def qn(content):
    """content: list of (flavour, sign) with sign +1 for quark, -1 for antiquark"""
    tot = [F(0)] * 7
    for fl, sg in content:
        for i, v in enumerate(QUARKS[fl]):
            tot[i] += sg * F(v)
    return tot


def vol_d():
    fl5 = ["u", "d", "s", "c", "b"]
    rows = []
    i = 0
    charges_b = set()
    for combo in cwr(fl5, 3):
        i += 1
        Q, I3, B, S, C, Bp, T = qn([(f, 1) for f in combo])
        Yh = B + S + C + Bp + T
        check(Q == I3 + Yh / 2, "Gell-Mann--Nishijima")
        check(Q.denominator == 1, "integer charge of colour singlet")
        charges_b.add(Q)
        nm = BARYON_NAMES.get("".join(combo), "")
        rows.append(["D.%02d" % i, "$%s$" % "".join(combo), frm(Q), frm(I3), frm(B), str(S), str(C), str(Bp),
                     frm(Yh), "ok", nm])
    nb = i
    charges_m = set()
    for q in fl5:
        for a in fl5:
            i += 1
            Q, I3, B, S, C, Bp, T = qn([(q, 1), (a, -1)])
            Yh = B + S + C + Bp + T
            check(Q == I3 + Yh / 2, "Gell-Mann--Nishijima meson")
            check(Q.denominator == 1, "integer charge meson")
            charges_m.add(Q)
            nm = MESON_NAMES.get((q, a), "")
            rows.append(["D.%02d" % i, "$%s\\bar{%s}$" % (q, a), frm(Q), frm(I3), frm(B), str(S), str(C), str(Bp),
                         frm(Yh), "ok", nm])
    SUMMARY["d_baryons"] = nb
    SUMMARY["d_mesons"] = i - nb
    SUMMARY["d_qb"] = sorted(charges_b)
    SUMMARY["d_qm"] = sorted(charges_m)
    check(sorted(charges_b) == [F(-1), F(0), F(1), F(2)], "baryon charges")
    check(sorted(charges_m) == [F(-1), F(0), F(1)], "meson charges")
    tab = longtable("@{}llllllllllp{3.2cm}@{}", ["Id", "Content", "$Q$", "$I_3$", "$B$", "$S$", "$C$", "$B'$",
                                                 "$Y_h$", "GMN", "Usual name"], rows)
    write("tab_d.tex", tab)
    # D.2: four- and five-constituent contents qq(qbar qbar) and qqqq(qbar)
    rows2 = []
    j = 0
    exq = {}
    nhidden = 0
    for kind, nq, na in (("tetra", 2, 2), ("penta", 4, 1)):
        qs = set()
        for qc in cwr(fl5, nq):
            for ac in cwr(fl5, na):
                j += 1
                Q, I3, B, S, C, Bp, T = qn([(f, 1) for f in qc] + [(f, -1) for f in ac])
                Yh = B + S + C + Bp + T
                check(Q == I3 + Yh / 2, "Gell-Mann--Nishijima exotic")
                check(Q.denominator == 1, "integer charge exotic")
                check((nq - na) % 3 == 0, "colour singlet possible")
                qs.add(Q)
                hid = sorted(set(qc) & set(ac))
                nhidden += bool(hid)
                cont = "$%s\\,%s$" % ("".join(qc), "".join("\\bar{%s}" % f for f in ac))
                rows2.append(["D.2.%03d" % j, cont, frm(Q), frm(I3), frm(B), str(S), str(C), str(Bp), frm(Yh), "ok",
                              ", ".join(hid) if hid else "--"])
        exq[kind] = sorted(qs)
    SUMMARY["d2_n"] = j
    SUMMARY["d2_hidden"] = nhidden
    SUMMARY["d2_q"] = exq
    tab2 = longtable("@{}llllllllllp{2.0cm}@{}", ["Id", "Content", "$Q$", "$I_3$", "$B$", "$S$", "$C$", "$B'$",
                                                 "$Y_h$", "GMN", "Hidden flavour"], rows2)
    write("tab_d2.tex", tab2)


# ---------------------------------------------------------------------------
# Volume E. Spacetime-structural quantities.
# ---------------------------------------------------------------------------

def vol_e():
    rows = []
    for n in range(2, 12):
        metric = n * (n + 1) // 2
        riem = n * n * (n * n - 1) // 12
        ricci = n * (n + 1) // 2 if n >= 3 else 1
        weyl = riem - n * (n + 1) // 2 if n >= 3 else 0
        chris = n * n * (n + 1) // 2
        lor = n * (n - 1) // 2
        poin = n * (n + 1) // 2
        grav = n * (n - 3) // 2 if n >= 3 else 0
        if n == 3:
            check(weyl == 0, "Weyl vanishes in 3 dimensions")
        if n == 4:
            check((riem, weyl, grav, lor, poin) == (20, 10, 2, 6, 10), "four-dimensional counts")
        check(metric - 2 * n == grav or n < 3, "dof = components - 2n")
        rows.append([str(n), str(metric), str(chris), str(riem), str(ricci), str(weyl), str(lor), str(poin), str(grav)])
    tab1 = longtable("@{}rrrrrrrrr@{}", ["$n$", "$g_{ab}$", "$\\Gamma^a_{bc}$", "$R_{abcd}$", "$R_{ab}$",
                                          "$C_{abcd}$", "Lorentz", "Poincar\\'e", "grav.\\ d.o.f."], rows,
                     size="small", sep="5pt")
    # E.2 separations, units with c = 1
    boosts = []
    for (p, q) in [(1, 2), (1, 3), (2, 3), (1, 4), (3, 4), (1, 5), (2, 5), (3, 5), (4, 5), (5, 6), (7, 8), (9, 10)]:
        r = F(p, q)
        g = (1 + r * r) / (1 - r * r)
        gv = 2 * r / (1 - r * r)
        check(g * g - gv * gv == 1, "rational boost")
        boosts.append((g, gv, gv / g))
    rows2 = []
    k = 0
    cls_count = {"timelike": 0, "null": 0, "spacelike": 0}
    nboostchecks = 0
    for dt in range(0, 5):
        for dx in range(0, 5):
            for dy in range(0, dx + 1):
                for dz in range(0, dy + 1):
                    if dt == dx == dy == dz == 0:
                        continue
                    k += 1
                    s2 = dt * dt - dx * dx - dy * dy - dz * dz
                    r2 = dx * dx + dy * dy + dz * dz
                    cls = "timelike" if s2 > 0 else ("null" if s2 == 0 else "spacelike")
                    cls_count[cls] += 1
                    # boost along x: check invariance of s2 under every listed boost, in both directions
                    tvals = []
                    for g, gv, v in boosts:
                        for sgn in (1, -1):
                            t2 = g * dt - sgn * gv * dx
                            x2 = g * dx - sgn * gv * dt
                            check(t2 * t2 - x2 * x2 - dy * dy - dz * dz == s2, "interval invariant")
                            nboostchecks += 1
                            tvals.append(t2)
                    flips = any(t < 0 for t in tvals) if dt > 0 else any(t != 0 for t in tvals)
                    if cls != "spacelike":
                        check(not any(t < 0 for t in tvals) or dt == 0, "time order of causal pairs invariant")
                    vmin2 = "--"
                    if cls == "spacelike":
                        vmin2 = frm(F(dt * dt, r2))
                    order = ("invariant" if cls != "spacelike" else ("frame-relative" if dt > 0 else "simult. in rest fr."))
                    tmin = min(tvals)
                    tmax = max(tvals)
                    rows2.append(["E.2.%02d" % k, "(%d,%d,%d,%d)" % (dt, dx, dy, dz), str(s2), cls, str(r2), vmin2,
                                  frm(tmin), frm(tmax), order])
    SUMMARY["e_rows"] = k
    SUMMARY["e_cls"] = cls_count
    SUMMARY["e_boostchecks"] = nboostchecks
    SUMMARY["e_nboosts"] = len(boosts)
    tab2 = longtable("@{}llrlrllll@{}", ["Id", "$(\\Delta t,\\Delta x,\\Delta y,\\Delta z)$", "$s^2$", "Class",
                                         "$|\\Delta\\vec{x}|^2$", "$v^2_{\\min}$", "min $\\Delta t'$", "max $\\Delta t'$",
                                         "Temporal order"], rows2)
    brows = []
    for i, (g, gv, v) in enumerate(boosts):
        brows.append(["E.3.%02d" % (i + 1), frm(v), frm(g), frm(gv), "$%s$" % fr(g * g - gv * gv)])
    tab3 = longtable("@{}lllll@{}", ["Id", "$v$", "$\\gamma$", "$\\gamma v$", "$\\gamma^2-\\gamma^2v^2$"], brows,
                     size="small", sep="6pt")
    write("tab_e1.tex", tab1)
    write("tab_e2.tex", tab2)
    write("tab_e3.tex", tab3)


# ---------------------------------------------------------------------------
# Volume F. SI quantities with mechanical dimensional analysis.
# Dimension vectors over (L, M, T, I, Theta, N, J).
# ---------------------------------------------------------------------------

BASE_DIM = ["L", "M", "T", "I", "\\Theta", "N", "J"]
BASE_UNIT = {"m": 0, "kg": 1, "s": 2, "A": 3, "K": 4, "mol": 5, "cd": 6}


def dvec(*pairs):
    v = [F(0)] * 7
    for i, e in pairs:
        v[i] += F(e)
    return tuple(v)


ZERO = tuple([F(0)] * 7)


def vadd(a, b, k=1):
    return tuple(x + k * y for x, y in zip(a, b))


NAMED_UNITS_SRC = [
    ("rad", "m m^-1"), ("sr", "m^2 m^-2"), ("Hz", "s^-1"), ("N", "kg m s^-2"), ("Pa", "N m^-2"), ("J", "N m"),
    ("W", "J s^-1"), ("C", "A s"), ("V", "W A^-1"), ("F", "C V^-1"), ("ohm", "V A^-1"), ("S", "A V^-1"),
    ("Wb", "V s"), ("T", "Wb m^-2"), ("H", "Wb A^-1"), ("degC", "K"), ("lm", "cd sr"), ("lx", "lm m^-2"),
    ("Bq", "s^-1"), ("Gy", "J kg^-1"), ("Sv", "J kg^-1"), ("kat", "mol s^-1"),
]
UNIT_DIM = {}


def parse_unit(s):
    v = ZERO
    if s.strip() == "1":
        return v
    for tok in s.split():
        if "^" in tok:
            u, e = tok.split("^")
            e = F(e)
        else:
            u, e = tok, F(1)
        if u in BASE_UNIT:
            d = dvec((BASE_UNIT[u], 1))
        else:
            d = UNIT_DIM[u]
        v = vadd(v, d, e)
    return v


for _u, _src in NAMED_UNITS_SRC:
    UNIT_DIM[_u] = parse_unit(_src)


def unit_tex(s):
    if s.strip() == "1":
        return "1"
    parts = []
    for tok in s.split():
        if "^" in tok:
            u, e = tok.split("^")
        else:
            u, e = tok, None
        u = {"ohm": "\\Omega", "degC": "{}^\\circ\\mathrm{C}"}.get(u, "\\mathrm{%s}" % u)
        parts.append("$" + u + ("^{%s}" % e if e else "") + "$")
    return " ".join(parts)


def dim_tex(v):
    parts = []
    for i, e in enumerate(v):
        if e != 0:
            parts.append("%s%s" % (BASE_DIM[i], "" if e == 1 else "^{%s}" % fr(e)))
    return "$" + ("\\,".join(parts) if parts else "1") + "$"


# key, name, symbol (TeX), relation {key: exponent}, SI unit, domain
# Base quantities have relation None.
SI = [
    ("l", "length", "l", None, "m", "base"),
    ("m", "mass", "m", None, "kg", "base"),
    ("t", "time (duration)", "t", None, "s", "base"),
    ("I", "electric current", "I", None, "A", "base"),
    ("T", "thermodynamic temperature", "T", None, "K", "base"),
    ("n", "amount of substance", "n", None, "mol", "base"),
    ("Iv", "luminous intensity", "I_v", None, "cd", "base"),
    # space and time
    ("N", "number of entities", "N", {}, "1", "space-time"),
    ("A", "area", "A", {"l": 2}, "m^2", "space-time"),
    ("V", "volume", "V", {"l": 3}, "m^3", "space-time"),
    ("ang", "plane angle", "\\alpha", {"l": 1, "l_": -1}, "rad", "space-time"),
    ("sang", "solid angle", "\\Omega", {"A": 1, "l": -2}, "sr", "space-time"),
    ("v", "velocity", "v", {"l": 1, "t": -1}, "m s^-1", "space-time"),
    ("c", "speed of light in vacuum", "c", {"l": 1, "t": -1}, "m s^-1", "constant"),
    ("a", "acceleration", "a", {"v": 1, "t": -1}, "m s^-2", "space-time"),
    ("jerk", "jerk", "j", {"a": 1, "t": -1}, "m s^-3", "space-time"),
    ("f", "frequency", "f", {"t": -1}, "Hz", "space-time"),
    ("om", "angular velocity", "\\omega", {"ang": 1, "t": -1}, "rad s^-1", "space-time"),
    ("alph", "angular acceleration", "\\dot\\omega", {"om": 1, "t": -1}, "rad s^-2", "space-time"),
    ("lam", "wavelength", "\\lambda", {"v": 1, "f": -1}, "m", "space-time"),
    ("sig", "wavenumber", "\\tilde\\nu", {"lam": -1}, "m^-1", "space-time"),
    ("kw", "angular wavenumber", "k", {"ang": 1, "lam": -1}, "rad m^-1", "space-time"),
    ("per", "period", "P", {"f": -1}, "s", "space-time"),
    ("kap", "curvature of a curve", "\\kappa", {"ang": 1, "l": -1}, "m^-1", "space-time"),
    ("s2", "spacetime interval (squared)", "s^2", {"c": 2, "t": 2}, "m^2", "space-time"),
    ("tau", "proper time", "\\tau", {"s2": F(1, 2), "c": -1}, "s", "space-time"),
    ("Riem", "Riemann curvature", "R^a{}_{bcd}", {"l": -2}, "m^-2", "space-time"),
    ("Lam", "cosmological constant", "\\Lambda", {"Riem": 1}, "m^-2", "space-time"),
    ("Hub", "Hubble parameter", "H_0", {"v": 1, "l": -1}, "s^-1", "space-time"),
    # mechanics
    ("rho", "mass density", "\\rho", {"m": 1, "V": -1}, "kg m^-3", "mechanics"),
    ("vsp", "specific volume", "v_s", {"V": 1, "m": -1}, "m^3 kg^-1", "mechanics"),
    ("rhoA", "surface density", "\\rho_A", {"m": 1, "A": -1}, "kg m^-2", "mechanics"),
    ("rhol", "linear density", "\\rho_l", {"m": 1, "l": -1}, "kg m^-1", "mechanics"),
    ("p", "momentum", "p", {"m": 1, "v": 1}, "kg m s^-1", "mechanics"),
    ("Fo", "force", "F", {"m": 1, "a": 1}, "N", "mechanics"),
    ("imp", "impulse", "J_p", {"Fo": 1, "t": 1}, "N s", "mechanics"),
    ("Lang", "angular momentum", "L", {"l": 1, "p": 1}, "kg m^2 s^-1", "mechanics"),
    ("mI", "moment of inertia", "J", {"m": 1, "l": 2}, "kg m^2", "mechanics"),
    ("tq", "torque", "\\tau_M", {"l": 1, "Fo": 1}, "N m", "mechanics"),
    ("aimp", "angular impulse", "H_\\tau", {"tq": 1, "t": 1}, "N m s", "mechanics"),
    ("pr", "pressure", "p_s", {"Fo": 1, "A": -1}, "Pa", "mechanics"),
    ("str", "normal stress", "\\sigma", {"Fo": 1, "A": -1}, "Pa", "mechanics"),
    ("strain", "linear strain", "\\varepsilon", {"l": 1, "l_": -1}, "1", "mechanics"),
    ("Ey", "Young modulus", "E", {"str": 1, "strain": -1}, "Pa", "mechanics"),
    ("Gs", "shear modulus", "G_s", {"str": 1, "strain": -1}, "Pa", "mechanics"),
    ("Kb", "bulk modulus", "K", {"pr": 1, "strain": -1}, "Pa", "mechanics"),
    ("comp", "compressibility", "\\kappa_T", {"Kb": -1}, "Pa^-1", "mechanics"),
    ("W", "work", "W", {"Fo": 1, "l": 1}, "J", "mechanics"),
    ("E", "energy", "E", {"W": 1}, "J", "mechanics"),
    ("Ek", "kinetic energy", "E_k", {"m": 1, "v": 2}, "J", "mechanics"),
    ("Ep", "potential energy (gravity)", "E_p", {"m": 1, "a": 1, "l": 1}, "J", "mechanics"),
    ("P", "power", "P", {"E": 1, "t": -1}, "W", "mechanics"),
    ("act", "action", "S_a", {"E": 1, "t": 1}, "J s", "mechanics"),
    ("eta", "dynamic viscosity", "\\eta", {"str": 1, "v": -1, "l": 1}, "Pa s", "mechanics"),
    ("nu", "kinematic viscosity", "\\nu", {"eta": 1, "rho": -1}, "m^2 s^-1", "mechanics"),
    ("gam", "surface tension", "\\gamma", {"Fo": 1, "l": -1}, "N m^-1", "mechanics"),
    ("ksp", "spring constant", "k_s", {"Fo": 1, "l": -1}, "N m^-1", "mechanics"),
    ("wden", "energy density", "w", {"E": 1, "V": -1}, "J m^-3", "mechanics"),
    ("qm", "mass flow rate", "q_m", {"m": 1, "t": -1}, "kg s^-1", "mechanics"),
    ("qV", "volume flow rate", "q_V", {"V": 1, "t": -1}, "m^3 s^-1", "mechanics"),
    ("G", "Newtonian constant of gravitation", "G", {"Fo": 1, "l": 2, "m": -2}, "N m^2 kg^-2", "mechanics"),
    ("gf", "gravitational field strength", "g", {"Fo": 1, "m": -1}, "N kg^-1", "mechanics"),
    ("gpot", "gravitational potential", "\\Phi_g", {"E": 1, "m": -1}, "J kg^-1", "mechanics"),
    ("mu_f", "coefficient of friction", "\\mu_f", {"Fo": 1, "Fo_": -1}, "1", "mechanics"),
    ("Iint", "intensity (power per area)", "I_P", {"P": 1, "A": -1}, "W m^-2", "mechanics"),
    ("pgrad", "pressure gradient", "\\nabla p", {"pr": 1, "l": -1}, "Pa m^-1", "mechanics"),
    ("Fl", "force per length", "F_l", {"Fo": 1, "l": -1}, "N m^-1", "mechanics"),
    ("kEin", "Einstein gravitational constant", "\\kappa_E", {"G": 1, "c": -4}, "N^-1", "constant"),
    # thermodynamics
    ("Qh", "heat", "Q_h", {"E": 1}, "J", "thermodynamics"),
    ("S", "entropy", "S", {"Qh": 1, "T": -1}, "J K^-1", "thermodynamics"),
    ("Cth", "heat capacity", "C_p", {"Qh": 1, "T": -1}, "J K^-1", "thermodynamics"),
    ("csp", "specific heat capacity", "c_p", {"Cth": 1, "m": -1}, "J kg^-1 K^-1", "thermodynamics"),
    ("Cm", "molar heat capacity", "C_m", {"Cth": 1, "n": -1}, "J mol^-1 K^-1", "thermodynamics"),
    ("phi", "heat flux density", "\\varphi", {"P": 1, "A": -1}, "W m^-2", "thermodynamics"),
    ("lth", "thermal conductivity", "\\lambda_{th}", {"phi": 1, "T": -1, "l": 1}, "W m^-1 K^-1", "thermodynamics"),
    ("Gth", "thermal conductance", "G_{th}", {"P": 1, "T": -1}, "W K^-1", "thermodynamics"),
    ("Rth", "thermal resistance", "R_{th}", {"Gth": -1}, "K W^-1", "thermodynamics"),
    ("ath", "thermal diffusivity", "a", {"lth": 1, "rho": -1, "csp": -1}, "m^2 s^-1", "thermodynamics"),
    ("alT", "linear expansion coefficient", "\\alpha_l", {"strain": 1, "T": -1}, "K^-1", "thermodynamics"),
    ("hT", "heat transfer coefficient", "h", {"phi": 1, "T": -1}, "W m^-2 K^-1", "thermodynamics"),
    ("Ssp", "specific entropy", "s", {"S": 1, "m": -1}, "J kg^-1 K^-1", "thermodynamics"),
    ("Sm", "molar entropy", "S_m", {"S": 1, "n": -1}, "J mol^-1 K^-1", "thermodynamics"),
    ("lat", "specific latent heat", "l_h", {"Qh": 1, "m": -1}, "J kg^-1", "thermodynamics"),
    ("kB", "Boltzmann constant", "k", {"E": 1, "T": -1}, "J K^-1", "constant"),
    ("sigSB", "Stefan--Boltzmann constant", "\\sigma", {"phi": 1, "T": -4}, "W m^-2 K^-4", "constant"),
    ("bW", "Wien displacement constant", "b", {"lam": 1, "T": 1}, "m K", "constant"),
    # chemistry
    ("Mm", "molar mass", "M", {"m": 1, "n": -1}, "kg mol^-1", "chemistry"),
    ("Vm", "molar volume", "V_m", {"V": 1, "n": -1}, "m^3 mol^-1", "chemistry"),
    ("cn", "amount concentration", "c_n", {"n": 1, "V": -1}, "mol m^-3", "chemistry"),
    ("bmol", "molality", "b", {"n": 1, "m": -1}, "mol kg^-1", "chemistry"),
    ("gmc", "mass concentration", "\\gamma_m", {"m": 1, "V": -1}, "kg m^-3", "chemistry"),
    ("NA", "Avogadro constant", "N_A", {"N": 1, "n": -1}, "mol^-1", "constant"),
    ("R", "molar gas constant", "R", {"pr": 1, "V": 1, "n": -1, "T": -1}, "J mol^-1 K^-1", "constant"),
    ("kat", "catalytic activity", "z", {"n": 1, "t": -1}, "kat", "chemistry"),
    ("Emol", "molar energy", "E_m", {"E": 1, "n": -1}, "J mol^-1", "chemistry"),
    ("chem", "chemical potential", "\\mu", {"E": 1, "n": -1}, "J mol^-1", "chemistry"),
    ("ndens", "number density", "n_N", {"N": 1, "V": -1}, "m^-3", "chemistry"),
    ("xfr", "amount fraction", "x", {"n": 1, "n_": -1}, "1", "chemistry"),
    ("rrate", "rate of reaction (volumic)", "r", {"cn": 1, "t": -1}, "mol m^-3 s^-1", "chemistry"),
    ("Dif", "diffusion coefficient", "D", {"n": 1, "A": -1, "t": -1, "cn": -1, "l": 1}, "m^2 s^-1", "chemistry"),
    # electromagnetism
    ("q", "electric charge", "q", {"I": 1, "t": 1}, "C", "electromagnetism"),
    ("rhoq", "charge density", "\\rho_q", {"q": 1, "V": -1}, "C m^-3", "electromagnetism"),
    ("sigq", "surface charge density", "\\sigma_q", {"q": 1, "A": -1}, "C m^-2", "electromagnetism"),
    ("lamq", "linear charge density", "\\lambda_q", {"q": 1, "l": -1}, "C m^-1", "electromagnetism"),
    ("J", "current density", "J", {"I": 1, "A": -1}, "A m^-2", "electromagnetism"),
    ("Ef", "electric field strength", "E", {"Fo": 1, "q": -1}, "V m^-1", "electromagnetism"),
    ("Vp", "electric potential", "V", {"E": 1, "q": -1}, "V", "electromagnetism"),
    ("emf", "electromotive force", "\\mathcal{E}", {"E": 1, "q": -1}, "V", "electromagnetism"),
    ("Cap", "capacitance", "C", {"q": 1, "Vp": -1}, "F", "electromagnetism"),
    ("Res", "resistance", "R_e", {"Vp": 1, "I": -1}, "ohm", "electromagnetism"),
    ("Gc", "conductance", "G_e", {"I": 1, "Vp": -1}, "S", "electromagnetism"),
    ("resy", "resistivity", "\\rho_e", {"Res": 1, "A": 1, "l": -1}, "ohm m", "electromagnetism"),
    ("cond", "conductivity", "\\sigma_e", {"resy": -1}, "S m^-1", "electromagnetism"),
    ("Bf", "magnetic flux density", "B", {"Fo": 1, "q": -1, "v": -1}, "T", "electromagnetism"),
    ("Phi", "magnetic flux", "\\Phi", {"Bf": 1, "A": 1}, "Wb", "electromagnetism"),
    ("Lind", "inductance", "L_i", {"Phi": 1, "I": -1}, "H", "electromagnetism"),
    ("Hf", "magnetic field strength", "H", {"I": 1, "l": -1}, "A m^-1", "electromagnetism"),
    ("Dd", "electric displacement", "D_e", {"q": 1, "A": -1}, "C m^-2", "electromagnetism"),
    ("eps", "permittivity", "\\varepsilon", {"Dd": 1, "Ef": -1}, "F m^-1", "electromagnetism"),
    ("mu", "permeability", "\\mu_m", {"Bf": 1, "Hf": -1}, "H m^-1", "electromagnetism"),
    ("pdip", "electric dipole moment", "p_e", {"q": 1, "l": 1}, "C m", "electromagnetism"),
    ("mmag", "magnetic moment", "m_m", {"I": 1, "A": 1}, "A m^2", "electromagnetism"),
    ("Pol", "electric polarization", "P_e", {"pdip": 1, "V": -1}, "C m^-2", "electromagnetism"),
    ("Mag", "magnetization", "M", {"mmag": 1, "V": -1}, "A m^-1", "electromagnetism"),
    ("Psi", "electric flux", "\\Psi", {"Dd": 1, "A": 1}, "C", "electromagnetism"),
    ("Poy", "Poynting vector", "S_P", {"Ef": 1, "Hf": 1}, "W m^-2", "electromagnetism"),
    ("Apot", "magnetic vector potential", "A_m", {"Bf": 1, "l": 1}, "Wb m^-1", "electromagnetism"),
    ("Imp", "impedance", "Z", {"Vp": 1, "I": -1}, "ohm", "electromagnetism"),
    ("Rel", "reluctance", "R_m", {"I": 1, "Phi": -1}, "H^-1", "electromagnetism"),
    ("qm_r", "charge-to-mass ratio", "q/m", {"q": 1, "m": -1}, "C kg^-1", "electromagnetism"),
    ("mob", "electric mobility", "\\mu_e", {"v": 1, "Ef": -1}, "m^2 V^-1 s^-1", "electromagnetism"),
    ("RH", "Hall coefficient", "R_H", {"Ef": 1, "J": -1, "Bf": -1}, "m^3 C^-1", "electromagnetism"),
    ("gyro", "gyromagnetic ratio", "\\gamma_g", {"mmag": 1, "Lang": -1}, "s^-1 T^-1", "electromagnetism"),
    ("eps0", "electric constant", "\\varepsilon_0", {"q": 2, "Fo": -1, "l": -2}, "F m^-1", "constant"),
    ("mu0", "magnetic constant", "\\mu_0", {"Fo": 1, "I": -2}, "N A^-2", "constant"),
    ("e", "elementary charge", "e", {"q": 1}, "C", "constant"),
    ("Far", "Faraday constant", "F_c", {"q": 1, "n": -1}, "C mol^-1", "constant"),
    ("Z0", "impedance of vacuum", "Z_0", {"mu0": 1, "c": 1}, "ohm", "constant"),
    # radiometry, photometry, optics, acoustics
    ("Phie", "radiant flux", "\\Phi_e", {"E": 1, "t": -1}, "W", "radiation"),
    ("Ie", "radiant intensity", "I_e", {"Phie": 1, "sang": -1}, "W sr^-1", "radiation"),
    ("Le", "radiance", "L_e", {"Ie": 1, "A": -1}, "W sr^-1 m^-2", "radiation"),
    ("Ee", "irradiance", "E_e", {"Phie": 1, "A": -1}, "W m^-2", "radiation"),
    ("He", "radiant exposure", "H_e", {"Ee": 1, "t": 1}, "J m^-2", "radiation"),
    ("Bnu", "spectral radiance (frequency)", "B_\\nu", {"Le": 1, "f": -1}, "W sr^-1 m^-2 Hz^-1", "radiation"),
    ("Llam", "spectral radiance (wavelength)", "L_\\lambda", {"Le": 1, "lam": -1}, "W sr^-1 m^-3", "radiation"),
    ("Phiv", "luminous flux", "\\Phi_v", {"Iv": 1, "sang": 1}, "lm", "radiation"),
    ("Evl", "illuminance", "E_v", {"Phiv": 1, "A": -1}, "lx", "radiation"),
    ("Lv", "luminance", "L_v", {"Iv": 1, "A": -1}, "cd m^-2", "radiation"),
    ("Qv", "luminous energy", "Q_v", {"Phiv": 1, "t": 1}, "lm s", "radiation"),
    ("Hv", "luminous exposure", "H_v", {"Evl": 1, "t": 1}, "lx s", "radiation"),
    ("Keff", "luminous efficacy", "K", {"Phiv": 1, "Phie": -1}, "lm W^-1", "radiation"),
    ("Kcd", "luminous efficacy of 540 THz radiation", "K_{cd}", {"Keff": 1}, "lm W^-1", "constant"),
    ("verg", "vergence (optical power)", "\\Phi_o", {"l": -1}, "m^-1", "radiation"),
    ("nref", "refractive index", "n_r", {"c": 1, "v": -1}, "1", "radiation"),
    ("prad", "radiation pressure", "p_r", {"Iint": 1, "c": -1}, "Pa", "radiation"),
    ("Zac", "specific acoustic impedance", "Z_a", {"pr": 1, "v": -1}, "Pa s m^-1", "radiation"),
    # ionizing radiation and nuclear
    ("Act", "activity", "A_r", {"N": 1, "t": -1}, "Bq", "nuclear"),
    ("Dabs", "absorbed dose", "D", {"E": 1, "m": -1}, "Gy", "nuclear"),
    ("Hdose", "dose equivalent", "H_d", {"Dabs": 1}, "Sv", "nuclear"),
    ("Kerma", "kerma", "K_e", {"E": 1, "m": -1}, "Gy", "nuclear"),
    ("Drate", "absorbed dose rate", "\\dot D", {"Dabs": 1, "t": -1}, "Gy s^-1", "nuclear"),
    ("Xexp", "exposure (ionization)", "X", {"q": 1, "m": -1}, "C kg^-1", "nuclear"),
    ("lamd", "decay constant", "\\lambda_d", {"t": -1}, "s^-1", "nuclear"),
    ("thalf", "half-life", "T_{1/2}", {"lamd": -1}, "s", "nuclear"),
    ("xs", "cross section", "\\sigma_x", {"A": 1}, "m^2", "nuclear"),
    ("flu", "particle fluence", "\\Phi_p", {"N": 1, "A": -1}, "m^-2", "nuclear"),
    ("flur", "fluence rate", "\\dot\\Phi_p", {"flu": 1, "t": -1}, "m^-2 s^-1", "nuclear"),
    ("mfp", "mean free path", "l_f", {"ndens": -1, "xs": -1}, "m", "nuclear"),
    ("muatt", "linear attenuation coefficient", "\\mu_a", {"l": -1}, "m^-1", "nuclear"),
    ("mumass", "mass attenuation coefficient", "\\mu_\\rho", {"muatt": 1, "rho": -1}, "m^2 kg^-1", "nuclear"),
    # quantum and atomic
    ("h", "Planck constant", "h", {"E": 1, "f": -1}, "J s", "constant"),
    ("hbar", "reduced Planck constant", "\\hbar", {"h": 1, "ang": -1}, "J s", "constant"),
    ("spin", "spin angular momentum", "S_s", {"hbar": 1}, "J s", "quantum"),
    ("muB", "Bohr magneton", "\\mu_B", {"e": 1, "hbar": 1, "m": -1}, "J T^-1", "constant"),
    ("Ryd", "Rydberg constant", "R_\\infty", {"sig": 1}, "m^-1", "constant"),
    ("alpha", "fine-structure constant", "\\alpha_{em}", {"e": 2, "eps0": -1, "hbar": -1, "c": -1}, "1", "constant"),
    ("lamC", "Compton wavelength", "\\lambda_C", {"h": 1, "m": -1, "c": -1}, "m", "quantum"),
    ("lamdB", "de Broglie wavelength", "\\lambda_{dB}", {"h": 1, "p": -1}, "m", "quantum"),
    ("KJ", "Josephson constant", "K_J", {"e": 1, "h": -1}, "Hz V^-1", "constant"),
    ("RK", "von Klitzing constant", "R_K", {"h": 1, "e": -2}, "ohm", "constant"),
    ("Phi0", "magnetic flux quantum", "\\Phi_0", {"h": 1, "e": -1}, "Wb", "constant"),
    ("G0", "conductance quantum", "G_0", {"e": 2, "h": -1}, "S", "constant"),
    ("a0", "Bohr radius", "a_0", {"eps0": 1, "hbar": 2, "m": -1, "e": -2}, "m", "constant"),
    ("lP", "Planck length", "l_P", {"hbar": F(1, 2), "G": F(1, 2), "c": F(-3, 2)}, "m", "constant"),
    ("tP", "Planck time", "t_P", {"hbar": F(1, 2), "G": F(1, 2), "c": F(-5, 2)}, "s", "constant"),
    ("mP", "Planck mass", "m_P", {"hbar": F(1, 2), "c": F(1, 2), "G": F(-1, 2)}, "kg", "constant"),
    ("TP", "Planck temperature", "T_P", {"mP": 1, "c": 2, "kB": -1}, "K", "constant"),
    ("qP", "Planck charge", "q_P", {"eps0": F(1, 2), "hbar": F(1, 2), "c": F(1, 2)}, "C", "constant"),
    ("rs", "Schwarzschild radius", "r_s", {"G": 1, "m": 1, "c": -2}, "m", "quantum"),
    ("Tmn", "stress-energy (energy density)", "T_{00}", {"wden": 1}, "J m^-3", "space-time"),
]
SI_KEYS = {}
for _row in SI:
    SI_KEYS[_row[0]] = _row
# keys with a trailing underscore denote a second, independent occurrence of the same quantity
ALIASES = {"l_": "l", "Fo_": "Fo", "n_": "n"}

# Mapping of SI quantities onto entries of the inventory (Volume K)
SI_TO_K = {"l": "K.06", "t": "K.07", "m": "K.24", "I": "K.69", "T": "K.61", "n": "K.68", "Iv": "K.67",
           "q": "K.35", "e": "K.35", "E": "K.26", "p": "K.27", "v": "K.28", "Lang": "K.29", "Ef": "K.37",
           "Bf": "K.38", "S": "K.62", "pr": "K.63", "mmag": "K.70", "s2": "K.02", "tau": "K.05",
           "Riem": "K.10", "Lam": "K.60", "spin": "K.20", "N": "K.68b", "Tmn": "K.84"}


def si_dims():
    dims = {}
    for key, name, sym, rel, unit, dom in SI:
        if rel is None:
            dims[key] = dvec((BASE_UNIT[unit], 1))
        else:
            d = ZERO
            for k2, e in rel.items():
                kk = ALIASES.get(k2, k2)
                check(kk in dims, "relation of %s uses earlier quantity %s" % (key, kk))
                d = vadd(d, dims[kk], F(e))
            dims[key] = d
        check(dims[key] == parse_unit(unit), "unit of %s agrees with its defining relation" % key)
    return dims


def rel_tex(rel):
    if rel is None:
        return "base"
    if not rel:
        return "count"
    parts = []
    for k2, e in rel.items():
        kk = ALIASES.get(k2, k2)
        sym = SI_KEYS[kk][2]
        e = F(e)
        if e == 1:
            parts.append(sym)
        else:
            parts.append("{%s}^{%s}" % (sym, fr(e)))
    return "$" + "\\,".join(parts) + "$"


EXACT_CONSTANTS = [
    ("F.0.1", "hyperfine transition frequency of $^{133}$Cs", "$\\Delta\\nu_{\\mathrm{Cs}}$", "9\\,192\\,631\\,770", "Hz", "f"),
    ("F.0.2", "speed of light in vacuum", "$c$", "299\\,792\\,458", "m s^-1", "c"),
    ("F.0.3", "Planck constant", "$h$", "6.626\\,070\\,15\\times 10^{-34}", "J s", "h"),
    ("F.0.4", "elementary charge", "$e$", "1.602\\,176\\,634\\times 10^{-19}", "C", "e"),
    ("F.0.5", "Boltzmann constant", "$k$", "1.380\\,649\\times 10^{-23}", "J K^-1", "kB"),
    ("F.0.6", "Avogadro constant", "$N_A$", "6.022\\,140\\,76\\times 10^{23}", "mol^-1", "NA"),
    ("F.0.7", "luminous efficacy of 540 THz radiation", "$K_{\\mathrm{cd}}$", "683", "lm W^-1", "Kcd"),
]


def vol_f(dims, kverd):
    rows0 = []
    for cid, name, sym, val, unit, key in EXACT_CONSTANTS:
        check(parse_unit(unit) == dims[key], "unit of defining constant %s" % cid)
        rows0.append([cid, name, sym, "$%s$" % val, unit_tex(unit), dim_tex(dims[key])])
    tab0 = longtable("@{}llllll@{}", ["Id", "Defining constant", "Sym.", "Exact value", "Unit", "Dimension"], rows0)
    rowsu = []
    for i, (u, src) in enumerate(NAMED_UNITS_SRC):
        rowsu.append(["F.U.%02d" % (i + 1), unit_tex(u), unit_tex(src), dim_tex(UNIT_DIM[u])])
    tabu = longtable("@{}llll@{}", ["Id", "Unit", "Definition", "Dimension (computed)"], rowsu, size="small", sep="6pt")

    # inventory support and verdict for every SI quantity
    info = {}
    rows = []
    mism = []
    ncons = 0
    for i, (key, name, sym, rel, unit, dom) in enumerate(SI):
        if key in SI_TO_K:
            kid = SI_TO_K[key]
            verdict, support = kverd[kid]["verdict"], kverd[kid]["support"]
            how = kid
        else:
            sup = set()
            for k2 in rel:
                kk = ALIASES.get(k2, k2)
                sup |= info[kk]["support"]
            verdict = "constructed"
            support = sup
            how = "SI rel."
        info[key] = {"verdict": verdict, "support": support}
        sistatus = "base" if rel is None else "derived"
        if (sistatus == "base") != (verdict == "genuine"):
            pass
        if sistatus == "derived" and verdict == "genuine":
            mism.append(key)
        if sistatus == "base" and verdict == "genuine":
            mism.append(key)
        if verdict == "constructed":
            ncons += 1
        rows.append(["F.%03d" % (i + 1), name, "$%s$" % sym, rel_tex(rel), unit_tex(unit), dim_tex(dims[key]),
                     verdict[:4] + ".", how, support_tex(support)])
    SUMMARY["f_n"] = len(SI)
    SUMMARY["f_genuine"] = [k for k in info if info[k]["verdict"] == "genuine"]
    SUMMARY["f_prov"] = [k for k in info if info[k]["verdict"] == "provisional"]
    SUMMARY["f_cons"] = ncons
    SUMMARY["f_base_genuine"] = [k for k in ("l", "m", "t", "I", "T", "n", "Iv") if info[k]["verdict"] == "genuine"]
    tab = longtable("@{}lp{2.4cm}lp{1.9cm}p{1.7cm}p{2.3cm}llp{2.0cm}@{}",
                    ["Id", "Quantity", "Sym.", "Def.\\ relation", "SI unit", "Dimension (checked)", "Verd.", "Via",
                     "Support"], rows, sep="2.5pt")
    write("tab_f0.tex", tab0)
    write("tab_fu.tex", tabu)
    write("tab_f.tex", tab)
    return info


def support_tex(sup):
    order = sorted(sup)
    return ", ".join(s.replace("K.", "") for s in order) if order else "$\\varnothing$"


# ---------------------------------------------------------------------------
# Volume G. Dimensional homogeneity of laws.
# ---------------------------------------------------------------------------

# Each law: id, name, list of terms (dicts), list of arguments of transcendental functions (dicts)
LAWS = [
    ("Newton's second law", [{"Fo": 1}, {"m": 1, "a": 1}], []),
    ("Newtonian gravitation", [{"Fo": 1}, {"G": 1, "m": 2, "l": -2}], []),
    ("Coulomb's law", [{"Fo": 1}, {"q": 2, "eps0": -1, "l": -2}], []),
    ("Lorentz force", [{"Fo": 1}, {"q": 1, "Ef": 1}, {"q": 1, "v": 1, "Bf": 1}], []),
    ("Gauss's law", [{"Ef": 1, "l": -1}, {"rhoq": 1, "eps0": -1}], []),
    ("Faraday's law (differential)", [{"Ef": 1, "l": -1}, {"Bf": 1, "t": -1}], []),
    ("Amp\\`ere--Maxwell law", [{"Bf": 1, "l": -1}, {"mu0": 1, "J": 1}, {"mu0": 1, "eps0": 1, "Ef": 1, "t": -1}], []),
    ("$c^2 = 1/(\\varepsilon_0\\mu_0)$", [{"c": 2}, {"eps0": -1, "mu0": -1}], []),
    ("Continuity of charge", [{"rhoq": 1, "t": -1}, {"J": 1, "l": -1}], []),
    ("Ohm's law", [{"Vp": 1}, {"Res": 1, "I": 1}], []),
    ("Joule heating", [{"P": 1}, {"I": 2, "Res": 1}], []),
    ("Field energy density", [{"wden": 1}, {"eps0": 1, "Ef": 2}, {"Bf": 2, "mu0": -1}], []),
    ("Poynting theorem", [{"wden": 1, "t": -1}, {"Poy": 1, "l": -1}, {"J": 1, "Ef": 1}], []),
    ("Kinetic energy", [{"Ek": 1}, {"m": 1, "v": 2}], []),
    ("Mass--energy relation", [{"E": 1}, {"m": 1, "c": 2}], []),
    ("Energy--momentum relation", [{"E": 2}, {"p": 2, "c": 2}, {"m": 2, "c": 4}], []),
    ("Lorentz factor", [], [{"v": 2, "c": -2}]),
    ("Spacetime interval", [{"s2": 1}, {"c": 2, "t": 2}, {"l": 2}], []),
    ("Planck--Einstein relation", [{"E": 1}, {"h": 1, "f": 1}], []),
    ("de Broglie relation", [{"lam": 1}, {"h": 1, "p": -1}], []),
    ("Schr\\\"odinger equation", [{"hbar": 1, "t": -1}, {"hbar": 2, "m": -1, "l": -2}, {"E": 1}], []),
    ("Uncertainty relation", [{"l": 1, "p": 1}, {"hbar": 1}], []),
    ("Dirac equation (mass term)", [{"hbar": 1, "l": -1}, {"m": 1, "c": 1}], []),
    ("Klein--Gordon equation", [{"t": -2, "c": -2}, {"l": -2}, {"m": 2, "c": 2, "hbar": -2}], []),
    ("Compton shift", [{"lam": 1}, {"h": 1, "m": -1, "c": -1}], []),
    ("Photoelectric equation", [{"Ek": 1}, {"h": 1, "f": 1}, {"E": 1}], []),
    ("Rydberg formula", [{"sig": 1}, {"Ryd": 1}], []),
    ("Bohr radius", [{"a0": 1}, {"eps0": 1, "hbar": 2, "m": -1, "e": -2}], []),
    ("Fine-structure constant", [], [{"e": 2, "eps0": -1, "hbar": -1, "c": -1}]),
    ("Cyclotron frequency", [{"om": 1}, {"q": 1, "Bf": 1, "m": -1}], []),
    ("Larmor precession", [{"om": 1}, {"gyro": 1, "Bf": 1}], []),
    ("Josephson relation", [{"f": 1}, {"e": 1, "Vp": 1, "h": -1}], []),
    ("Quantum Hall resistance", [{"Res": 1}, {"h": 1, "e": -2}], []),
    ("Ideal gas law (molar)", [{"pr": 1, "V": 1}, {"n": 1, "R": 1, "T": 1}], []),
    ("Ideal gas law (molecular)", [{"pr": 1, "V": 1}, {"N": 1, "kB": 1, "T": 1}], []),
    ("$R = N_A k$", [{"R": 1}, {"NA": 1, "kB": 1}], []),
    ("Boltzmann entropy", [{"S": 1}, {"kB": 1}], []),
    ("Clausius entropy", [{"S": 1}, {"Qh": 1, "T": -1}], []),
    ("First law", [{"E": 1}, {"Qh": 1}, {"pr": 1, "V": 1}], []),
    ("Gibbs energy", [{"E": 1}, {"T": 1, "S": 1}], []),
    ("Equipartition", [{"E": 1}, {"kB": 1, "T": 1}], []),
    ("Boltzmann factor", [], [{"E": 1, "kB": -1, "T": -1}]),
    ("Arrhenius equation", [], [{"Emol": 1, "R": -1, "T": -1}]),
    ("Nernst equation", [{"Vp": 1}, {"R": 1, "T": 1, "Far": -1}], []),
    ("$F = N_A e$", [{"Far": 1}, {"NA": 1, "e": 1}], []),
    ("Stefan--Boltzmann law", [{"phi": 1}, {"sigSB": 1, "T": 4}], []),
    ("Wien displacement law", [{"lam": 1, "T": 1}, {"bW": 1}], []),
    ("Planck's law", [{"Bnu": 1}, {"h": 1, "f": 3, "c": -2}], [{"h": 1, "f": 1, "kB": -1, "T": -1}]),
    ("Fourier's law", [{"phi": 1}, {"lth": 1, "T": 1, "l": -1}], []),
    ("Heat equation", [{"T": 1, "t": -1}, {"ath": 1, "T": 1, "l": -2}], []),
    ("Fick's first law", [{"n": 1, "A": -1, "t": -1}, {"Dif": 1, "cn": 1, "l": -1}], []),
    ("Wave equation", [{"l": 1, "t": -2}, {"v": 2, "l": -1}], []),
    ("Bernoulli's equation", [{"pr": 1}, {"rho": 1, "v": 2}, {"rho": 1, "gf": 1, "l": 1}], []),
    ("Navier--Stokes equation", [{"rho": 1, "v": 1, "t": -1}, {"rho": 1, "v": 2, "l": -1}, {"pr": 1, "l": -1},
                                 {"eta": 1, "v": 1, "l": -2}, {"Fo": 1, "V": -1}], []),
    ("Hydrostatic pressure", [{"pr": 1}, {"rho": 1, "gf": 1, "l": 1}], []),
    ("Stokes drag", [{"Fo": 1}, {"eta": 1, "l": 1, "v": 1}], []),
    ("Hagen--Poiseuille law", [{"qV": 1}, {"l": 4, "pgrad": 1, "eta": -1}], []),
    ("Hooke's law (spring)", [{"Fo": 1}, {"ksp": 1, "l": 1}], []),
    ("Hooke's law (material)", [{"str": 1}, {"Ey": 1, "strain": 1}], []),
    ("Pendulum period", [{"per": 2}, {"l": 1, "gf": -1}], []),
    ("Kepler's third law", [{"per": 2}, {"l": 3, "G": -1, "m": -1}], []),
    ("Escape speed", [{"v": 2}, {"G": 1, "m": 1, "l": -1}], []),
    ("Schwarzschild radius", [{"rs": 1}, {"G": 1, "m": 1, "c": -2}], []),
    ("Einstein field equations", [{"Riem": 1}, {"Lam": 1}, {"kEin": 1, "Tmn": 1}], []),
    ("Friedmann equation", [{"Hub": 2}, {"G": 1, "rho": 1}, {"c": 2, "l": -2}, {"Lam": 1, "c": 2}], []),
    ("Hubble's law", [{"v": 1}, {"Hub": 1, "l": 1}], []),
    ("Radiation pressure", [{"prad": 1}, {"Iint": 1, "c": -1}], []),
    ("Photon momentum", [{"p": 1}, {"E": 1, "c": -1}], []),
    ("Larmor radiated power", [{"P": 1}, {"q": 2, "a": 2, "eps0": -1, "c": -3}], []),
    ("Capacitor energy", [{"E": 1}, {"Cap": 1, "Vp": 2}], []),
    ("Inductor energy", [{"E": 1}, {"Lind": 1, "I": 2}], []),
    ("RC time constant", [{"t": 1}, {"Res": 1, "Cap": 1}], []),
    ("LC resonance", [{"om": 2}, {"Lind": -1, "Cap": -1}], []),
    ("Faraday induction (integral)", [{"emf": 1}, {"Phi": 1, "t": -1}], []),
    ("Field of a straight wire", [{"Bf": 1}, {"mu0": 1, "I": 1, "l": -1}], []),
    ("Coulomb potential energy", [{"E": 1}, {"q": 2, "eps0": -1, "l": -1}], []),
    ("Mean molecular speed", [{"v": 2}, {"kB": 1, "T": 1, "m": -1}], []),
    ("Speed of sound", [{"v": 2}, {"Kb": 1, "rho": -1}], []),
    ("Wave speed on a string", [{"v": 2}, {"Fo": 1, "rhol": -1}], []),
    ("Torricelli's law", [{"v": 2}, {"gf": 1, "l": 1}], []),
    ("Radioactive decay", [{"Act": 1}, {"lamd": 1, "N": 1}], [{"lamd": 1, "t": 1}]),
    ("Beer--Lambert law", [], [{"muatt": 1, "l": 1}]),
    ("Mean free path", [{"mfp": 1}, {"ndens": -1, "xs": -1}], []),
]

BAD_LAWS = [
    ("E = m c", [{"E": 1}, {"m": 1, "c": 1}], []),
    ("F = m v", [{"Fo": 1}, {"m": 1, "v": 1}], []),
    ("pV = nT", [{"pr": 1, "V": 1}, {"n": 1, "T": 1}], []),
    ("exp(-E/T)", [], [{"E": 1, "T": -1}]),
]


def dim_of(term, dims):
    d = ZERO
    for k, e in term.items():
        d = vadd(d, dims[ALIASES.get(k, k)], F(e))
    return d


def term_tex(term):
    parts = []
    for k, e in term.items():
        sym = SI_KEYS[ALIASES.get(k, k)][2]
        e = F(e)
        parts.append(sym if e == 1 else "{%s}^{%s}" % (sym, fr(e)))
    return "\\,".join(parts)


def law_ok(terms, args, dims):
    ds = [dim_of(t, dims) for t in terms]
    ok = all(d == ds[0] for d in ds)
    ok = ok and all(dim_of(a, dims) == ZERO for a in args)
    return ok, ds


def vol_g(dims):
    rows = []
    nterms = 0
    for i, (name, terms, args) in enumerate(LAWS):
        ok, ds = law_ok(terms, args, dims)
        check(ok, "law %s homogeneous" % name)
        nterms += len(terms) + len(args)
        tt = " \\sim ".join(term_tex(t) for t in terms)
        at = "; ".join(term_tex(a) for a in args)
        rows.append(["G.%02d" % (i + 1), name, "$%s$" % tt if tt else "--", "$%s$" % at if at else "--",
                     dim_tex(ds[0]) if ds else "--", str(len(terms)), "ok"])
    for name, terms, args in BAD_LAWS:
        ok, ds = law_ok(terms, args, dims)
        check(not ok, "deliberately ill-formed relation %s is rejected" % name)
    SUMMARY["g_n"] = len(LAWS)
    SUMMARY["g_terms"] = nterms
    SUMMARY["g_bad"] = len(BAD_LAWS)
    tab = longtable("@{}lp{3.0cm}p{5.6cm}p{2.0cm}p{2.3cm}rl@{}",
                    ["Id", "Law", "Terms (each must agree)", "Dimensionless args.", "Common dim.", "$n$", "Chk"],
                    rows)
    write("tab_g.tex", tab)


# ---------------------------------------------------------------------------
# Volume H. Buckingham Pi groups computed by exact null spaces.
# ---------------------------------------------------------------------------

PI_PROBLEMS = [
    ("Simple pendulum", ["l", "gf", "m", "per"]),
    ("Projectile range", ["v", "gf", "l"]),
    ("Drag on a sphere", ["rho", "v", "l", "eta", "Fo"]),
    ("Pressure drop in a pipe", ["rho", "v", "l", "eta", "pgrad"]),
    ("Deep-water gravity waves", ["gf", "lam", "v"]),
    ("Capillary waves", ["gam", "rho", "lam", "v"]),
    ("Mass on a spring", ["ksp", "m", "per"]),
    ("Kepler orbit", ["G", "m", "l", "per"]),
    ("Taylor blast wave", ["E", "rho", "t", "l"]),
    ("Black-body energy density", ["kB", "T", "h", "c", "wden"]),
    ("Size of the hydrogen atom", ["hbar", "m", "e", "eps0", "l"]),
    ("Planck scale", ["G", "hbar", "c", "l"]),
    ("Fine structure", ["e", "eps0", "hbar", "c"]),
    ("Transient heat conduction", ["ath", "l", "t"]),
    ("Natural convection", ["l", "nu", "ath", "gf", "alT", "T"]),
    ("Vibrating string", ["Fo", "rhol", "l", "f"]),
    ("Sound in a gas", ["pr", "rho", "v"]),
    ("Soap bubble", ["gam", "l", "pr"]),
    ("Capillary rise", ["gam", "rho", "gf", "l", "l_"]),
    ("Stokes settling", ["eta", "gf", "l", "rho", "v"]),
    ("Escape speed", ["G", "m", "l", "v"]),
    ("Schwarzschild radius", ["G", "m", "c", "l"]),
    ("LC oscillator", ["Lind", "Cap", "f"]),
    ("RC circuit", ["Res", "Cap", "t"]),
    ("Cyclotron", ["q", "Bf", "m", "f"]),
    ("Plasma frequency", ["ndens", "e", "eps0", "m", "om"]),
    ("Debye length", ["eps0", "kB", "T", "ndens", "e", "l"]),
    ("Thermal de Broglie wavelength", ["h", "m", "kB", "T", "lam"]),
    ("Compton wavelength", ["h", "m", "c", "lam"]),
    ("Wien peak", ["h", "c", "kB", "T", "lam"]),
    ("Ideal gas", ["pr", "V", "N", "kB", "T"]),
    ("Poiseuille flow", ["pgrad", "l", "eta", "qV"]),
    ("Torricelli outflow", ["gf", "l", "v"]),
    ("Circular motion", ["m", "v", "l", "Fo"]),
    ("Electrostatic force", ["q", "eps0", "l", "Fo"]),
    ("Force between currents", ["mu0", "I", "l", "Fl"]),
    ("Larmor radius", ["m", "v", "q", "Bf", "l"]),
    ("Jeans length", ["G", "rho", "v", "l"]),
    ("Hubble time", ["Hub", "t"]),
    ("Oscillating drop", ["gam", "rho", "l", "f"]),
    ("Ship waves", ["v", "gf", "l"]),
    ("Wind turbine", ["rho", "v", "l", "P"]),
    ("Droplet break-up", ["rho", "v", "l", "gam"]),
    ("Convective heat transfer", ["hT", "l", "lth"]),
    ("Supersonic flow", ["v", "v_"]),
    ("Thermal radiation of a body", ["sigSB", "T", "A", "P"]),
    ("Quantum Hall effect", ["h", "e", "Res"]),
    ("Josephson effect", ["e", "h", "Vp", "f"]),
    ("Vacuum energy", ["Lam", "c", "G", "rho"]),
    ("Rotating disk", ["mI", "om", "E"]),
    ("Gyromagnetic ratio of a charged body", ["q", "m", "gyro"]),
    ("Magnetic moment of an orbit", ["q", "m", "Lang", "mmag"]),
    ("Heated wire", ["I", "Res", "Gth", "T"]),
    ("Viscous dissipation", ["eta", "v", "l", "P"]),
    ("Sedimentation diffusion", ["Dif", "kB", "T", "eta", "l"]),
    ("Gravitational collapse time", ["G", "rho", "t"]),
    ("Radiation pressure on a mirror", ["Iint", "c", "A", "Fo"]),
    ("Planck temperature", ["hbar", "c", "G", "kB", "T"]),
]
PI_ALIASES = {"v_": "v", "l_": "l"}


def nullspace(mat, ncols):
    """Exact RREF null space; mat is a list of rows of Fractions."""
    m = [row[:] for row in mat]
    piv = []
    r = 0
    for c in range(ncols):
        pr = None
        for i in range(r, len(m)):
            if m[i][c] != 0:
                pr = i
                break
        if pr is None:
            continue
        m[r], m[pr] = m[pr], m[r]
        pv = m[r][c]
        m[r] = [x / pv for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                fac = m[i][c]
                m[i] = [a - fac * b for a, b in zip(m[i], m[r])]
        piv.append(c)
        r += 1
        if r == len(m):
            break
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for fcol in free:
        v = [F(0)] * ncols
        v[fcol] = F(1)
        for i, pc in enumerate(piv):
            v[pc] = -m[i][fcol]
        den = reduce(lambda a, b: a * b // gcd(a, b), [x.denominator for x in v], 1)
        v = [x * den for x in v]
        g = reduce(gcd, [abs(int(x)) for x in v if x != 0], 0)
        v = [x / g for x in v]
        basis.append(v)
    return len(piv), basis


def vol_h(dims):
    rows = []
    ngroups = 0
    for i, (name, keys) in enumerate(PI_PROBLEMS):
        ks = [PI_ALIASES.get(k, k) for k in keys]
        cols = [dims[k] for k in ks]
        mat = [[cols[j][r] for j in range(len(ks))] for r in range(7)]
        rank, basis = nullspace(mat, len(ks))
        check(len(basis) == len(ks) - rank, "Pi theorem count")
        groups = []
        for v in basis:
            d = ZERO
            for j, e in enumerate(v):
                d = vadd(d, cols[j], e)
            check(d == ZERO, "group dimensionless")
            parts = []
            for j, e in enumerate(v):
                if e != 0:
                    sym = SI_KEYS[ks[j]][2]
                    if keys[j].endswith("_"):
                        sym = sym + "'"
                    parts.append(sym if e == 1 else "{%s}^{%s}" % (sym, fr(e)))
            groups.append("$" + "\\,".join(parts) + "$")
        ngroups += len(groups)
        vars_tex = ", ".join("$%s%s$" % (SI_KEYS[k][2], "'" if keys[j].endswith("_") else "")
                             for j, k in enumerate(ks))
        rows.append(["H.%02d" % (i + 1), name, vars_tex, str(len(ks)), str(rank), "; ".join(groups) if groups else "none"])
    SUMMARY["h_n"] = len(PI_PROBLEMS)
    SUMMARY["h_groups"] = ngroups
    tab = longtable("@{}lp{3.0cm}p{3.6cm}rrp{6.2cm}@{}", ["Id", "Problem", "Variables", "$k$", "rank",
                                                          "Independent dimensionless groups (computed)"], rows)
    write("tab_h.tex", tab)


def vol_i(dims):
    classes = {}
    for key, name, sym, rel, unit, dom in SI:
        classes.setdefault(dims[key], []).append(key)
    rows = []
    multi = [(d, ks) for d, ks in classes.items() if len(ks) > 1]
    multi.sort(key=lambda dk: (-len(dk[1]), [str(x) for x in dk[0]]))
    for i, (d, ks) in enumerate(multi):
        rows.append(["I.%02d" % (i + 1), dim_tex(d), str(len(ks)),
                     "; ".join("%s (%s)" % (SI_KEYS[k][1], "F.%03d" % (SI.index(SI_KEYS[k]) + 1)) for k in ks)])
    SUMMARY["i_classes"] = len(classes)
    SUMMARY["i_multi"] = len(multi)
    SUMMARY["i_in_multi"] = sum(len(ks) for d, ks in multi)
    tab = longtable("@{}llrp{11.6cm}@{}", ["Id", "Dimension", "$n$", "Quantities sharing it"], rows)
    write("tab_i.tex", tab)


# ---------------------------------------------------------------------------
# Volume K. The inventory and the verdicts.
# ---------------------------------------------------------------------------
# fields: id, candidate, kind ('q' quantity, 'r' relation, 'k' kind), Inv (invariant under the symmetries
# of the laws: 'Y', 'N' or 'F' = frame-relative but definable relative to a physical frame), Law (figures in the
# fundamental dynamical laws), Univ (determinates instantiated by two or more distinct objects), construction
# (list of ingredients, possibly empty for logical constructions, None if no construction), construction text,
# open question (None if none).
PARAMS = {"FRAME": "reference body (worldline congruence)", "NBHD": "projection along neighbouring-point relations",
          "COUNT": "numerical quantifier (logical)", "PERC": "relation to perceivers"}

K = [
    # spacetime
    ("K.01", "metric (infinitesimal interval)", "r", "Y", "Y", "Y", None, "", None),
    ("K.02", "interval between finitely separated events", "r", "Y", "N", "Y", ["K.01", "NBHD"],
     "extremal $\\int ds$ along connecting geodesics", None),
    ("K.03", "causal order of events", "r", "Y", "N", "Y", ["K.01", "K.04", "NBHD"],
     "future-directed non-spacelike curve exists", None),
    ("K.04", "time orientation", "q", "Y", "N", "Y", None, "", "is the direction of time genuine or constructed from entropy gradients?"),
    ("K.05", "proper time along a worldline", "q", "Y", "N", "Y", ["K.01", "NBHD"], "$\\int\\sqrt{g_{ab}\\dot x^a\\dot x^b}$ along the worldline", None),
    ("K.06", "spatial distance", "r", "F", "N", "Y", ["K.01", "FRAME"], "interval orthogonal to a frame's worldlines", None),
    ("K.07", "temporal duration", "r", "F", "N", "Y", ["K.01", "FRAME"], "proper time of a frame's worldline between its simultaneity slices", None),
    ("K.08", "distant simultaneity", "r", "F", "N", "Y", ["K.01", "FRAME"], "orthogonality to a frame's worldlines (Einstein synchrony)", None),
    ("K.09", "Christoffel symbols", "q", "N", "N", "Y", None, "", None),
    ("K.10", "Riemann curvature", "q", "Y", "Y", "Y", ["K.01", "NBHD"], "second derivatives of the metric", None),
    ("K.11", "Ricci curvature", "q", "Y", "Y", "Y", ["K.10"], "contraction $R^a{}_{bad}$", None),
    ("K.12", "Weyl curvature", "q", "Y", "N", "Y", ["K.10", "K.11", "K.01"], "trace-free part of $R_{abcd}$", None),
    ("K.13", "scalar curvature", "q", "Y", "N", "Y", ["K.11", "K.01"], "$g^{ab}R_{ab}$", None),
    ("K.14", "coordinate position", "q", "N", "N", "Y", None, "", None),
    # Lorentz representation labels and kinematics
    ("K.20", "spin (Casimir label $s$)", "q", "Y", "Y", "Y", None, "", None),
    ("K.21", "chirality (Weyl representation)", "q", "Y", "Y", "Y", None, "", None),
    ("K.22", "helicity", "q", "F", "N", "Y", ["K.20", "K.27"], "spin projected on momentum", None),
    ("K.23", "spin component along an axis", "q", "F", "N", "Y", ["K.20", "FRAME"], "projection on an axis fixed by a body", None),
    ("K.24", "invariant (rest) mass", "q", "Y", "Y", "Y", None, "", "Casimir label, or constructed from Yukawa coupling and Higgs vacuum value (K.46, K.45)?"),
    ("K.25", "four-momentum", "q", "Y", "N", "Y", ["K.24", "K.05", "NBHD"], "$m\\,dx^a/d\\tau$", None),
    ("K.26", "energy", "q", "F", "N", "Y", ["K.25", "FRAME"], "$p_a u^a$ for the frame velocity $u^a$", None),
    ("K.27", "three-momentum", "q", "F", "N", "Y", ["K.25", "FRAME"], "projection of $p^a$ orthogonal to $u^a$", None),
    ("K.28", "velocity", "r", "F", "N", "Y", ["K.06", "K.07", "NBHD"], "$d\\vec x/dt$ in a frame", None),
    ("K.29", "orbital angular momentum", "q", "F", "N", "Y", ["K.27", "K.06", "FRAME"], "$\\vec r\\times\\vec p$ about a chosen origin", None),
    # gauge structure
    ("K.30", "weak hypercharge $Y$", "q", "Y", "Y", "Y", None, "", None),
    ("K.31", "weak isospin multiplet $T$", "q", "Y", "Y", "Y", None, "", None),
    ("K.32", "colour representation", "q", "Y", "Y", "Y", None, "", None),
    ("K.33", "colour index (red, green, blue)", "q", "N", "N", "Y", None, "", None),
    ("K.34", "weak isospin component $T_3$", "q", "Y", "N", "Y", ["K.35", "K.30"], "$T_3 = Q - Y/2$, relative to the vacuum", None),
    ("K.35", "electric charge $Q$", "q", "Y", "Y", "Y", None, "", None),
    ("K.36", "electromagnetic field tensor $F_{ab}$", "q", "Y", "Y", "Y", None, "", None),
    ("K.37", "electric field $\\vec E$", "q", "F", "N", "Y", ["K.36", "FRAME"], "$F_{ab}u^b$", None),
    ("K.38", "magnetic field $\\vec B$", "q", "F", "N", "Y", ["K.36", "FRAME"], "dual of $F_{ab}$ contracted with $u^b$", None),
    ("K.39", "electromagnetic potential $A_a$", "q", "N", "Y", "Y", None, "", None),
    ("K.40", "electromagnetic holonomy (loop phase)", "r", "Y", "N", "Y", None, "", "genuine non-local relation, or constructed from $F_{ab}$ where the region is simply connected?"),
    ("K.41", "non-abelian field strengths (components)", "q", "N", "Y", "Y", None, "", None),
    ("K.42", "non-abelian holonomies (Wilson loops)", "r", "Y", "N", "Y", None, "", "are gauge-invariant loop quantities the genuine content of $SU(2)$ and $SU(3)$ fields?"),
    ("K.43", "Higgs field components", "q", "N", "Y", "Y", None, "", None),
    ("K.44", "hypercharge field strength $B_{ab}$", "q", "Y", "Y", "Y", None, "", None),
    ("K.45", "Higgs field magnitude $H^\\dagger H$", "q", "Y", "Y", "Y", None, "", "elementary or composite scalar sector?"),
    ("K.46", "Yukawa couplings", "r", "Y", "Y", "Y", None, "", "parameters of the best system, or genuine relations among fields?"),
    ("K.47", "gauge couplings", "r", "Y", "Y", "Y", None, "", "values run with the energy scale; scale-relative?"),
    ("K.48", "generation (family)", "q", "Y", "N", "Y", ["K.24", "K.46"], "ordering by mass within an indiscernibility class", None),
    ("K.49", "baryon number $B$", "q", "Y", "N", "Y", ["K.32", "K.20", "COUNT"], "$(n_{\\mathbf 3}-n_{\\bar{\\mathbf 3}})/3$ over spin-1/2 fields", None),
    ("K.50", "lepton number $L$", "q", "Y", "N", "Y", ["K.32", "K.20", "K.30", "COUNT"], "count of colourless spin-1/2 fields, sign by $Y$", None),
    ("K.51", "$B-L$", "q", "Y", "N", "Y", ["K.49", "K.50"], "difference", None),
    ("K.52", "flavour numbers $S, C, B', T$", "q", "Y", "N", "Y", ["K.48", "K.35", "K.32", "COUNT"], "counts of quarks by generation and charge", None),
    ("K.53", "strong isospin $I_3$", "q", "Y", "N", "Y", ["K.34", "K.48", "COUNT"], "$(n_u-n_d)/2$ with antiquarks subtracted", None),
    ("K.54", "intrinsic parity", "q", "Y", "N", "Y", None, "", "convention-laden, and parity is violated by the weak interaction"),
    ("K.55", "quark and lepton mixing", "r", "Y", "Y", "Y", None, "", "derived from Yukawa matrices (K.46)?"),
    ("K.56", "neutrino mass", "q", "Y", "Y", "Y", None, "", "Dirac or Majorana?"),
    ("K.57", "right-handed neutrino charges", "q", "Y", "N", "N", None, "", "existence of $\\nu_R$ unknown"),
    ("K.58", "graviton (spin-2 quantum)", "q", "Y", "N", "N", None, "", "no established quantum theory of gravity"),
    ("K.60", "cosmological constant", "r", "Y", "Y", "Y", None, "", "constant of law, or vacuum energy?"),
    # derived and macroscopic
    ("K.61", "temperature", "q", "F", "N", "Y", ["K.26", "K.62"], "$1/T = \\partial S/\\partial E$ in the rest frame", None),
    ("K.62", "entropy", "q", "Y", "N", "Y", ["K.26", "COUNT"], "$k\\ln W$, counting microstates in an energy shell", None),
    ("K.63", "pressure", "q", "F", "N", "Y", ["K.27", "K.06", "K.07"], "momentum flux per area", None),
    ("K.64", "atomic number (chemical element)", "q", "Y", "N", "Y", ["K.35", "K.49", "COUNT"], "number of protons in the nucleus", None),
    ("K.65", "shape (e.g.\\ cubical)", "q", "Y", "N", "Y", ["K.06", "NBHD"], "arrangement of parts", None),
    ("K.66", "perceived colour (e.g.\\ red)", "q", "Y", "N", "Y", ["K.36", "NBHD", "PERC"], "surface reflectance and perceiver response", None),
    ("K.67", "luminous intensity", "q", "F", "N", "Y", ["K.26", "K.07", "PERC"], "radiant power weighted by human spectral sensitivity", None),
    ("K.68", "amount of substance", "q", "Y", "N", "Y", ["COUNT"], "number of entities divided by $N_A$", None),
    ("K.68b", "number of entities", "q", "Y", "N", "Y", ["COUNT"], "numerical quantifier over a kind", None),
    ("K.69", "electric current", "q", "F", "N", "Y", ["K.35", "K.07", "K.06", "COUNT"], "charge crossing a surface per unit time", None),
    ("K.70", "magnetic moment of a particle", "q", "Y", "N", "Y", ["K.20", "K.35", "K.24"], "$g\\,(Q/2m)\\,\\vec S$", None),
    ("K.71", "colour singlet (hadron)", "q", "Y", "N", "Y", ["K.32", "COUNT"], "invariant contraction of constituents", None),
    ("K.72", "existence", "q", "Y", "N", "Y", [], "empty conjunction", None),
    ("K.73", "self-identity", "r", "Y", "N", "Y", [], "logical (permutation invariant)", None),
    ("K.74", "grue", "q", "F", "N", "Y", ["K.66", "K.07", "FRAME"], "green and examined before $t_0$, or blue and not", None),
    ("K.75", "solubility (a disposition)", "q", "Y", "N", "Y", ["K.35", "K.36", "K.24", "NBHD"], "supervenient on constituents' charges, masses and fields", None),
    ("K.81", "being an electron", "k", "Y", "N", "Y", ["K.20", "K.35", "K.31", "K.30", "K.32", "K.24"], "conjunction of determinates (A.3.07)", None),
    ("K.82", "being a proton", "k", "Y", "N", "Y", ["K.49", "K.35", "K.20", "K.71"], "colour singlet $uud$ (D.02) of spin 1/2", None),
    ("K.83", "rest mass of a composite", "q", "Y", "N", "Y", ["K.25", "NBHD"], "invariant norm of total four-momentum", None),
    ("K.84", "stress-energy tensor", "q", "Y", "Y", "Y", ["K.25", "K.36", "NBHD"], "sum of matter and field contributions", None),
]


def vol_k():
    ids = [r[0] for r in K]
    check(len(ids) == len(set(ids)), "unique inventory ids")
    byid = {r[0]: r for r in K}
    verd = {}

    def verdict(r):
        kid, name, kind, inv, law, univ, cons, ctext, open_ = r
        if open_ is not None:
            return "provisional"
        if cons is not None:
            return "constructed"
        if inv == "N":
            return "non-qualitative"
        check(inv == "Y" and law == "Y" and univ == "Y", "genuine entries satisfy all criteria: %s" % kid)
        return "genuine"
    for r in K:
        verd[r[0]] = verdict(r)
    # constructions: ingredients exist, are acyclic, never non-qualitative
    support = {}
    depth = {}
    state = {}

    def visit(kid):
        if kid in PARAMS:
            return {kid}, 0
        if state.get(kid) == "done":
            return support[kid], depth[kid]
        check(state.get(kid) != "active", "acyclic construction graph at %s" % kid)
        state[kid] = "active"
        r = byid[kid]
        cons = r[6]
        v = verd[kid]
        if v in ("genuine", "provisional") or cons is None:
            s, d = {kid}, 0
        else:
            s, d = set(), 0
            for ing in cons:
                check(ing in byid or ing in PARAMS, "ingredient %s of %s exists" % (ing, kid))
                if ing in byid:
                    check(verd[ing] != "non-qualitative", "construction %s avoids non-qualitative %s" % (kid, ing))
                s2, d2 = visit(ing)
                s |= s2
                d = max(d, d2 + 1)
        support[kid], depth[kid] = s, d
        state[kid] = "done"
        return s, d
    for r in K:
        visit(r[0])
    for kid in ids:
        if verd[kid] == "constructed":
            for s in support[kid]:
                check(s in PARAMS or verd[s] in ("genuine", "provisional"), "support of %s is basic" % kid)
    rows = []
    out = {}
    for r in K:
        kid, name, kind, inv, law, univ, cons, ctext, open_ = r
        v = verd[kid]
        out[kid] = {"verdict": v, "support": support[kid]}
        if v == "constructed":
            how = ctext + (" [" + ", ".join(cons) + "]" if cons else "")
        elif v == "provisional":
            how = "open: " + open_
        elif v == "non-qualitative":
            how = "gauge- or coordinate-relative; no physical relatum"
        else:
            how = "--"
        sup = support_tex(support[kid]) if v == "constructed" else "--"
        rows.append([kid, name, {"q": "qty", "r": "rel", "k": "kind"}[kind], inv, law, univ,
                     {"genuine": "\\textbf{genuine}", "constructed": "constructed", "provisional": "\\emph{provisional}",
                      "non-qualitative": "non-qual."}[v], how, sup, str(depth[kid]) if v == "constructed" else "--"])
    counts = {}
    for v in verd.values():
        counts[v] = counts.get(v, 0) + 1
    SUMMARY["k_n"] = len(K)
    SUMMARY["k_counts"] = counts
    SUMMARY["k_genuine"] = [k for k in ids if verd[k] == "genuine"]
    SUMMARY["k_frame"] = [k for k in ids if verd[k] == "constructed" and "FRAME" in support[k]]
    SUMMARY["k_maxdepth"] = max(depth[k] for k in ids if verd[k] == "constructed")
    tab = longtable("@{}p{0.75cm}p{2.9cm}llllp{1.45cm}p{4.6cm}p{1.9cm}r@{}",
                    ["Id", "Candidate", "Type", "Inv", "Law", "Univ", "Verdict", "Construction or reason",
                     "Support", "Dp"], rows, sep="2.5pt")
    write("tab_k.tex", tab)
    return out


# ---------------------------------------------------------------------------
# Volume J. Determinables and determinates.
# ---------------------------------------------------------------------------

def vol_j(states, kverd):
    Qs = sorted({s["Q"] for s in states if s["st"] == "established"})
    Ys = sorted({s["Y"] for s in states if s["st"] == "established"} | {F(0), F(1), F(-1)})
    Bs = sorted({s["B"] for s in states})
    Ls = sorted({s["L"] for s in states})
    lst = lambda xs: ", ".join(fr(x) for x in xs)
    J = [
        ("electric charge", "K.35", lst(Qs) + " (elementary states, A.2); " + lst(SUMMARY["d_qb"]) + " (baryons, D)",
         "discrete, ordered, additive, conserved"),
        ("weak hypercharge", "K.30", lst(Ys), "discrete, additive"),
        ("weak isospin multiplet", "K.31", "0, 1/2, 1", "representation labels"),
        ("colour representation", "K.32", "$\\mathbf 1,\\mathbf 3,\\bar{\\mathbf 3},\\mathbf 8$", "representation labels; triality additive mod 3"),
        ("spin", "K.20", "0, 1/2, 1 (elementary); 3/2 and higher (composite)", "discrete, half-integer"),
        ("chirality", "K.21", "left-handed $(\\frac12,0)$, right-handed $(0,\\frac12)$", "two-valued"),
        ("metric interval", "K.01", "real values; classes timelike / null / spacelike (E.2)", "continuous, signed"),
        ("invariant mass", "K.24", "non-negative reals", "continuous, ordered, not additive for composites"),
        ("baryon number", "K.49", lst(Bs) + " (elementary)", "additive, conserved at $d\\le 4$"),
        ("lepton number", "K.50", lst(Ls) + " (elementary)", "additive, conserved at $d\\le 4$"),
        ("$B-L$", "K.51", "integer multiples of 1/3", "additive; anomaly-free (B.2)"),
        ("generation", "K.48", "1, 2, 3", "ordinal"),
        ("helicity", "K.22", "$\\pm s$ for massless particles; frame-relative otherwise", "discrete"),
        ("spatial distance", "K.06", "non-negative reals (per frame)", "continuous, metric"),
        ("temporal duration", "K.07", "non-negative reals (per frame)", "continuous"),
        ("energy", "K.26", "reals (per frame)", "additive, conserved"),
        ("velocity", "K.28", "vectors of magnitude $<c$ (per frame)", "relativistic composition"),
        ("temperature", "K.61", "positive reals", "ordered, intensive"),
        ("entropy", "K.62", "non-negative reals", "additive for independent systems"),
        ("pressure", "K.63", "reals", "intensive"),
        ("perceived colour", "K.66", "red, orange, yellow, green, blue, violet, \\dots", "hue circle; resemblance ordering"),
        ("shape", "K.65", "cubical, spherical, \\dots", "structural"),
        ("atomic number", "K.64", "positive integers", "discrete"),
        ("electromagnetic field", "K.36", "antisymmetric tensors at each point", "linear, superposable"),
        ("electric field", "K.37", "vectors (per frame)", "linear, frame-relative"),
        ("Riemann curvature", "K.10", "tensors with the symmetries of $R_{abcd}$ (E.1)", "linear"),
        ("intrinsic parity", "K.54", "$\\pm 1$", "multiplicative"),
        ("Yukawa coupling", "K.46", "complex matrices in generation space", "continuous"),
    ]
    rows = []
    for i, (name, kid, dets, struct) in enumerate(J):
        v = kverd[kid]["verdict"]
        rows.append(["J.%02d" % (i + 1), name, dets, struct, kid, v, "disjunction of determinates"])
    SUMMARY["j_n"] = len(J)
    tab = longtable("@{}lp{2.3cm}p{4.5cm}p{2.9cm}lp{1.6cm}p{1.7cm}@{}",
                    ["Id", "Determinable", "Determinates", "Structure", "Entry", "Determinates are",
                     "Determinable is"], rows)
    write("tab_j.tex", tab)


def main():
    states, kinds = vol_a()
    vol_b()
    vol_c()
    vol_d()
    vol_e()
    kverd = vol_k()
    dims = si_dims()
    vol_f(dims, kverd)
    vol_g(dims)
    vol_h(dims)
    vol_i(dims)
    vol_j(states, kverd)
    # summary macros
    S = SUMMARY
    lines = ["% generated by gen/generate.py; do not edit"]

    def mac(name, val):
        lines.append("\\newcommand{\\vv%s}{%s}" % (name, val))
    mac("NChecks", "{:,}".format(CHECKS["n"]).replace(",", "{,}"))
    mac("NQcheck", S["nQcheck"])
    mac("NKinds", S["nkinds"])
    mac("NFermClasses", S["nfermclasses"])
    mac("NBthreeSpace", "{:,}".format(S["b3space"]).replace(",", "{,}"))
    mac("NBthree", S["b3n"])
    mac("NBthreeSM", S["b3sm"])
    mac("NBfourSpace", "{:,}".format(S["b4space"]).replace(",", "{,}"))
    mac("NBfour", S["b4n"])
    mac("NBfourLin", S["b4lin"])
    mac("NCtested", "{:,}".format(S["c_tested"]).replace(",", "{,}"))
    mac("NCfound", S["c_found"])
    mac("NCreps", S["c_reps"])
    mac("DmaxC", DMAX_C)
    mac("NDbaryons", S["d_baryons"])
    mac("NDmesons", S["d_mesons"])
    mac("NDtwo", S["d2_n"])
    mac("NDtwoHidden", S["d2_hidden"])
    mac("NDtwoQtetra", ", ".join("$%s$" % fr(x) for x in S["d2_q"]["tetra"]))
    mac("NDtwoQpenta", ", ".join("$%s$" % fr(x) for x in S["d2_q"]["penta"]))
    mac("NErows", S["e_rows"])
    mac("NEtime", S["e_cls"]["timelike"])
    mac("NEnull", S["e_cls"]["null"])
    mac("NEspace", S["e_cls"]["spacelike"])
    mac("NEboostchecks", "{:,}".format(S["e_boostchecks"]).replace(",", "{,}"))
    mac("NEboosts", S["e_nboosts"])
    mac("NF", S["f_n"])
    mac("NFcons", S["f_cons"])
    mac("NFgenuine", len(S["f_genuine"]))
    mac("NFprov", len(S["f_prov"]))
    mac("NG", S["g_n"])
    mac("NGterms", S["g_terms"])
    mac("NGbad", S["g_bad"])
    mac("NH", S["h_n"])
    mac("NHgroups", S["h_groups"])
    mac("NIclasses", S["i_classes"])
    mac("NImulti", S["i_multi"])
    mac("NIinmulti", S["i_in_multi"])
    mac("NJ", S["j_n"])
    mac("NK", S["k_n"])
    for v, nm in (("genuine", "NKgenuine"), ("constructed", "NKconstructed"), ("provisional", "NKprovisional"),
                  ("non-qualitative", "NKnonqual")):
        mac(nm, S["k_counts"].get(v, 0))
    mac("NKframe", len(S["k_frame"]))
    mac("NKmaxdepth", S["k_maxdepth"])
    mac("KGenuineList", ", ".join(S["k_genuine"]))
    write("summary.tex", "\n".join(lines) + "\n")
    # print a short report
    for k, v in sorted(S.items()):
        print(k, v)
    print("checks", CHECKS["n"])


if __name__ == "__main__":
    main()
