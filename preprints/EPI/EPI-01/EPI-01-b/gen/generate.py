#!/usr/bin/env python3
"""Generator for EPI-01-b, "A Classification of Gettier Cases".

Reads the hand-curated case table in cases.py, computes for every case model
and every systematic variant the verdicts of the analysis of EPI-01-a
(justified, true, safe, knowledge, Gettier case), its class in the typology,
its safety profile across closeness thresholds, and the verdicts of four rival
fourth conditions; checks the theorems of the manuscript on every row
(assert); and writes the LaTeX tables included by ../main.tex.

Python 3 standard library only; deterministic output.
"""
import os
from collections import Counter, OrderedDict
from cases import CASES, W

HERE = os.path.dirname(os.path.abspath(__file__))
THETAS = range(0, 5)
REMOTE = 4

SRC_LABEL = {
    "Gettier1963": r"\citet{Gettier1963}", "Lehrer1965": r"\citet{Lehrer1965}",
    "Feldman1974": r"\citet{Feldman1974}", "Russell1948": r"\citet{Russell1948}",
    "Goldman1976": r"\citet{Goldman1976}", "Kripke2011": r"\citet{Kripke2011}",
    "Chisholm1966": r"\citet{Chisholm1966}", "Zagzebski1994": r"\citet{Zagzebski1994}",
    "Skyrms1967": r"\citet{Skyrms1967}", "LehrerPaxson1969": r"\citet{LehrerPaxson1969}",
    "Harman1973": r"\citet{Harman1973}", "BonJour1980": r"\citet{BonJour1980}",
    "Lehrer1990": r"\citet{Lehrer1990}", "Sosa1999": r"\citet{Sosa1999}",
    "Sosa2007": r"\citet{Sosa2007}", "Pritchard2012": r"\citet{Pritchard2012}",
    "Lackey2007": r"\citet{Lackey2007}", "Hawthorne2004": r"\citet{Hawthorne2004}",
    "Williamson2000": r"\citet{Williamson2000}", "Dretske1970": r"\citet{Dretske1970}",
    "Nozick1981": r"\citet{Nozick1981}", "Comesana2005": r"\citet{Comesana2005}",
    "Bogardus2014": r"\citet{Bogardus2014}", "Warfield2005": r"\citet{Warfield2005}",
    "DeRose1992": r"\citet{DeRose1992}", "PlatoTht": r"Plato, \emph{Theaetetus}",
    "Vogel1987": r"\citet{Vogel1987}",
}

ROUTE_NAME = {"inf": "inference", "ind": "induction", "perc": "perception",
              "instr": "instrument", "test": "testimony", "stat": "statistics",
              "ded": "deduction", "calc": "calculation", "fac": "faculty"}

# ---------------------------------------------------------------- semantics

def close(m, theta):
    return [v for v in m["worlds"] if v.d <= theta]


def actual(m):
    # Centring (EPI-01-a, Assumption 2.1): the actual world, at distance 0.
    return W("actual", 0, 1, int(m["T"]), "act", m.get("qT"), None)


def safe_local(m, theta):
    """Definition 2.2 of EPI-01-a."""
    return all(v.p for v in [actual(m)] + close(m, theta) if v.b)


def safe_basis(m, theta):
    """Basis-wide safety: also no close world where the same basis yields a
    false belief in another proposition (the amendment of EPI-01-a, reply to
    the objection from necessary truths)."""
    return safe_local(m, theta) and all(v.alt is not False for v in close(m, theta))


def delta(m):
    """Error distance: least distance of a world where S believes on the
    basis and the belief (in p, or basis-wide) is false."""
    ds = [v.d for v in [actual(m)] + m["worlds"]
          if (v.b and not v.p) or v.alt is False]
    return min(ds) if ds else None


def verdicts(m, theta=None):
    th = m["theta"] if theta is None else theta
    J, T = m["J"], m["T"]
    sl, sb = safe_local(m, th), safe_basis(m, th)
    K = J and sb
    G = J and T and not sl            # Definition 2.4 of EPI-01-a
    Gp = J and T and not sb           # same, with basis-wide safety
    return dict(J=J, T=T, SL=sl, SB=sb, K=K, G=G, Gp=Gp)


def sensitive(m):
    """Nozick: in the nearest worlds where p is false, S does not believe p
    (on the same basis).  Vacuous if p is false in no encoded world."""
    fw = [v for v in [actual(m)] + m["worlds"] if not v.p]
    if not fw:
        return True
    dn = min(v.d for v in fw)
    return not any(v.b for v in fw if v.d == dn)


def rivals(m):
    jt = m["J"] and m["T"]
    return OrderedDict(
        NFL=jt and m["lemma"] is None,
        CAU=jt and m["causal"],
        SEN=jt and sensitive(m),
        UND=jt and m["defeater"] == "none",
        SAF=verdicts(m)["K"],
    )


PRIORITY = ["time", "draw", "marg", "src", "env", "tm"]


def falsifiers(m, theta):
    return [v for v in close(m, theta) if (v.b and not v.p)]


def classify(m):
    v = verdicts(m)
    th = m["theta"]
    if not v["J"]:
        return "U"
    if not v["T"]:
        return "F"
    if v["SB"]:
        fl = []
        if any(x.tag == "basis" for x in close(m, th)):
            fl.append("ev")
        if m["defeater"] == "misleading":
            fl.append("md")
        if not m["refl"]:
            fl.append("rf")
        if "content" in m["flags"]:
            fl.append("ct")
        if "fix" in m["flags"]:
            fl.append("fx")
        return "K" + ("[" + ",".join(fl) + "]" if fl else "")
    locus = "c" if m["causal"] else "d"
    if v["SL"]:
        return "G-nec/" + locus
    fs = falsifiers(m, th)
    dmin = min(x.d for x in fs)
    tags = {x.tag for x in fs if x.d == dmin}
    top = next(t for t in PRIORITY if t in tags)
    if top == "time":
        c = "G-tmp"
    elif top == "draw":
        c = "G-lot"
    elif top == "marg":
        c = "G-mrg"
    elif top == "src":
        c = "G-tst"
    elif top == "env":
        c = "G-env"
    elif m["route"] in ("inf", "ind", "ded"):
        c = "G-fl" if m["lemma"] else "G-nfl"
    else:
        c = "G-int"
    return c + "/" + locus


def profile(m):
    return "".join("S" if safe_basis(m, t) else "u" for t in THETAS)


# ---------------------------------------------------------------- variants

def clone(m, **k):
    n = dict(m)
    n["worlds"] = list(m["worlds"])
    n.update(k)
    return n


def mk(parent, op, note, **k):
    n = clone(parent, **k)
    n["id"] = parent["id"] + "." + op
    n["op"] = op
    n["note"] = note
    n["parent"] = parent["id"]
    n["lit"] = None
    n["dispute"] = None
    return n


def variants(m):
    out = []
    th = m["theta"]
    fals_any = [v for v in m["worlds"] if v.b and not v.p]
    if m["lemma"]:
        out.append(mk(m, "nfl", "false lemma removed; same evidence, true intermediates", lemma=None))
    elif m["route"] in ("inf", "ind", "ded"):
        out.append(mk(m, "fl", "a false intermediate belief added to the route", lemma="added"))
    if m["T"] and any(v.tag in ("tm", "draw", "time") for v in fals_any):
        ws = [v._replace(b=0) if (v.b and not v.p and v.tag in ("tm", "draw", "time")) else v
              for v in m["worlds"]]
        out.append(mk(m, "sec", "truth-maker secured: the basis now bears on it", worlds=ws, causal=True))
    if any(v.tag in ("env", "src") for v in fals_any):
        ws = [v for v in m["worlds"] if not (v.tag in ("env", "src") and v.b and not v.p)]
        out.append(mk(m, "nor", "environment made normal: look-alikes and bad sources removed", worlds=ws))
    if m["route"] in ("perc", "instr", "test") and not any(
            v.tag in ("env", "src") and v.b and not v.p and v.d <= th for v in m["worlds"]):
        ws = m["worlds"] + [W("a look-alike or bad source nearby", 1, 1, 0, "env", 0 if m.get("q") else None, None)]
        out.append(mk(m, "hos", "hostile environment: a look-alike is placed nearby", worlds=ws))
    if m["T"] and not safe_basis(m, th):
        ws = [v._replace(d=REMOTE) if ((v.b and not v.p) or v.alt is False) else v for v in m["worlds"]]
        out.append(mk(m, "rem", "every error world moved to distance 4", worlds=ws))
    if m["T"]:
        out.append(mk(m, "fal", "the belief made false at the actual world", T=False, qT=m.get("qT")))
    if m["J"]:
        out.append(mk(m, "unj", "justification removed", J=False))
    if m["T"]:
        out.append(mk(m, "rel", "a hearer believes on the subject's sincere testimony",
                      route="test", lemma=m["lemma"]))
        ws = m["worlds"] + [W("the speaker would assert it falsely", 1, 1, 0, "src", None, None)]
        out.append(mk(m, "lie", "relay from a speaker who could easily have lied", route="test",
                      worlds=ws, defeater="genuine" if m["defeater"] == "none" else m["defeater"]))
    if m.get("q"):
        ws = [v._replace(p=v.q) for v in m["worlds"]]
        out.append(mk(m, "ded", "competent deduction of the weaker $q$", worlds=ws, T=m["qT"],
                      route="ded", p=m["q"], lemma=m["lemma"]))
    return out


# ---------------------------------------------------------------- checks

def check_model(m):
    for x in m["worlds"]:
        assert not (x.b and not x.p) or x.tag in PRIORITY, (m["id"], x)
    v = verdicts(m)
    th = m["theta"]
    # Theorem 3.1 of EPI-01-a: safety entails truth (centring).
    assert not v["SL"] or v["T"]
    # Characterization (Thm 3.3 / Cor 3.4 of EPI-01-a), basis-wide form.
    if v["J"] and v["T"]:
        assert v["K"] == (not v["Gp"])
    # Lemma 2.5: safe iff error distance exceeds threshold.
    d = delta(m)
    assert v["SB"] == (d is None or d > th), m["id"]
    # Monotonicity in theta (Proposition 4.10).
    pr = profile(m)
    assert "uS" not in pr, m["id"]
    # Veritic luck coincides with unsafety for true beliefs (Proposition 4.1).
    if v["T"]:
        veritic = bool(falsifiers(m, th)) or any(x.alt is False for x in close(m, th))
        assert veritic == (not v["SB"])
    # Necessary content: no Gettier case under Definition 2.4 (Proposition 4.7).
    if m["route"] == "calc":
        assert not v["G"]
    c = classify(m)
    assert c.startswith("G") == bool(v["Gp"]), m["id"]
    assert c.startswith("K") == bool(v["K"]), m["id"]
    return v


def check_variant(parent, n):
    vp, vn = verdicts(parent), verdicts(n)
    op = n["op"]
    th = parent["theta"]
    if op in ("nfl", "fl"):                       # Proposition 4.3
        assert vp["SB"] == vn["SB"] and vp["Gp"] == vn["Gp"]
        return "safety unchanged"
    if op == "sec":                               # Proposition 4.4
        rest = {x.tag for x in falsifiers(parent, th)} - {"tm", "draw", "time"}
        if not rest and all(x.alt is not False for x in close(parent, th)):
            assert vn["SB"]
            return "safe"
        return "safe iff no other error" if vn["SB"] else "other error remains"
    if op == "nor":                               # Proposition 4.4
        rest = {x.tag for x in falsifiers(parent, th)} - {"env", "src"}
        if not rest:
            assert vn["SB"]
            return "safe"
        return "other error remains"
    if op == "hos":                               # Proposition 4.4
        assert not vn["SB"]
        if vn["J"] and vn["T"] and vp["SB"]:
            assert classify(n).startswith("G-env")
        return "unsafe"
    if op == "rem":                               # Proposition 4.10
        assert profile(n)[:REMOTE] == "S" * REMOTE and profile(n)[REMOTE] == "u"
        return "safe below 4"
    if op == "fal":
        assert not vn["G"] and classify(n) in ("F", "U")
        return "not Gettier"
    if op == "unj":
        assert not vn["K"] and classify(n) == "U"
        return "not knowledge"
    if op == "rel":                               # Proposition 4.8
        assert vn["SB"] == vp["SB"]
        return "safety transmitted"
    if op == "lie":                               # Proposition 4.8
        assert not vn["SB"]
        return "unsafe"
    if op == "ded":                               # Prop. 6.1 of EPI-01-a
        if vp["SB"]:
            assert vn["SB"]
            return "safe (closure)"
        return "safe" if vn["SB"] else "unsafe"
    raise ValueError(op)


# ---------------------------------------------------------------- exhaustive census

def census():
    """All case models with at most two non-actual worlds, over the stated
    feature space; every theorem is checked on every model at every theta."""
    opts = []
    for d in range(1, 5):
        opts.append((d, 1, 1, "ok"))
        for t in PRIORITY:
            opts.append((d, 1, 0, t))
        opts.append((d, 0, 1, "basis"))
        opts.append((d, 0, 0, "ok"))
    configs = [[]] + [[o] for o in opts] + [[o1, o2] for o1 in opts for o2 in opts]
    feats = []
    for route, lemma in (("inf", "L"), ("inf", None), ("perc", None), ("test", None)):
        for causal in (False, True):
            for J in (False, True):
                for T in (False, True):
                    feats.append((route, lemma, causal, J, T))
    cnt = Counter()
    checks = 0
    nmodels = 0
    for cfg in configs:
        ws = [W("w%d" % i, d, b, p, t, None, None) for i, (d, b, p, t) in enumerate(cfg)]
        for route, lemma, causal, J, T in feats:
            m = dict(id="census", route=route, lemma=lemma, causal=causal, J=J, T=T,
                     refl=True, defeater="none", flags=(), theta=2, worlds=ws, q=None, qT=None)
            nmodels += 1
            for th in THETAS:
                m["theta"] = th
                check_model(m)
                checks += 1
                c = classify(m)
                if th == 2:
                    cnt[c.split("/")[0].split("[")[0]] += 1
                # Proposition 4.3: lemma toggling
                if route == "inf":
                    m2 = dict(m, lemma=None if lemma else "L")
                    assert verdicts(m2)["SB"] == verdicts(m)["SB"]
                    checks += 1
                # Proposition 4.4(c): hostile environment
                if route in ("perc", "test"):
                    m3 = dict(m, worlds=ws + [W("x", 1, 1, 0, "env", None, None)])
                    if th >= 1:
                        assert not verdicts(m3)["SB"]
                        if J and T and verdicts(m)["SB"]:
                            assert classify(m3).startswith("G-env")
                    checks += 1
            m["theta"] = 2
    return nmodels, checks, cnt, len(configs)


# ---------------------------------------------------------------- output

def yn(b):
    return "yes" if b else "no"


def tf(b):
    return r"\textsf{+}" if b else r"\textsf{--}"


def src_of(m):
    if m["src"] is None:
        return "schematic"
    return SRC_LABEL[m["src"]] + (", " + m["srcnote"] if m["srcnote"] else "")


def world_rows(m):
    rows = []
    q = bool(m.get("q"))
    for v in [actual(m)] + m["worlds"]:
        lab = "actual world" if v.tag == "act" else v.label
        closev = v.d <= m["theta"]
        cells = [lab, str(v.d), yn(closev), yn(v.b), yn(v.p), v.tag]
        if q:
            cells.append("--" if v.q is None else yn(v.q))
        if any(x.alt is not None for x in m["worlds"]):
            cells.append("--" if v.alt is None else yn(v.alt))
        rows.append(cells)
    return rows


def write_catalogue(models):
    L = []
    for m in models:
        v = verdicts(m)
        c = classify(m)
        hasq = bool(m.get("q"))
        hasalt = any(x.alt is not None for x in m["worlds"])
        L.append(r"\needspace{12\baselineskip}")
        L.append(r"\subsection*{%s \enspace %s}" % (m["id"], m["name"]))
        L.append(r"\addcontentsline{toc}{subsection}{%s %s}" % (m["id"], m["name"]))
        L.append(r"\noindent\textit{Source.} %s.\quad \textit{Route:} %s.\quad \textit{Basis:} %s.\par" %
                 (src_of(m), ROUTE_NAME[m["route"]], m["basis"]))
        L.append(r"\noindent\textit{Case.} %s\par" % m["desc"])
        L.append(r"\noindent\textit{Belief} $p$: %s." % m["p"])
        if hasq:
            L.append(r" \textit{Weaker} $q$: %s." % m["q"])
        L.append(r" \textit{False lemma:} %s. \textit{Causal connection:} %s. \textit{Defeater:} %s. "
                 r"\textit{Reflective access:} %s. \textit{Threshold} $\theta = %d$.\par" %
                 (m["lemma"] if m["lemma"] else "none", yn(m["causal"]), m["defeater"],
                  yn(m["refl"]), m["theta"]))
        cols = "@{}p{0.43\\linewidth}rcccl" + ("c" if hasq else "") + ("c" if hasalt else "") + "@{}"
        L.append(r"\begin{center}\begin{tabular}{%s}" % cols)
        hdr = [r"world", r"$d$", r"close", r"$B$", r"$p$", r"tag"]
        if hasq:
            hdr.append(r"$q$")
        if hasalt:
            hdr.append(r"alt")
        L.append(" & ".join(hdr) + r" \\ \midrule")
        for r in world_rows(m):
            L.append(" & ".join(r) + r" \\")
        L.append(r"\end{tabular}\end{center}")
        d = delta(m)
        L.append(r"\noindent\textit{Computed.} J %s, T %s, error distance $\delta = %s$, "
                 r"locally safe %s, safe basis-wide %s, Gettier case %s, knowledge %s. "
                 r"Profile over $\theta = 0..4$: \texttt{%s}. Class: \textbf{%s}." %
                 (yn(v["J"]), yn(v["T"]), "\\infty" if d is None else d, yn(v["SL"]), yn(v["SB"]),
                  yn(v["Gp"]), yn(v["K"]), profile(m), c))
        if m["lit"]:
            agree = (m["lit"] == "K") == v["K"]
            L.append(r" \textit{Source verdict:} %s (%s). Agreement: %s." %
                     ("knowledge" if m["lit"] == "K" else "not knowledge",
                      {"G": "presented as a Gettier case", "S": "presented against a fourth condition",
                       "O": "other"}[m["role"]], yn(agree)))
        if m["dispute"]:
            L.append(r" \textit{Dispute (%s):} %s" % (m["dispute"][0], m["dispute"][1]))
        L.append(r"\par\medskip")
    open(os.path.join(HERE, "catalogue.tex"), "w").write("\n".join(L) + "\n")


def write_variants(rows):
    L = [r"{\scriptsize\setlength{\tabcolsep}{2.5pt}",
         r"\begin{longtable}{@{}lp{0.36\linewidth}cccccll@{}}",
         r"\toprule",
         r"Id & Operation & J & T & $\delta$ & Safe & K & Class (parent $\to$ variant) & Prediction \\",
         r"\midrule\endhead", r"\bottomrule\endfoot"]
    last = None
    for parent, n, pred in rows:
        if last and last != parent["id"]:
            L.append(r"\midrule")
        last = parent["id"]
        v = verdicts(n)
        d = delta(n)
        cp, cn = classify(parent), classify(n)
        L.append(" & ".join([n["id"], n["note"], tf(v["J"]), tf(v["T"]),
                             "$\\infty$" if d is None else str(d), tf(v["SB"]), tf(v["K"]),
                             (cp + r" $\to$ " + cn) if cp != cn else cn + " (same)",
                             pred + r" \checkmark"]) + r" \\")
    L += [r"\end{longtable}}"]
    open(os.path.join(HERE, "variants.tex"), "w").write("\n".join(L) + "\n")


def write_profiles(models):
    L = [r"{\scriptsize\setlength{\tabcolsep}{3pt}",
         r"\begin{longtable}{@{}llcccccccccl@{}}",
         r"\toprule",
         r"Id & Route & $\theta$ & $\delta$ & Profile & NFL & CAU & SEN & UND & SAF & Lit. & Class \\",
         r"\midrule\endhead", r"\bottomrule\endfoot"]
    for m in models:
        r = rivals(m)
        d = delta(m)
        lit = m["lit"] or "--"
        L.append(" & ".join([m["id"], ROUTE_NAME[m["route"]][:5], str(m["theta"]),
                             "$\\infty$" if d is None else str(d), r"\texttt{%s}" % profile(m)] +
                            [tf(x) for x in r.values()] + [lit, classify(m)]) + r" \\")
    L += [r"\end{longtable}}"]
    open(os.path.join(HERE, "profiles.tex"), "w").write("\n".join(L) + "\n")


def main():
    sources = [dict(m) for m in CASES]
    for m in sources:
        m.setdefault("op", None)
    ids = [m["id"] for m in sources]
    assert len(ids) == len(set(ids))
    for m in sources:
        check_model(m)
    vrows = []
    allv = []
    for m in sources:
        for n in variants(m):
            check_model(n)
            pred = check_variant(m, n)
            vrows.append((m, n, pred))
            allv.append(n)
    models = sources + allv

    # ---- the mechanical check against the literature
    lit_rows = [m for m in sources if m["lit"]]
    G_rows = [m for m in lit_rows if m["role"] == "G"]
    for m in G_rows:
        v = verdicts(m)
        assert v["J"] and v["T"] and v["Gp"], m["id"]
    agree, depart = [], []
    for m in lit_rows:
        v = verdicts(m)
        (agree if ((m["lit"] == "K") == v["K"]) else depart).append(m)
    for m in depart:
        assert m["dispute"] and m["dispute"][0] in ("dep", "bas"), m["id"]
    # coincidence in undisputed rows
    undisputed = [m for m in lit_rows if not (m["dispute"] and m["dispute"][0] in ("dep", "bas"))]
    for m in undisputed:
        v = verdicts(m)
        if v["J"] and v["T"]:
            assert (m["lit"] == "N") == v["Gp"], m["id"]

    # ---- rival accuracy
    racc = OrderedDict((k, [0, 0]) for k in ["NFL", "CAU", "SEN", "UND", "SAF"])
    for m in undisputed:
        r = rivals(m)
        for k, val in r.items():
            racc[k][0] += (val == (m["lit"] == "K"))
            racc[k][1] += 1
    vagree = OrderedDict((k, 0) for k in ["NFL", "CAU", "SEN", "UND"])
    for n in allv:
        r = rivals(n)
        for k in vagree:
            vagree[k] += (r[k] == r["SAF"])

    # ---- typology incidence
    def base(c):
        return c.split("/")[0].split("[")[0]
    cls_src = Counter(base(classify(m)) for m in sources)
    cls_all = Counter(base(classify(m)) for m in models)
    wit = {}
    for m in models:
        wit.setdefault(base(classify(m)), []).append(m["id"])
    order = ["G-fl", "G-nfl", "G-int", "G-env", "G-tmp", "G-lot", "G-tst", "G-mrg", "G-nec", "K", "U", "F"]
    for c in cls_all:
        assert c in order, c
    routes = ["inf", "ind", "perc", "instr", "test", "stat", "ded", "calc", "fac"]
    gclasses = [c for c in order if c.startswith("G")]
    mat = {(c, r): 0 for c in gclasses for r in routes}
    for m in models:
        c = base(classify(m))
        if c.startswith("G"):
            mat[(c, m["route"])] += 1
    loci = Counter()
    for m in models:
        c = classify(m)
        if c.startswith("G"):
            loci[c.split("/")[1]] += 1
    # causal condition vs safety: four combinations among JT models
    combos = Counter()
    combo_wit = {}
    for m in models:
        v = verdicts(m)
        if v["J"] and v["T"]:
            key = (bool(m["causal"]), bool(v["SB"]))
            combos[key] += 1
            combo_wit.setdefault(key, []).append(m["id"])
    assert all(combos[k] > 0 for k in [(True, True), (True, False), (False, True), (False, False)])
    # false lemma vs safety among JT models
    lcombo = Counter()
    lwit = {}
    for m in models:
        v = verdicts(m)
        if v["J"] and v["T"]:
            key = (m["lemma"] is not None, bool(v["SB"]))
            lcombo[key] += 1
            lwit.setdefault(key, []).append(m["id"])
    assert all(lcombo[k] > 0 for k in [(True, True), (True, False), (False, True), (False, False)])
    # evidential luck independent of safety
    ev = Counter()
    for m in models:
        v = verdicts(m)
        if v["J"] and v["T"]:
            e = any(x.tag == "basis" for x in close(m, m["theta"]))
            ev[(e, bool(v["SB"]))] += 1

    cn_models, cn_checks, cn_cnt, cn_cfg = census()
    order0 = ["G-fl", "G-nfl", "G-int", "G-env", "G-tmp", "G-lot", "G-tst", "G-mrg", "G-nec", "K", "U", "F"]
    E = [r"\begin{center}\small", r"\begin{tabular}{@{}lr@{}}\toprule", r"Class at $\theta = 2$ & Models \\ \midrule"]
    for c in order0:
        E.append(r"%s & %d \\" % (c, cn_cnt.get(c, 0)))
    E.append(r"\midrule Total & %d \\" % sum(cn_cnt.values()))
    E.append(r"\bottomrule\end{tabular}\end{center}")
    open(os.path.join(HERE, "census.tex"), "w").write("\n".join(E) + "\n")
    TT = [r"{\small\setlength{\tabcolsep}{4pt}", r"\begin{longtable}{@{}lccccccl@{}}", r"\toprule",
          r"Id & $\delta$ & $\theta=0$ & $1$ & $2$ & $3$ & $4$ & Case threshold \\", r"\midrule\endhead", r"\bottomrule\endfoot"]
    for m in sources:
        row = [m["id"], "$\\infty$" if delta(m) is None else str(delta(m))]
        for t in THETAS:
            row.append(classify(dict(m, theta=t)))
        row.append(str(m["theta"]))
        TT.append(" & ".join(row) + r" \\")
    TT.append(r"\end{longtable}}")
    open(os.path.join(HERE, "thresholds.tex"), "w").write("\n".join(TT) + "\n")
    write_catalogue(sources)
    write_variants(vrows)
    write_profiles(models)

    # ---- summary tables
    S = []
    S.append(r"\begin{center}\small")
    S.append(r"\begin{tabular}{@{}lp{0.36\linewidth}rrp{0.3\linewidth}@{}}\toprule")
    S.append(r"Class & Description & Sources & All & Witnesses (first five) \\ \midrule")
    desc = {
        "G-fl": "inferential, through a false lemma; truth-maker varies",
        "G-nfl": "inferential, no false lemma; truth-maker varies",
        "G-int": "non-inferential; truth-maker varies (intervening)",
        "G-env": "look-alike, trick or faulty device nearby",
        "G-tmp": "moment of consultation varies (temporal)",
        "G-lot": "outcome of a chance process varies (lottery)",
        "G-tst": "testimonial source varies or is insincere",
        "G-mrg": "parameter within the margin of discrimination",
        "G-nec": "necessary content; basis-wide unsafety only",
        "K": "knowledge (justified, basis-wide safe)",
        "U": "unjustified",
        "F": "justified false belief",
    }
    for c in order:
        ws = wit.get(c, [])
        S.append(r"%s & %s & %d & %d & %s \\" % (c, desc[c], cls_src.get(c, 0), cls_all.get(c, 0),
                                                  ", ".join(ws[:5]) if ws else "--"))
    S.append(r"\bottomrule\end{tabular}\end{center}")
    open(os.path.join(HERE, "classes.tex"), "w").write("\n".join(S) + "\n")

    M = [r"\begin{center}\small", r"\begin{tabular}{@{}l" + "r" * len(routes) + r"@{}}\toprule",
         "Class & " + " & ".join(ROUTE_NAME[r][:5] + "." for r in routes) + r" \\ \midrule"]
    for c in gclasses:
        M.append(c + " & " + " & ".join(str(mat[(c, r)]) if mat[(c, r)] else "." for r in routes) + r" \\")
    M.append(r"\bottomrule\end{tabular}\end{center}")
    open(os.path.join(HERE, "matrix.tex"), "w").write("\n".join(M) + "\n")

    R = [r"\begin{center}\small", r"\begin{tabular}{@{}lrrr@{}}\toprule",
         r"Condition & Correct on undisputed sources & Rate & Agrees with safety on variants \\ \midrule"]
    for k, (a, n) in racc.items():
        R.append(r"%s & %d / %d & %.2f & %s \\" % (k, a, n, a / n,
                                                  ("%d / %d" % (vagree[k], len(allv))) if k in vagree else "--"))
    R.append(r"\bottomrule\end{tabular}\end{center}")
    open(os.path.join(HERE, "rivals.tex"), "w").write("\n".join(R) + "\n")

    D = [r"\begin{center}\small", r"\begin{tabular}{@{}lllp{0.5\linewidth}@{}}\toprule",
         r"Id & Source verdict & Computed & Kind and note \\ \midrule"]
    for m in depart:
        v = verdicts(m)
        D.append(r"%s & %s & %s & (%s) %s \\" % (m["id"], "knowledge" if m["lit"] == "K" else "not knowledge",
                                                 classify(m), m["dispute"][0], m["dispute"][1]))
    D.append(r"\bottomrule\end{tabular}\end{center}")
    open(os.path.join(HERE, "departures.tex"), "w").write("\n".join(D) + "\n")

    def wl(d, k):
        return ", ".join(d.get(k, [])[:6])
    C = [r"\begin{center}\small", r"\begin{tabular}{@{}llrp{0.48\linewidth}@{}}\toprule",
         r"Feature & Safe & Count & Witnesses (first six) \\ \midrule"]
    for key in [(True, True), (True, False), (False, True), (False, False)]:
        C.append(r"causal %s & %s & %d & %s \\" % (yn(key[0]), yn(key[1]), combos[key], wl(combo_wit, key)))
    C.append(r"\midrule")
    for key in [(True, True), (True, False), (False, True), (False, False)]:
        C.append(r"false lemma %s & %s & %d & %s \\" % (yn(key[0]), yn(key[1]), lcombo[key], wl(lwit, key)))
    C.append(r"\bottomrule\end{tabular}\end{center}")
    open(os.path.join(HERE, "combos.tex"), "w").write("\n".join(C) + "\n")

    nG = sum(1 for m in models if verdicts(m)["Gp"])
    jt_src = [m for m in sources if m["J"] and m["T"]]
    nonrobust = [m["id"] for m in jt_src
                 if len({safe_basis(m, t) for t in (1, 2, 3)}) > 1]
    nmulti = 0
    for m in models:
        fs = falsifiers(m, m["theta"])
        if fs:
            dm = min(x.d for x in fs)
            if len({x.tag for x in fs if x.d == dm}) > 1:
                nmulti += 1
    gdelta = Counter(delta(m) for m in G_rows)
    nK = sum(1 for m in models if verdicts(m)["K"])
    ops = Counter(n["op"] for n in allv)
    stats = OrderedDict(
        nsources=len(sources), nlit=len(lit_rows), nschem=len(sources) - len(lit_rows),
        nvariants=len(allv), nmodels=len(models), nG=nG, nK=nK, nGrows=len(G_rows),
        nagree=len(agree), ndepart=len(depart), nundisputed=len(undisputed),
        locc=loci["c"], locd=loci["d"],
        evsafe=ev[(True, True)], evunsafe=ev[(True, False)],
        njtsrc=len(jt_src), nnonrobust=len(nonrobust), nmulti=nmulti,
        nGdeltaone=gdelta.get(1, 0), cnmodels=cn_models, cnchecks=cn_checks, cnconfigs=cn_cfg,
    )
    with open(os.path.join(HERE, "stats.tex"), "w") as f:
        for k, val in stats.items():
            f.write("\\newcommand{\\st%s}{%d}\n" % (k, val))
        f.write("%% operations: %s\n" % dict(sorted(ops.items())))
        f.write("%% classes (all models): %s\n" % dict(sorted(cls_all.items())))
        f.write("%% departures: %s\n" % [m["id"] for m in depart])
        f.write("%% nonrobust: %s\n" % nonrobust)
    print(dict(stats))
    print("ops", dict(sorted(ops.items())))
    print("classes", dict(sorted(cls_all.items())))
    print("departures", [m["id"] for m in depart])
    print("nonrobust", nonrobust, "gdelta", dict(gdelta))
    print("rivals", {k: tuple(v) for k, v in racc.items()}, dict(vagree))


if __name__ == "__main__":
    main()
