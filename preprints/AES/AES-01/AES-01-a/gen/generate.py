#!/usr/bin/env python3
"""Generator for AES-01-a, "What Art Is".

Reads the hand-curated catalogue of episodes in cases.py; computes for each
episode the verdict of the institutional-uptake account (IU) of the
manuscript and the verdicts of six rival accounts; applies systematic
one-condition variants; enumerates the full space of encoded states and the
space of short histories of artworld events; checks the theorems of
Section 3 of the manuscript on every row (assert); and writes the LaTeX files
included by ../main.tex.

Python 3 standard library only; deterministic output.
"""
import itertools
import os
from collections import Counter, OrderedDict

from cases import CASES
from timelines import TIMELINES

HERE = os.path.dirname(os.path.abspath(__file__))

PRES = ("no", "maker", "other")
CRIT = ("none", "curio", "refused", "adverse", "favourable", "mixed", "divided")
MKT = ("none", "sold", "high")
ENGAGED = ("adverse", "favourable", "mixed")      # Definition 2.2
NOT_ENGAGED = ("none", "curio", "refused")
GAUT_THETA = 5

GROUPS = OrderedDict([
    ("R", "Duchamp's readymades"),
    ("I", "Indiscernibles and thought experiments"),
    ("P", "Performance, music and Fluxus"),
    ("M", "Minimal, conceptual and appropriation works"),
    ("A", "Adverse reception"),
    ("O", "Outsider and posthumous work"),
    ("H", "Before artworlds: caves, icons, ritual objects"),
    ("N", "Non-human makers and found objects"),
    ("F", "Forgery"),
    ("C", "The contemporary market"),
    ("D", "Objects mistaken, attacked or destroyed"),
    ("X", "Machine outputs"),
    ("S", "Schematic cases"),
])

CITE = {
    "Danto1964": r"\citet{Danto1964}", "Danto1981": r"\citet{Danto1981}",
    "Dickie1974": r"\citet{Dickie1974}", "deDuve1996": r"\citet{deDuve1996}",
    "Cage1961": r"\citet{Cage1961}", "Morgenthaler1921": r"\citet{Morgenthaler1921}",
    "Prinzhorn1922": r"\citet{Prinzhorn1922}", "Bataille1955": r"\citet{Bataille1955}",
    "Cartailhac1902": r"\citet{Cartailhac1902}", "Belting1994": r"\citet{Belting1994}",
    "Rubin1984": r"\citet{Rubin1984}", "McEvilley1984": r"\citet{McEvilley1984}",
    "Morris1962": r"\citet{Morris1962}", "Bredius1937": r"\citet{Bredius1937}",
    "Whistler1890": r"\citet{Whistler1890}", "Hertzmann2018": r"\citet{Hertzmann2018}",
}

VNAME = {"A": "art", "C": "contested", "K": "candidate (presented, not taken up)",
         "N": "not art (not presented)", "W": "not art (no artworld at this index)"}

# ------------------------------------------------------------------ verdicts


def iu(aw, pres, crit):
    """Principle P1 with Definitions 2.1--2.4: the institutional-uptake verdict.

    W: no artworld at the index; N: not presented; K: presented but not taken
    up (a candidate); C: the practice divided on engaging it; A: art.
    Market uptake and single declarations are not arguments: the verdict
    cannot depend on them.
    """
    if not aw:
        return "W"
    if pres == "no":
        return "N"
    if crit in NOT_ENGAGED:
        return "K"
    if crit in ENGAGED:
        return "A"
    return "C"


def iu_full(aw, pres, crit, mkt, decl):
    """The verdict as a function of the full encoded state (market uptake and
    declaration included), used to check Proposition 3.5 and Theorem 3.6."""
    v = iu(aw, pres, crit)
    return v


def dickie74(aw, pres):
    """Dickie (1974): status of candidate for appreciation conferred by a
    person acting on behalf of the artworld; conferral is read as
    presentation by a participant."""
    return "A" if aw and pres != "no" else "N"


def aesthetic(c):
    return {"Y": "A", "N": "N", "?": "?"}[c["ae"]]


def levinson(c):
    return {"Y": "A", "ur": "A", "N": "N", "?": "?"}[c["lev"]]


def gaut_count(c):
    return sum(int(x) for x in c["g"])


def gaut(c, theta=GAUT_THETA):
    n = gaut_count(c)
    if n >= theta:
        return "A"
    if n <= theta - 3:
        return "N"
    return "?"


def stecker(c):
    central = c["g"][8] == "1"
    if c["exc"] == "Y" or (central and c["fn"] == "Y"):
        return "A"
    if central and c["fn"] == "?":
        return "?"
    return "N"


def carroll(c):
    return {"Y": "A", "N": "N", "?": "?"}[c["narr"]]


RIVALS = OrderedDict([
    ("D74", ("Dickie 1974", lambda c: dickie74(c["aw"], c["pres"]))),
    ("AE", ("Beardsley", aesthetic)),
    ("HL", ("Levinson", levinson)),
    ("CG", ("Gaut, $\\theta=5$", gaut)),
    ("ST", ("Stecker", stecker)),
    ("CN", ("Carroll", carroll)),
])


def pole(v):
    if v == "A":
        return "+"
    if v in ("N", "K", "W"):
        return "-"
    return "o"


def relation(iuv, rv):
    a, b = pole(iuv), pole(rv)
    if "o" in (a, b):
        return "open"
    return "agree" if a == b else "diverge"


def verdict(c):
    return iu(c["aw"], c["pres"], c["crit"])

# ------------------------------------------------------------------ checks


def check_state(aw, pres, crit, mkt, decl):
    """Assert the theorems of Section 3 on one encoded state; return the
    list of theorem labels instantiated."""
    v = iu_full(aw, pres, crit, mkt, decl)
    used = []
    if not aw:
        assert v == "W"
    if aw and pres == "no":
        assert v == "N"                      # Lemma 3.1
        used.append("L3.1")
    if aw and pres != "no" and crit in NOT_ENGAGED:
        assert v == "K" and v != "A"         # Theorem 3.2
        used.append("T3.2")
    if aw and pres != "no" and crit == "adverse":
        assert v == "A"                      # Theorem 3.3
        used.append("T3.3")
    # Corollary 3.4: adverse and favourable uptake give the same verdict
    assert iu(aw, pres, "adverse") == iu(aw, pres, "favourable")
    # Proposition 3.5: independence of market uptake
    for m in MKT:
        assert iu_full(aw, pres, crit, m, decl) == v
    # Theorem 3.6: independence of single declarations; and acts of a single
    # agent (presentation, declaration, purchase) never suffice without uptake
    for d in (False, True):
        assert iu_full(aw, pres, crit, mkt, d) == v
    for p in PRES:
        for m in MKT:
            for d in (False, True):
                for cr in NOT_ENGAGED:
                    assert iu_full(aw, p, cr, m, d) != "A"
    used += ["C3.4", "P3.5", "T3.6"]
    return used


def check_episode(c):
    used = check_state(c["aw"], c["pres"], c["crit"], c["mkt"], c["decl"])
    # Dickie (1974) diverges from IU exactly on presented episodes without
    # (undivided) uptake.
    d, v = dickie74(c["aw"], c["pres"]), verdict(c)
    assert (pole(d) != pole(v)) == (v in ("K", "C")), c["id"]
    return used

# ------------------------------------------------------------------ variants

OPS = OrderedDict([
    ("p0", "presentation removed"),
    ("p1", "presented, nothing else changed"),
    ("u0", "uptake set to none"),
    ("ur", "uptake set to refused"),
    ("ua", "uptake set to adverse"),
    ("uf", "uptake set to favourable"),
    ("mk", "market uptake toggled"),
    ("dc", "declaration toggled"),
])


def variants(c):
    out = []
    aw, pres, crit, mkt, decl = c["aw"], c["pres"], c["crit"], c["mkt"], c["decl"]
    if pres != "no":
        out.append(("p0", aw, "no", "none", mkt, decl, "N", "L3.1"))
    if aw and pres == "no":
        out.append(("p1", aw, "other", "none", mkt, decl, "K", "T3.2"))
    if pres != "no" and crit != "none":
        out.append(("u0", aw, pres, "none", mkt, decl, "K", "T3.2"))
    if pres != "no" and crit != "refused":
        out.append(("ur", aw, pres, "refused", mkt, decl, "K", "T3.2"))
    if pres != "no" and crit != "adverse":
        out.append(("ua", aw, pres, "adverse", mkt, decl, "A", "T3.3"))
    if pres != "no" and crit != "favourable":
        out.append(("uf", aw, pres, "favourable", mkt, decl, "A", "C3.4"))
    m2 = "high" if mkt == "none" else "none"
    out.append(("mk", aw, pres, crit, m2, decl, verdict(c), "P3.5"))
    out.append(("dc", aw, pres, crit, mkt, not decl, verdict(c), "T3.6"))
    rows = []
    for op, a, p, cr, m, d, pred, thm in out:
        check_state(a, p, cr, m, d)
        v = iu_full(a, p, cr, m, d)
        assert v == pred, (c["id"], op, v, pred)
        rows.append(dict(op=op, aw=a, pres=p, crit=cr, mkt=m, decl=d, v=v,
                         pred=pred, thm=thm, d74=dickie74(a, p)))
    return rows

# ------------------------------------------------------------------ histories
# Events of a history (Appendix D): 0 nothing; P presentation by a participant;
# D a single agent's declaration; R refusal by a venue; S a sale;
# a adverse engagement; f favourable engagement; v divided engagement.
EVENTS = "0PDRSafv"


def trajectory(h):
    presented = engaged = divided = False
    out = []
    for e in h:
        if e == "P":
            presented = True
        elif e in "afm" and presented:
            engaged = True
        elif e == "v" and presented:
            divided = True
        if not presented:
            out.append("N")
        elif engaged:
            out.append("A")
        elif divided:
            out.append("C")
        else:
            out.append("K")
    return "".join(out)


def check_history(h):
    t = trajectory(h)
    # H1: without favourable or adverse engagement no stage is art (Thm 3.2, 3.6)
    if not any(e in "af" for e in h):
        assert "A" not in t
    # H2: adverse engagement at or after presentation yields art from that stage
    for i, e in enumerate(h):
        if e == "a" and "P" in h[:i]:
            assert t[i] == "A" and set(t[i:]) == {"A"}
    # H3: deleting sales and declarations changes nothing
    h2 = "".join("0" if e in "SD" else e for e in h)
    assert trajectory(h2) == t
    # H4: persistence: once art, art at every later stage
    if "A" in t:
        assert set(t[t.index("A"):]) == {"A"}
    # H5: exchanging adverse and favourable engagement changes nothing
    h3 = h.translate(str.maketrans("af", "fa"))
    assert trajectory(h3) == t
    # H6: a refusal never changes the trajectory
    h4 = "".join("0" if e == "R" else e for e in h)
    assert trajectory(h4) == t
    return t

# ------------------------------------------------------------------ LaTeX


def yn(b):
    return "yes" if b else "no"


CRIT_SHORT = {"none": "0", "curio": "c", "refused": "r", "adverse": "a",
              "favourable": "f", "mixed": "m", "divided": "v"}
PRES_SHORT = {"no": "n", "maker": "m", "other": "o"}
MKT_SHORT = {"none": "0", "sold": "s", "high": "h"}


def code(aw, pres, crit, mkt, decl):
    return "%s%s%s%s%s" % ("+" if aw else "-", PRES_SHORT[pres],
                           CRIT_SHORT[crit], MKT_SHORT[mkt], "+" if decl else "-")


def tt(s):
    return r"\texttt{%s}" % s


def write(name, text):
    with open(os.path.join(HERE, name), "w") as f:
        f.write(text)


def catalogue_tex(rows):
    out = []
    for g, title in GROUPS.items():
        members = [c for c in CASES if c["grp"] == g]
        if not members:
            continue
        out.append("\\subsection{%s}\n" % title)
        for c in members:
            v = verdict(c)
            rv = OrderedDict((k, f(c)) for k, (_, f) in RIVALS.items())
            out.append("\\needspace{8\\baselineskip}")
            out.append("\\paragraph{%s\\enspace %s, %s.}" % (c["id"], c["name"], c["stage"]))
            kind = " \\textit{(Thought experiment or schematic case.)}" if c["hyp"] else ""
            src = ""
            if c["cite"]:
                src = " \\textit{Literature:} " + "; ".join(CITE[k] for k in c["cite"]) + "."
            out.append(c["facts"] + kind + src + "\\par")
            pres = {"no": "no", "maker": "yes, by the maker", "other": "yes, by another"}[c["pres"]]
            if c["by"]:
                pres += " (" + c["by"] + ")"
            out.append(
                "\\noindent\\textit{Encoding} %s. Artworld: %s. Presented: %s. "
                "Critical uptake: \\textsc{%s}. %s Market uptake: %s. Single declaration: %s.\\par"
                % (tt(code(c["aw"], c["pres"], c["crit"], c["mkt"], c["decl"])),
                   yn(c["aw"]), pres, c["crit"], c["note"], c["mkt"], yn(c["decl"])))
            out.append(
                "\\noindent\\textit{Rival inputs.} Beardsley %s; Levinson %s; Gaut %s (%d/10); "
                "Stecker: function %s, excellence %s; narrative %s.\\par"
                % (c["ae"], c["lev"], tt(c["g"]), gaut_count(c), c["fn"], c["exc"], c["narr"]))
            div = [k for k, r in rv.items() if relation(v, r) == "diverge"]
            out.append(
                "\\noindent\\textit{Verdicts.} IU: \\textbf{%s} (%s). %s. Divergent: %s.\\par"
                % (v, VNAME[v], ", ".join("%s %s" % (k, r) for k, r in rv.items()),
                   ", ".join(div) if div else "none"))
            out.append("")
    return "\n".join(out)


def variants_tex(all_rows):
    head = (r"\begin{longtable}{@{}llllcccl@{}}" "\n"
            r"id & op & parent & variant & IU & pred. & D74 & checks \\ \midrule\endhead" "\n")
    lines = []
    for cid, parent, rows in all_rows:
        for r in rows:
            lines.append("%s & %s & %s & %s & %s & %s & %s & %s \\\\" % (
                cid, r["op"], tt(parent), tt(code(r["aw"], r["pres"], r["crit"], r["mkt"], r["decl"])),
                r["v"], r["pred"], r["d74"], r["thm"]))
    return "{\\scriptsize\n" + head + "\n".join(lines) + "\n\\end{longtable}}\n"


def census_tex(states):
    head = (r"\begin{longtable}{@{}rlllllcc@{\hspace{2.2em}}rlllllcc@{}}" "\n"
            r"\# & code & aw & pres & crit & mkt & IU & D74 & \# & code & aw & pres & crit & mkt & IU & D74 \\ \midrule\endhead" "\n")
    cells = []
    for i, s in enumerate(states, 1):
        aw, pres, crit, mkt, decl, v, d = s
        cells.append("%d & %s & %s & %s & %s & %s & %s & %s" % (
            i, tt(code(aw, pres, crit, mkt, decl)), "+" if aw else "-", pres, crit, mkt, v, d))
    half = (len(cells) + 1) // 2
    lines = []
    for i in range(half):
        right = cells[i + half] if i + half < len(cells) else "& & & & & & &"
        lines.append(cells[i] + " & " + right + " \\\\")
    return "{\\scriptsize\\setlength{\\tabcolsep}{3.5pt}\n" + head + "\n".join(lines) + "\n\\end{longtable}}\n"


def histories_tex(hist):
    ncol = 6
    head = ("\\begin{longtable}{@{}" + "l" * ncol + "@{}}\n")
    cells = ["%s\\,$\\mapsto$\\,%s" % (tt(h), tt(t)) for h, t in hist]
    rows = (len(cells) + ncol - 1) // ncol
    lines = []
    for i in range(rows):
        row = [cells[i + k * rows] if i + k * rows < len(cells) else "" for k in range(ncol)]
        lines.append(" & ".join(row) + " \\\\")
    return "{\\scriptsize\n" + head + "\n".join(lines) + "\n\\end{longtable}}\n"


EVNAME = {"P": "presentation", "D": "declaration", "R": "refusal", "S": "sale",
          "a": "adverse", "f": "favourable", "m": "mixed", "v": "divided",
          "c": "curiosity", "0": "no bearing"}


def timelines_tex():
    out = []
    for key, name, eps, events, note in TIMELINES:
        for e in eps:
            assert e in {c["id"] for c in CASES}, e
        h = "".join(ev for _, ev, _ in events)
        t = trajectory(h)
        # the trajectory agrees with the catalogue verdict of the last episode
        last = [c for c in CASES if c["id"] == eps[-1]][0]
        assert t[-1] == verdict(last), (key, t, verdict(last))
        # checks of Appendix D apply to documented histories as well
        h_noSD = "".join("0" if e in "SDRc" else e for e in h)
        assert trajectory(h_noSD) == t, key
        if "A" in t:
            first = t.index("A")
            assert set(t[first:]) == {"A"}
            status = "art, from the stage dated %s" % events[first][0]
        else:
            status = {"K": "candidate", "C": "contested", "N": "not presented"}[t[-1]]
        out.append("\\needspace{8\\baselineskip}")
        out.append("\\paragraph{%s\\enspace %s} (episodes %s). Computed status: \\textbf{%s}.%s" % (
            key, name, ", ".join(eps), status, (" " + note) if note else ""))
        out.append("\\begin{center}\\footnotesize\\begin{tabular}{@{}llp{0.52\\linewidth}lc@{}}")
        out.append("date & event & description & kind & status \\\\ \\midrule")
        for (date, ev, desc), st in zip(events, t):
            out.append("%s & \\texttt{%s} & %s & %s & %s \\\\" % (date, ev, desc, EVNAME[ev], st))
        out.append("\\end{tabular}\\end{center}")
        out.append("")
    return "\n".join(out), len(TIMELINES)


def rivals_tex():
    head = (r"\begin{longtable}{@{}lp{0.30\linewidth}cccccccc@{}}" "\n"
            r"id & case, stage & IU & D74 & AE & HL & CG & ST & CN & div. \\ \midrule\endhead" "\n")
    lines = []
    for c in CASES:
        v = verdict(c)
        rv = [f(c) for _, (_, f) in RIVALS.items()]
        cells = []
        for r in rv:
            rel = relation(v, r)
            cells.append(("\\textbf{%s}" % r) if rel == "diverge" else r)
        nd = sum(1 for r in rv if relation(v, r) == "diverge")
        lines.append("%s & %s, %s & %s & %s & %d \\\\" % (
            c["id"], c["name"], c["stage"], v, " & ".join(cells), nd))
    return "{\\footnotesize\n" + head + "\n".join(lines) + "\n\\end{longtable}}\n"


def thresholds_tex():
    thetas = range(3, 9)
    head = (r"\begin{longtable}{@{}l" + "c" * 10 + "c" + "c" * len(thetas) + "c@{}}" "\n"
            "id & " + " & ".join("g%d" % i for i in range(1, 11)) + " & $n$ & "
            + " & ".join("$\\theta{=}%d$" % t for t in thetas) + r" & IU \\ \midrule\endhead" "\n")
    lines = []
    for c in CASES:
        lines.append("%s & %s & %d & %s & %s \\\\" % (
            c["id"], " & ".join(c["g"]), gaut_count(c),
            " & ".join(gaut(c, t) for t in thetas), verdict(c)))
    return "{\\scriptsize\n" + head + "\n".join(lines) + "\n\\end{longtable}}\n"


def main():
    ids = [c["id"] for c in CASES]
    assert len(ids) == len(set(ids))

    # episodes
    used = Counter()
    for c in CASES:
        for u in check_episode(c):
            used[u] += 1

    # variants
    var_rows = []
    nvar = 0
    opcount = Counter()
    for c in CASES:
        rows = variants(c)
        nvar += len(rows)
        for r in rows:
            opcount[r["op"]] += 1
        var_rows.append((c["id"], code(c["aw"], c["pres"], c["crit"], c["mkt"], c["decl"]), rows))

    # census of encoded states
    allstates = list(itertools.product((True, False), PRES, CRIT, MKT, (False, True)))
    coherent = []
    for aw, pres, crit, mkt, decl in allstates:
        check_state(aw, pres, crit, mkt, decl)
        if (not aw and pres != "no") or (pres == "no" and crit != "none"):
            continue
        coherent.append((aw, pres, crit, mkt, decl, iu_full(aw, pres, crit, mkt, decl),
                         dickie74(aw, pres)))
    census_counts = Counter(s[5] for s in coherent)
    census_div = sum(1 for s in coherent if s[5] != s[6])

    # histories
    hist3 = []
    for h in itertools.product(EVENTS, repeat=3):
        h = "".join(h)
        hist3.append((h, check_history(h)))
    final3 = Counter(t[-1] for _, t in hist3)
    final_by_len = {}
    for n in (4, 5):
        cnt = Counter()
        for h in itertools.product(EVENTS, repeat=n):
            cnt[check_history("".join(h))[-1]] += 1
        final_by_len[n] = cnt

    # statistics
    vc = Counter(verdict(c) for c in CASES)
    rel = OrderedDict()
    for k, (_, f) in RIVALS.items():
        rel[k] = Counter(relation(verdict(c), f(c)) for c in CASES)
    grp = Counter(c["grp"] for c in CASES)
    nhyp = sum(1 for c in CASES if c["hyp"])

    # write files
    write("catalogue.tex", catalogue_tex(var_rows))
    write("variants.tex", variants_tex(var_rows))
    write("census.tex", census_tex(coherent))
    write("histories.tex", histories_tex(hist3))
    write("rivals.tex", rivals_tex())
    tl, ntl = timelines_tex()
    write("timelines.tex", tl)
    write("thresholds.tex", thresholds_tex())

    def mac(name, val):
        return "\\newcommand{\\st%s}{%s}\n" % (name, val)
    s = "% generated by gen/generate.py\n"
    s += mac("nepisodes", len(CASES)) + mac("nhyp", nhyp) + mac("nreal", len(CASES) - nhyp)
    for k in "ACKNW":
        s += mac("v" + k, vc.get(k, 0))
    s += mac("nvariants", nvar)
    for op in OPS:
        s += mac("op" + op.replace("0", "zero").replace("1", "one"), opcount.get(op, 0))
    s += mac("nstates", len(allstates)) + mac("ncoherent", len(coherent))
    s += mac("nincoherent", len(allstates) - len(coherent))
    for k in "ACKNW":
        s += mac("cs" + k, census_counts.get(k, 0))
    s += mac("censusdiv", census_div)
    s += mac("nhistthree", len(hist3))
    for k in "ACKN":
        s += mac("hthree" + k, final3.get(k, 0))
    for n, word in ((4, "four"), (5, "five")):
        s += mac("nhist" + word, sum(final_by_len[n].values()))
        for k in "ACKN":
            s += mac("h" + word + k, final_by_len[n].get(k, 0))
    for k in RIVALS:
        for r in ("agree", "diverge", "open"):
            s += mac(k.lower().replace("74", "s") + r, rel[k].get(r, 0))
    for g in GROUPS:
        s += mac("grp" + g, grp.get(g, 0))
    s += mac("ntimelines", ntl)
    write("stats.tex", s)

    print("episodes", len(CASES), "hypothetical", nhyp, "verdicts", dict(vc))
    print("variants", nvar, dict(opcount))
    print("states", len(allstates), "coherent", len(coherent), dict(census_counts), "D74 div", census_div)
    print("histories3", len(hist3), dict(final3), {n: dict(v) for n, v in final_by_len.items()})
    for k in RIVALS:
        print(k, dict(rel[k]))


if __name__ == "__main__":
    main()
