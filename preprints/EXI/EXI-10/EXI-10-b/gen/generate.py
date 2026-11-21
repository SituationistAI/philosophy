#!/usr/bin/env python3
"""Generator for EXI-10-b, "Appendix: Empirical Studies of Boredom".

Reads the hand-curated study table in studies.py, computes for each study its
bearing on (a) the mismatch thesis and (b) the function thesis of EXI-10 by
the fixed rules below, and writes the annotated bibliography and the
cross-tabulations included by ../main.tex.  Standard library only;
deterministic output.
"""
import os
from collections import Counter, OrderedDict
from studies import S

HERE = os.path.dirname(os.path.abspath(__file__))

TAGS = OrderedDict([
    ("under+", "boredom rises with under-challenge or monotony"),
    ("over+", "boredom rises with over-challenge"),
    ("meaning+", "boredom rises with lack of meaning or value"),
    ("fit-", "matched challenge and skill yields engagement"),
    ("attn", "boredom linked to failure of attentional engagement"),
    ("relational", "state boredom depends on person and situation jointly"),
    ("overanx", "over-challenge yields anxiety, not boredom"),
    ("seek", "boredom prompts seeking of stimulation or novelty"),
    ("switch", "boredom prompts change of goal or of manner of engagement"),
    ("meaningreg", "boredom prompts meaning-restoring responses"),
    ("creat", "boredom followed by more divergent thinking"),
    ("signal", "boredom described as a signal or feedback state"),
    ("distinct", "boredom has a distinct experiential or physiological profile"),
    ("harm", "boredom prompts self-harming or costly responses"),
    ("perf-", "boredom related to lower performance on the task"),
    ("chronic", "trait proneness related to poor outcomes"),
    ("person", "trait or individual-difference correlates"),
    ("meas", "measurement or conceptual work"),
    ("neuro", "neural correlates"),
])

DESIGN = OrderedDict([("exp", "experiment"), ("esm", "experience sampling"), ("corr", "correlational"),
                      ("psy", "psychometric"), ("phys", "physiological / imaging"), ("meta", "meta-analysis"),
                      ("rev", "review"), ("theo", "theory"), ("qual", "interview-based")])

A_SUP = {"under+", "over+", "meaning+", "fit-", "attn", "relational"}
A_CHA = {"overanx"}
B_MOT = {"seek", "switch", "meaningreg", "creat"}
B_SIG = {"signal", "distinct"}
B_COST = {"harm"}
B_STRICT_COST = {"harm", "chronic", "perf-"}


def combine(sup, cha):
    if sup and cha:
        return "S/C"
    if sup:
        return "S"
    if cha:
        return "C"
    return "N"


def bearing_a(t):
    sup, cha = sorted(set(t) & A_SUP), sorted(set(t) & A_CHA)
    return combine(sup, cha), sup, cha


def bearing_b(t, strict=False):
    mot, sig = sorted(set(t) & B_MOT), sorted(set(t) & B_SIG)
    cost = sorted(set(t) & (B_STRICT_COST if strict else B_COST))
    return combine(mot + sig, cost), mot, sig, cost


def trace(t):
    a, asup, acha = bearing_a(t)
    b, mot, sig, cost = bearing_b(t)
    parts = []
    parts.append("(a) %s: support [%s], challenge [%s]" % (a, ", ".join(asup) or "--", ", ".join(acha) or "--"))
    parts.append("(b) %s: motivation [%s], signal [%s], cost [%s]" % (
        b, ", ".join(mot) or "--", ", ".join(sig) or "--", ", ".join(cost) or "--"))
    acc = sorted(set(t) & {"chronic", "perf-", "person"})
    if acc:
        parts.append("accommodated by Cor.~3.4 of EXI-10-a: [%s]" % ", ".join(acc))
    return "; ".join(parts)


VALS = ["S", "S/C", "N", "C"]


def tab2(rows, cols, cell, rowname, rlabels=None):
    L = [r"\begin{center}\small", r"\begin{tabular}{@{}l" + "r" * (len(cols) + 1) + r"@{}}\toprule",
         rowname + " & " + " & ".join(cols) + r" & Total \\ \midrule"]
    tot = Counter()
    for r in rows:
        vals = [cell(r, c) for c in cols]
        for c, v in zip(cols, vals):
            tot[c] += v
        L.append((rlabels[r] if rlabels else r) + " & " + " & ".join(str(v) if v else "." for v in vals) +
                 " & %d \\\\" % sum(vals))
    L.append(r"\midrule Total & " + " & ".join(str(tot[c]) for c in cols) + " & %d \\\\" % sum(tot.values()))
    L.append(r"\bottomrule\end{tabular}\end{center}")
    return "\n".join(L) + "\n"


def main():
    ids = [s["id"] for s in S]
    assert len(ids) == len(set(ids)) and len({s["key"] for s in S}) == len(S)
    for s in S:
        assert s["design"] in DESIGN, s["id"]
        for t in s["tags"]:
            assert t in TAGS, (s["id"], t)
        assert s["tags"], s["id"]
    rows = sorted(S, key=lambda s: (s["year"], s["id"]))
    for s in rows:
        s["a"] = bearing_a(s["tags"])[0]
        s["b"] = bearing_b(s["tags"])[0]
        s["bs"] = bearing_b(s["tags"], strict=True)[0]

    # ---- annotated bibliography
    L = []
    for s in rows:
        L.append(r"\needspace{6\baselineskip}")
        L.append(r"\noindent\textbf{%s}\enspace \citet{%s}.\par" % (s["id"], s["key"]))
        L.append(r"{\small\noindent\textit{Design:} %s.\quad \textit{Sample:} %s.\quad \textit{Measure:} %s.\par" %
                 (DESIGN[s["design"]], s["sample"], s["measure"]))
        L.append(r"\noindent\textit{Finding.} %s\par" % s["finding"])
        L.append(r"\noindent\textit{Codes:} \texttt{%s}.\quad \textit{Bearing:} (a) \textbf{%s}, (b) \textbf{%s}.\par" %
                 (" ".join(s["tags"]), s["a"], s["b"]))
        L.append(r"\noindent\textit{Rule trace:} %s.\par}" % trace(s["tags"]).replace("[", "{[}").replace("]", "{]}"))
        L.append(r"\medskip")
    open(os.path.join(HERE, "annotated.tex"), "w").write("\n".join(L) + "\n")

    # ---- summary table (one line per study)
    T = [r"{\footnotesize\setlength{\tabcolsep}{3pt}", r"\begin{longtable}{@{}lrllccc@{}}", r"\toprule",
         r"Id & Year & Design & Codes & (a) & (b) & (b) strict \\", r"\midrule\endhead", r"\bottomrule\endfoot"]
    for s in rows:
        T.append(r"%s & %d & %s & \texttt{%s} & %s & %s & %s \\" % (
            s["id"], s["year"], DESIGN[s["design"]], " ".join(s["tags"]), s["a"], s["b"], s["bs"]))
    T.append(r"\end{longtable}}")
    open(os.path.join(HERE, "summary.tex"), "w").write("\n".join(T) + "\n")

    # ---- cross-tabulations
    ct = Counter((s["a"], s["b"]) for s in rows)
    open(os.path.join(HERE, "xt_ab.tex"), "w").write(
        tab2(VALS, VALS, lambda r, c: ct[(r, c)], r"(a) $\backslash$ (b)"))
    cd_a = Counter((s["design"], s["a"]) for s in rows)
    cd_b = Counter((s["design"], s["b"]) for s in rows)
    designs = [d for d in DESIGN if any(s["design"] == d for s in rows)]
    open(os.path.join(HERE, "xt_design_a.tex"), "w").write(
        tab2(designs, VALS, lambda r, c: cd_a[(r, c)], "Design (a)", DESIGN))
    open(os.path.join(HERE, "xt_design_b.tex"), "w").write(
        tab2(designs, VALS, lambda r, c: cd_b[(r, c)], "Design (b)", DESIGN))
    dec = lambda y: "%ds" % (y // 10 * 10) if y >= 2000 else ("before 2000")
    decs = ["before 2000", "2000s", "2010s", "2020s"]
    cdec = Counter((dec(s["year"]), s["a"], s["b"]) for s in rows)
    D = [r"\begin{center}\small", r"\begin{tabular}{@{}lrrrrrrrrr@{}}\toprule",
         r" & \multicolumn{4}{c}{(a)} & \multicolumn{4}{c}{(b)} & \\",
         r"Period & S & S/C & N & C & S & S/C & N & C & Total \\ \midrule"]
    for d in decs:
        ra = [sum(v for (dd, a, b), v in cdec.items() if dd == d and a == x) for x in VALS]
        rb = [sum(v for (dd, a, b), v in cdec.items() if dd == d and b == x) for x in VALS]
        D.append(d + " & " + " & ".join(str(x) if x else "." for x in ra + rb) + " & %d \\\\" % sum(ra))
    D.append(r"\bottomrule\end{tabular}\end{center}")
    open(os.path.join(HERE, "xt_period.tex"), "w").write("\n".join(D) + "\n")
    # empirical only (exclude theory and review)
    emp = [s for s in rows if s["design"] not in ("theo", "rev")]
    ce = Counter((s["a"], s["b"]) for s in emp)
    open(os.path.join(HERE, "xt_ab_emp.tex"), "w").write(
        tab2(VALS, VALS, lambda r, c: ce[(r, c)], r"(a) $\backslash$ (b)"))
    # strict sensitivity
    cs = Counter((s["b"], s["bs"]) for s in rows)
    open(os.path.join(HERE, "xt_strict.tex"), "w").write(
        tab2(VALS, VALS, lambda r, c: cs[(r, c)], r"(b) lenient $\backslash$ strict"))

    # ---- clauses and statements of EXI-10-a
    CL = OrderedDict([
        (r"Def.~2.2, under-challenge", ({"under+"}, set())),
        (r"Def.~2.2, over-challenge", ({"over+"}, {"overanx"})),
        (r"Def.~2.2, meaninglessness", ({"meaning+"}, set())),
        (r"Assumption~2.4 (value of engagement)", ({"fit-"}, set())),
        (r"Lemma~3.1 (signal)", ({"signal", "distinct", "attn"}, set())),
        (r"Lemma~3.2 (motivation)", ({"seek", "switch", "meaningreg", "creat"}, set())),
        (r"Theorem~3.3 (adaptive function)", ({"fit-", "switch", "meaningreg", "creat"}, {"harm"})),
        (r"Corollary~3.4 (chronic boredom)", ({"chronic", "person"}, set())),
    ])
    C = [r"{\small\setlength{\tabcolsep}{3pt}", r"\begin{longtable}{@{}p{0.27\linewidth}p{0.43\linewidth}p{0.24\linewidth}@{}}",
         r"\toprule", r"Statement of EXI-10-a & Bearing for (all study ids) & Bearing against \\",
         r"\midrule\endhead", r"\bottomrule\endfoot"]
    clause_counts = OrderedDict()
    for name, (pos, neg) in CL.items():
        p = [s["id"] for s in rows if set(s["tags"]) & pos]
        n = [s["id"] for s in rows if set(s["tags"]) & neg]
        pe = [s["id"] for s in rows if set(s["tags"]) & pos and s["design"] not in ("theo", "rev")]
        clause_counts[name] = (len(p), len(pe), len(n))
        C.append(r"%s & %s (%d; %d empirical) & %s \\" % (name, ", ".join(p) or "--", len(p), len(pe),
                                                        ", ".join(n) or "--"))
    C.append(r"\end{longtable}}")
    open(os.path.join(HERE, "clauses.tex"), "w").write("\n".join(C) + "\n")

    # ---- incidence matrix studies x statements
    short = ["Und", "Ovr", "Mng", "A2.4", "L3.1", "L3.2", "T3.3", "C3.4"]
    M = [r"{\footnotesize\setlength{\tabcolsep}{4pt}", r"\begin{longtable}{@{}l" + "c" * len(short) + r"@{}}",
         r"\caption{Entries and the statements of EXI-10-a they bear on.}\label{tab:matrix}\\",
         r"\toprule", "Id & " + " & ".join(short) + r" \\", r"\midrule\endhead", r"\bottomrule\endfoot"]
    colcount = [0] * len(short)
    for s in rows:
        cells = []
        for i, (pos, neg) in enumerate(CL.values()):
            p, n = bool(set(s["tags"]) & pos), bool(set(s["tags"]) & neg)
            cells.append("$\\pm$" if p and n else ("$+$" if p else ("$-$" if n else ".")))
            colcount[i] += (p or n)
        M.append(s["id"] + " & " + " & ".join(cells) + r" \\")
    M.append(r"\midrule Entries & " + " & ".join(str(c) for c in colcount) + r" \\")
    M.append(r"\end{longtable}}")
    open(os.path.join(HERE, "matrix.tex"), "w").write("\n".join(M) + "\n")

    # ---- samples
    def skind(x):
        x = x.lower()
        if x.startswith("none"):
            return "none (theory/review)"
        if "school" in x and "university" not in x:
            return "school students"
        if "undergraduate" in x or "student" in x or "university" in x:
            return "students"
        if "online" in x or "smartphone" in x:
            return "online or smartphone adults"
        return "other adult or laboratory"
    kinds = ["students", "school students", "online or smartphone adults", "other adult or laboratory", "none (theory/review)"]
    for s in rows:
        s["sk"] = skind(s["sample"])
    csa = Counter((s["sk"], s["a"]) for s in rows)
    csb = Counter((s["sk"], s["b"]) for s in rows)
    X = [r"\begin{center}\small", r"\begin{tabular}{@{}lrrrrrrrrr@{}}\toprule",
         r" & \multicolumn{4}{c}{(a)} & \multicolumn{4}{c}{(b)} & \\",
         r"Sample & S & S/C & N & C & S & S/C & N & C & Total \\ \midrule"]
    for k in kinds:
        ra = [csa[(k, v)] for v in VALS]
        rb = [csb[(k, v)] for v in VALS]
        X.append(k + " & " + " & ".join(str(x) if x else "." for x in ra + rb) + " & %d \\\\" % sum(ra))
    X.append(r"\bottomrule\end{tabular}\end{center}")
    open(os.path.join(HERE, "xt_sample.tex"), "w").write("\n".join(X) + "\n")

    # ---- tag frequencies
    tf = Counter(t for s in rows for t in s["tags"])
    F = [r"\begin{center}\small", r"\begin{tabular}{@{}llr@{}}\toprule", r"Code & Meaning & Studies \\ \midrule"]
    for t, m in TAGS.items():
        F.append(r"\texttt{%s} & %s & %d \\" % (t, m, tf[t]))
    F.append(r"\bottomrule\end{tabular}\end{center}")
    open(os.path.join(HERE, "codes.tex"), "w").write("\n".join(F) + "\n")

    ca, cb = Counter(s["a"] for s in rows), Counter(s["b"] for s in rows)
    cbs = Counter(s["bs"] for s in rows)
    st = OrderedDict(n=len(rows), nemp=len(emp), ntheo=len(rows) - len(emp),
                     aS=ca["S"], aSC=ca["S/C"], aN=ca["N"], aC=ca["C"],
                     bS=cb["S"], bSC=cb["S/C"], bN=cb["N"], bC=cb["C"],
                     bsS=cbs["S"], bsSC=cbs["S/C"], bsN=cbs["N"], bsC=cbs["C"],
                     ymin=min(s["year"] for s in rows), ymax=max(s["year"] for s in rows),
                     overpos=clause_counts[r"Def.~2.2, over-challenge"][0],
                     overposemp=clause_counts[r"Def.~2.2, over-challenge"][1],
                     overneg=clause_counts[r"Def.~2.2, over-challenge"][2])
    names = {"aSC": "aSandC", "bSC": "bSandC", "bsSC": "bsSandC"}
    with open(os.path.join(HERE, "stats.tex"), "w") as f:
        for k, v in st.items():
            f.write("\\newcommand{\\st%s}{%d}\n" % (names.get(k, k), v))
    print(dict(st))
    for k, v in clause_counts.items():
        print(k, v)


if __name__ == "__main__":
    main()
