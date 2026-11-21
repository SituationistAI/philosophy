#!/usr/bin/env python3
"""Generator for the computed part of REL-01-c.

Part A: enumerates finite second-order Kripke models (see models.py) up to
isomorphism and checks the axioms of the filter emendation AF, its
conclusion, the corresponding Scott axioms, and modal collapse.
Part B: checks the labelled natural-deduction derivations in derivations.py
with the checker in nd.py and typesets them.

Python 3 standard library only; deterministic output.
Writes: models_sym.tex, models_nonsym.tex, modelstats.tex, modelcounts.tex,
        deriv_*.tex, derivstats.tex
"""
import itertools, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from models import Model, partitions, atoms_of_partition  # noqa: E402
import nd  # noqa: E402
import derivations  # noqa: E402
import sem  # noqa: E402

# Scope I: every frame, n*m <= 6, n <= 3.  Scope II: symmetric frames only.
# Scope III: four worlds, one individual, frames that are symmetric or reflexive.
SCOPE_ALL = [(1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2)]
SCOPE_SYM = [(1, 4), (2, 4), (3, 3), (4, 2)]
SCOPE_REFL = [(4, 1)]


# ---------------------------------------------------------------- frames
def rel_from_mask(n, mk):
    return [[(mk >> (i * n + j)) & 1 == 1 for j in range(n)] for i in range(n)]


def canonical_frames(n):
    perms = list(itertools.permutations(range(n)))
    seen, out = set(), []
    for mk in range(1 << (n * n)):
        R = rel_from_mask(n, mk)
        best = None
        for p in perms:
            k = 0
            for i in range(n):
                for j in range(n):
                    if R[i][j]:
                        k |= 1 << (p[i] * n + p[j])
            if best is None or k < best:
                best = k
        if best not in seen:
            seen.add(best)
            out.append(best)
    out.sort(key=lambda k: (bin(k).count("1"), k))
    return out


def frame_conditions(n, R):
    W = range(n)
    return {
        "T": all(R[w][w] for w in W),
        "B": all(R[v][w] for w in W for v in W if R[w][v]),
        "4": all(R[w][u] for w in W for v in W for u in W if R[w][v] and R[v][u]),
        "D": all(any(R[w]) for w in W),
        "C": retraceable(n, R),
    }


def retraceable(n, R):
    T = [row[:] for row in R]
    for k in range(n):
        for i in range(n):
            if T[i][k]:
                for j in range(n):
                    if T[k][j]:
                        T[i][j] = True
    return all(T[v][w] for w in range(n) for v in range(n) if R[w][v])


def succ_str(n, R):
    return ".".join("".join(str(j) for j in range(n) if R[i][j]) or "-" for i in range(n))


def perm_int(Y, n, m, s, t):
    r = 0
    for w in range(n):
        for d in range(m):
            if (Y >> (w * m + d)) & 1:
                r |= 1 << (s[w] * m + t[d])
    return r


# ---------------------------------------------------------------- display
LET = "abcdefghijklmnopqrstuvwxyz"


def labeling(M):
    """point labeling: per world, the atom letter of each individual"""
    order = []
    lab = {}
    for w in range(M.n):
        for d in range(M.m):
            b = 1 << (w * M.m + d)
            a = next(x for x in M.atoms if x & b)
            if a not in lab:
                lab[a] = LET[len(lab)]
                order.append(a)
    s = "|".join("".join(lab[next(x for x in M.atoms if x & (1 << (w * M.m + d)))] for d in range(M.m))
                 for w in range(M.n))
    return s, lab


def letters(Y, lab):
    if Y == 0:
        return "0"
    return "".join(sorted(l for a, l in lab.items() if a & Y))


# ---------------------------------------------------------------- part A
def analyse(n, R, m, atoms, c):
    succ = [sum(1 << j for j in range(n) if R[i][j]) for i in range(n)]
    M = Model(n, succ, m, atoms, c)
    if not M.F2_ok():
        return None, "F2"
    G = M.G_A()
    if G not in M.Pset:
        return None, "G-comp"
    if not M.P(G):
        return None, "A3"
    NE = M.NE_A()
    if NE not in M.Pset:
        return None, "NE-comp"
    if not M.P(NE):
        return None, "A5"
    r = {"M": M, "G": G, "NE": NE}
    fail = [w for w in range(n) if not M.nec_inst(G, w)]
    r["concl_fail"] = fail
    r["exG"] = [w for w in range(n) if M.inst(G, w)]
    r["gods0"] = [d for d in range(m) if M.has(G, 0, d)]
    # checks of the intermediate results at every world
    T1 = all(M.pos_inst(Y, w) for w in range(n) for Y in M.Pi if M.P(Y))
    T2 = all(M.ess_A(G, w, d) for w in range(n) for d in range(m) if M.has(G, w, d))
    T3 = all(M.has(NE, w, d) for w in range(n) for d in range(m) if M.has(G, w, d))
    T4 = all(M.nec_x(G, w, d) for w in range(n) for d in range(m) if M.has(G, w, d))
    r["lemmas"] = (T1, T2, T3, T4)
    # modal collapse: a property Y and world w with exists x Y(x) at w but not box exists x Y(x)
    wit = None
    for w in range(n):
        for Y in M.Pi:
            if M.inst(Y, w) and not M.nec_inst(Y, w):
                if wit is None or (bin(Y).count("1"), Y, w) < (bin(wit[0]).count("1"), wit[0], wit[1]):
                    wit = (Y, w)
    r["collapse"] = wit
    # Scott's axioms on the same model
    if not M.ultra():
        r["scott"] = "."
    else:
        GS = M.G_S()
        NES = M.NE_S()
        if GS in M.Pset and M.P(GS) and NES in M.Pset and M.P(NES):
            sc_concl = all(M.nec_inst(GS, w) for w in range(n))
            r["scott"] = "S" if sc_concl else "s"
            r["scott_concl"] = sc_concl
        else:
            r["scott"] = "-"
    return r, "ok"


def enumerate_models():
    out = []
    reject = {}
    for (n, m) in SCOPE_ALL + SCOPE_SYM + SCOPE_REFL:
        sym_only = (n, m) in SCOPE_SYM
        refl_or_sym = (n, m) in SCOPE_REFL
        parts = [atoms_of_partition(p) for p in partitions(list(range(n * m)))]
        for fi, fm in enumerate(canonical_frames(n), 1):
            R = rel_from_mask(n, fm)
            cond = frame_conditions(n, R)
            if sym_only and not cond["B"]:
                continue
            if refl_or_sym and not (cond["B"] or cond["T"]):
                continue
            succ = [sum(1 << j for j in range(n) if R[i][j]) for i in range(n)]
            auts = [s for s in itertools.permutations(range(n))
                    if all(R[i][j] == R[s[i]][s[j]] for i in range(n) for j in range(n))]
            iperms = list(itertools.permutations(range(m)))
            seen = set()
            for atoms in parts:
                M0 = Model(n, succ, m, atoms, 0)
                if not M0.closed():
                    reject["closure"] = reject.get("closure", 0) + 1
                    continue
                for c in M0.Pi:
                    if c == 0:
                        continue
                    key = min((tuple(sorted(perm_int(a, n, m, s, t) for a in atoms)), perm_int(c, n, m, s, t))
                              for s in auts for t in iperms)
                    if key in seen:
                        continue
                    seen.add(key)
                    r, why = analyse(n, R, m, atoms, c)
                    if r is None:
                        reject[why] = reject.get(why, 0) + 1
                        continue
                    r.update(n=n, m=m, R=R, fi=fi, cond=cond, key=key)
                    out.append(r)
    return out, reject


def model_line(r, sym):
    M = r["M"]
    lab_s, lab = labeling(M)
    fr = f"F{r['n']}.{r['fi']}"
    cnd = ("T" if r["cond"]["T"] else "-") + ("B" if r["cond"]["B"] else "-") + ("4" if r["cond"]["4"] else "-")
    concl = "+" if not r["concl_fail"] else "-" + str(r["concl_fail"][0])
    ex = "".join(str(w) for w in r["exG"]) or "-"
    gods = "".join(str(d) for d in r["gods0"]) or "-"
    if r["collapse"]:
        Y, w = r["collapse"]
        col = f"{letters(Y, lab)}@{w}"
    else:
        col = "none"
    cells = [r["id"], fr, cnd, str(r["m"]), lab_s, letters(M.c, lab), letters(r["G"], lab),
             letters(r["NE"], lab), ex, gods, concl, r["scott"], col]
    return cells


def tt(s):
    return "\\texttt{" + s.replace("|", "\\textbar{}").replace("-", "-{}").replace("@", "@") + "}"


def write_models(models):
    sym = [r for r in models if r["cond"]["B"]]
    non = [r for r in models if not r["cond"]["B"]]
    hdr = ("id & frame & TB4 & $m$ & $\\Pi$ (atoms by point) & core & $G$ & $\\mathit{NE}$ & $\\exists G$ at & gods@0 "
           "& $\\nec\\exists G$ & Sc & collapse wit.\\\\")
    for fname, rows, title in (("models_sym.tex", sym, "symmetric"), ("models_nonsym.tex", non, "non-symmetric")):
        L = ["% generated by gen/generate.py -- do not edit",
             "{\\scriptsize\\setlength{\\tabcolsep}{2.6pt}",
             "\\begin{longtable}{@{}lllrlllllllll@{}}\\toprule", hdr, "\\midrule\\endfirsthead",
             "\\toprule", hdr, "\\midrule\\endhead"]
        cur = None
        for r in rows:
            if (r["n"], r["m"]) != cur:
                cur = (r["n"], r["m"])
                k = sum(1 for x in rows if (x["n"], x["m"]) == cur)
                L.append(f"\\multicolumn{{13}}{{@{{}}l}}{{\\rule{{0pt}}{{2.8ex}}\\footnotesize\\bfseries "
                         f"$n={cur[0]}$ worlds, $m={cur[1]}$ individuals: {k} model{'s' if k != 1 else ''}}}\\\\*")
            cells = model_line(r, True)
            L.append(" & ".join([cells[0], cells[1], tt(cells[2]), cells[3], tt(cells[4]), tt(cells[5]), tt(cells[6]),
                                 tt(cells[7]), tt(cells[8]), tt(cells[9]), tt(cells[10]), tt(cells[11]),
                                 tt(cells[12])]) + "\\\\")
        L.append("\\bottomrule\\end{longtable}}")
        open(os.path.join(HERE, fname), "w").write("\n".join(L) + "\n")
    return sym, non


# ---------------------------------------------------------------- main
def main():
    t0 = time.time()
    models, reject = enumerate_models()
    # sort and number
    models.sort(key=lambda r: (not r["cond"]["B"], r["n"], r["m"], r["fi"], r["key"]))
    for i, r in enumerate(models, 1):
        r["id"] = ("S" if r["cond"]["B"] else "N") + str(i if r["cond"]["B"] else
                                                          i - sum(1 for x in models if x["cond"]["B"]))
    sym, non = write_models(models)

    # ---- verification
    errors = []
    for r in sym:
        if r["concl_fail"]:
            errors.append(("conclusion fails on symmetric frame", r["id"]))
        if not all(r["lemmas"]):
            errors.append(("lemma fails on symmetric frame", r["id"], r["lemmas"]))
        if r["scott"] == "S" and r["collapse"]:
            errors.append(("Scott model without collapse", r["id"]))
    for r in models:
        if r["cond"]["C"] and (r["concl_fail"] or not all(r["lemmas"])):
            errors.append(("conclusion or lemma fails on retraceable frame", r["id"]))
        if not r["lemmas"][0] or not r["lemmas"][3]:
            errors.append(("T1/T4 fail", r["id"]))
    if errors:
        print("ERRORS", errors[:10])
        sys.exit(1)

    # ---- semantic cross-check of the syntax of Part B against the models of Part A
    X = derivations
    af_concl = X.deriv_af()[-1]["f"][2]
    collapse = X.deriv_scott()[-1]["f"][2]
    xchk = 0
    xform = 0
    for r in models:
        M = r["M"]
        if len(M.Pi) > 64:
            continue
        E = sem.Evaluator(M, X.DEFS)
        bad = []
        if E.term(X.G, {}) != r["G"] or E.term(X.NE, {}) != r["NE"]:
            bad.append("intension")
        for a in ("F1", "F2", "F3", "A3", "A4", "A5"):
            xform += 1
            if not E.valid(X.AXIOMS[a]):
                bad.append(a)
        xform += 2
        if E.valid(af_concl[1]) != (not r["concl_fail"]):
            bad.append("conclusion")
        if E.valid(collapse) != (r["collapse"] is None):
            bad.append("collapse")
        if r["scott"] in ("S", "s"):
            for a in ("S1", "F2", "S3", "A4", "S5"):
                xform += 1
                if not E.valid(X.AXIOMS[a]):
                    bad.append("Scott " + a)
        if (r["cond"]["B"] or r["cond"]["C"]) and not E.valid(af_concl):
            bad.append("retraceable conclusion")
        if bad:
            errors.append((r["id"], bad))
        xchk += 1
    if errors:
        print("CROSS-CHECK ERRORS", errors[:10])
        sys.exit(1)

    # ---- statistics
    def cnt(rows, pred):
        return sum(1 for r in rows if pred(r))
    st = {
        "Models": len(models),
        "Sym": len(sym), "Non": len(non),
        "SymColl": cnt(sym, lambda r: r["collapse"] is not None),
        "SymNoColl": cnt(sym, lambda r: r["collapse"] is None),
        "SymT": cnt(sym, lambda r: r["cond"]["T"]),
        "SymTColl": cnt(sym, lambda r: r["cond"]["T"] and r["collapse"] is not None),
        "NonFail": cnt(non, lambda r: bool(r["concl_fail"])),
        "NonC": cnt(non, lambda r: r["cond"]["C"]),
        "NonCFail": cnt(non, lambda r: r["cond"]["C"] and (bool(r["concl_fail"]) or not all(r["lemmas"]))),
        "NonNotC": cnt(non, lambda r: not r["cond"]["C"]),
        "NonNotCFail": cnt(non, lambda r: not r["cond"]["C"] and bool(r["concl_fail"])),
        "NonNotCOk": cnt(non, lambda r: not r["cond"]["C"] and not r["concl_fail"]),
        "NonOk": cnt(non, lambda r: not r["concl_fail"]),
        "NonFailT": cnt(non, lambda r: bool(r["concl_fail"]) and r["cond"]["T"]),
        "NonFailFour": cnt(non, lambda r: bool(r["concl_fail"]) and r["cond"]["4"]),
        "NonFailTFour": cnt(non, lambda r: bool(r["concl_fail"]) and r["cond"]["4"] and r["cond"]["T"]),
        "Ultra": cnt(models, lambda r: r["scott"] != "."),
        "ScottModels": cnt(models, lambda r: r["scott"] in "Ss" and r["scott"] != "."),
        "ScottSym": cnt(sym, lambda r: r["scott"] == "S"),
        "ScottSymColl": cnt(sym, lambda r: r["scott"] == "S" and r["collapse"] is not None),
        "ScottNonColl": cnt(non, lambda r: r["scott"] in "Ss" and r["scott"] != "." and r["collapse"] is not None),
        "UltraNotScott": cnt(models, lambda r: r["scott"] == "-"),
        "ManyGods": cnt(sym, lambda r: len(r["gods0"]) > 1),
        "RejClosure": reject.get("closure", 0),
        "RejFTwo": reject.get("F2", 0),
        "RejGcomp": reject.get("G-comp", 0),
        "RejAThree": reject.get("A3", 0),
        "RejNEcomp": reject.get("NE-comp", 0),
        "RejAFive": reject.get("A5", 0),
    }
    st["XModels"] = xchk
    st["XFormulas"] = xform
    st["Candidates"] = sum(v for k, v in reject.items() if k != "closure") + len(models)

    # counts per (n,m)
    C = ["% generated by gen/generate.py -- do not edit",
         "\\begin{center}\\footnotesize\\begin{tabular}{@{}rrrrrrrrr@{}}\\toprule",
         "$n$ & $m$ & scope & models & symmetric & collapse fails & $\\nec\\exists G$ fails & Scott models & Scott, collapse fails\\\\\\midrule"]
    for (n, m) in SCOPE_ALL + SCOPE_SYM + SCOPE_REFL:
        rows = [r for r in models if r["n"] == n and r["m"] == m]
        sc = "all" if (n, m) in SCOPE_ALL else ("B" if (n, m) in SCOPE_SYM else "B or T")
        C.append(f"{n} & {m} & {sc} & {len(rows)} & {cnt(rows, lambda r: r['cond']['B'])} & "
                 f"{cnt(rows, lambda r: r['collapse'] is not None)} & {cnt(rows, lambda r: bool(r['concl_fail']))} & "
                 f"{cnt(rows, lambda r: r['scott'] in ('S', 's'))} & "
                 f"{cnt(rows, lambda r: r['scott'] in ('S', 's') and r['collapse'] is not None)}\\\\")
    C.append("\\bottomrule\\end{tabular}\\end{center}")
    open(os.path.join(HERE, "modelcounts.tex"), "w").write("\n".join(C) + "\n")

    # ---- part B: derivations
    dstats = {}
    for name, (title, build) in derivations.DERIVATIONS.items():
        lines = build()
        res = nd.check(lines, derivations.AXIOMS, derivations.DEFS)
        if not res["ok"]:
            print("DERIVATION FAILED", name, res["error"])
            sys.exit(1)
        open(os.path.join(HERE, f"deriv_{name}.tex"), "w").write(
            nd.typeset(lines, res, derivations.DEFS))
        dstats[name] = res
        print(name, len(lines), "lines; open assumptions:", res["open"], "; relational rules:", res["relrules"],
              "; axioms:", res["axioms"])
    for name, res in dstats.items():
        key = name.capitalize()
        st["Lines" + key] = res["nlines"]
        st["Rules" + key] = res["nrules"]
    with open(os.path.join(HERE, "modelstats.tex"), "w") as fh:
        fh.write("% generated by gen/generate.py -- do not edit\n")
        for k, v in st.items():
            fh.write(f"\\newcommand{{\\cs{k}}}{{{v:,}}}\n".replace(",", "{,}"))
    for k, v in st.items():
        print(k, v)
    print("time", round(time.time() - t0, 1))


if __name__ == "__main__":
    main()
