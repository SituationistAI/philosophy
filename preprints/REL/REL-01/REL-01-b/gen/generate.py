#!/usr/bin/env python3
"""Generator for the computed part of REL-01-b.

Enumerates all Kripke frames with 1 to NMAX worlds up to isomorphism,
classifies each by the frame conditions T, B, 4, 5, D and by the further
conditions U, U+, C (and the auxiliary U*, checked equivalent to U+) used in the manuscript, and decides by brute force
over all valuations whether each argument schema S1--S6 is valid on the
frame.  It also checks the quantified (constant-domain, two-being) form of
the schemas against the propositional verdicts, and checks that each schema
is valid on a frame exactly when the corresponding first-order condition
holds.  Python 3 standard library only; output is deterministic.

Writes: frames.tex (the listing), systems.tex (classification by systems),
counts.tex (summary counts), stats.tex (macros with numbers used in the text).
"""
import itertools, os, sys

NMAX = 4
HERE = os.path.dirname(os.path.abspath(__file__))


# ---------------------------------------------------------------- frames
def rel_from_mask(n, m):
    return [[(m >> (i * n + j)) & 1 == 1 for j in range(n)] for i in range(n)]


def mask_from_rel(n, R):
    m = 0
    for i in range(n):
        for j in range(n):
            if R[i][j]:
                m |= 1 << (i * n + j)
    return m


def canonical_frames(n):
    perms = list(itertools.permutations(range(n)))
    seen = set()
    out = []
    for m in range(1 << (n * n)):
        R = rel_from_mask(n, m)
        best = None
        for p in perms:
            # relabel: world i becomes p[i]
            Q = [[False] * n for _ in range(n)]
            for i in range(n):
                for j in range(n):
                    if R[i][j]:
                        Q[p[i]][p[j]] = True
            k = mask_from_rel(n, Q)
            if best is None or k < best:
                best = k
        if best not in seen:
            seen.add(best)
            out.append(best)
    out.sort(key=lambda k: (bin(k).count("1"), k))
    return out


def succ(n, R):
    return [frozenset(j for j in range(n) if R[i][j]) for i in range(n)]


def tclosure(n, R):
    T = [row[:] for row in R]
    for k in range(n):
        for i in range(n):
            if T[i][k]:
                for j in range(n):
                    if T[k][j]:
                        T[i][j] = True
    return T


def upto(n, R, k):
    """worlds reachable in 1..k steps"""
    S = succ(n, R)
    out = []
    for w in range(n):
        reach, frontier = set(), {w}
        for _ in range(k):
            frontier = set().union(*[S[x] for x in frontier]) if frontier else set()
            reach |= frontier
        out.append(frozenset(reach))
    return out


# ---------------------------------------------------------------- conditions
def conditions(n, R):
    W = range(n)
    S = succ(n, R)
    Rp = tclosure(n, R)
    Sp = succ(n, Rp)
    c = {}
    c["T"] = all(R[w][w] for w in W)
    c["B"] = all(R[v][w] for w in W for v in W if R[w][v])
    c["4"] = all(R[w][u] for w in W for v in W for u in W if R[w][v] and R[v][u])
    c["5"] = all(R[v][u] for w in W for v in W for u in W if R[w][v] and R[w][u])
    c["D"] = all(len(S[w]) > 0 for w in W)
    # U: all successors of a world have the same successors
    c["U"] = all(S[u] == S[v] for w in W for u in S[w] for v in S[w])
    # U+: all successors of a world reach the same worlds
    c["U+"] = all(Sp[u] == Sp[v] for w in W for u in S[w] for v in S[w])
    # C: every step of accessibility can be retraced (R+ symmetric)
    c["C"] = all(Rp[v][w] for w in W for v in W if R[w][v])
    # Ck: every step can be retraced in at most k steps, and whatever a successor sees is reachable
    # in at most k steps from every successor
    for k in (2, 3):
        Sk = upto(n, R, k)
        c["C%d" % k] = all(w in Sk[v] for w in W for v in S[w]) and \
            all(S[u] <= Sk[v] for w in W for u in S[w] for v in S[w])
    # U*: whatever a successor sees, every successor reaches
    c["U*"] = all(S[u] <= Sp[v] for w in W for u in S[w] for v in S[w])
    return c


# ---------------------------------------------------------------- schemas
def box(S, X, n):
    return frozenset(w for w in range(n) if S[w] <= X)


def dia(S, X, n):
    return frozenset(w for w in range(n) if S[w] & X)


SCHEMAS = ["S1", "S2", "S3", "S4", "S5", "S6", "S7", "S8"]
SCHEMA_COND = {"S1": "B", "S2": "5", "S3": "U", "S4": "4", "S5": "C", "S6": "U+", "S7": "C2", "S8": "C3"}


def schema_sets(n, S, Sp, X, S2=None, S3=None):
    """Return, for valuation X of p, the sets where antecedent and consequent hold."""
    W = frozenset(range(n))
    bp = box(S, X, n)
    bpp = box(Sp, X, n)          # box-plus p: p at every world reachable in >=1 steps
    d_bp = dia(S, bp, n)
    d_bpp = dia(S, bpp, n)
    return {
        "S1": (d_bp, X),
        "S2": (d_bp, bp),
        "S3": (d_bp, box(S, bp, n)),
        "S4": (bp, box(S, bp, n)),
        "S5": (d_bpp, X),
        "S6": (d_bpp, box(S, bpp, n)),
        "S7": (dia(S, box(S2, X, n), n), X & box(S, bp, n)),
        "S8": (dia(S, box(S3, X, n), n), X & box(S, bp, n)),
    }


def evaluate(n, R):
    S = succ(n, R)
    Sp = succ(n, tclosure(n, R))
    S2, S3 = upto(n, R, 2), upto(n, R, 3)
    valid = {s: True for s in SCHEMAS}
    witness = {s: None for s in SCHEMAS}
    for vm in range(1 << n):
        X = frozenset(w for w in range(n) if (vm >> w) & 1)
        ss = schema_sets(n, S, Sp, X, S2, S3)
        for s in SCHEMAS:
            ante, cons = ss[s]
            bad = ante - cons
            if bad and valid[s]:
                valid[s] = False
                witness[s] = (min(bad), vm)
    return valid, witness


def evaluate_quantified(n, R, nb=2):
    """Constant domain of nb beings; M(x,w): x exists and is maximally excellent at w.
    MG(x,w) iff M(x,v) for all v with wRv; MG*(x,w) iff M(x,v) for all v with wR+v.
    Returns validity of the quantified forms of S1..S6."""
    S = succ(n, R)
    Sp = succ(n, tclosure(n, R))
    S2, S3 = upto(n, R, 2), upto(n, R, 3)
    W = frozenset(range(n))
    valid = {s: True for s in SCHEMAS}
    for vm in range(1 << (n * nb)):
        Ms = [frozenset(w for w in range(n) if (vm >> (b * n + w)) & 1) for b in range(nb)]
        mg = [box(S, M, n) for M in Ms]           # where being b is maximally great
        mgs = [box(Sp, M, n) for M in Ms]         # where b is maximally great*
        some_mg = frozenset().union(*mg)
        some_mgs = frozenset().union(*mgs)
        some_M = frozenset().union(*Ms)           # some being exists and is max. excellent
        nec_some_mg = box(S, some_mg, n)
        nec_some_mgs = box(S, some_mgs, n)
        pos_some_mg = dia(S, some_mg, n)
        pos_some_mgs = dia(S, some_mgs, n)
        # S2 (Lemma 3.3 instance): poss some MG -> some MG
        # S4 (Anselm's principle, quantified): some MG -> nec some MG
        sets = {
            "S1": (pos_some_mg, some_M),
            "S2": (pos_some_mg, some_mg),
            "S3": (pos_some_mg, nec_some_mg),
            "S4": (some_mg, nec_some_mg),
            "S5": (pos_some_mgs, some_M),
            "S6": (pos_some_mgs, nec_some_mgs),
            "S7": (dia(S, frozenset().union(*[box(S2, M, n) for M in Ms]), n), some_M & nec_some_mg),
            "S8": (dia(S, frozenset().union(*[box(S3, M, n) for M in Ms]), n), some_M & nec_some_mg),
        }
        for s in SCHEMAS:
            a, c = sets[s]
            if a - c:
                valid[s] = False
    return valid


# ---------------------------------------------------------------- formatting
def succ_str(n, R):
    parts = []
    for i in range(n):
        s = "".join(str(j) for j in range(n) if R[i][j])
        parts.append(s if s else "-")
    return ".".join(parts)


def flags(c, keys):
    return "".join((k if c[k] else "-") for k in keys)


def main():
    frames = []
    for n in range(1, NMAX + 1):
        for k, m in enumerate(canonical_frames(n), 1):
            R = rel_from_mask(n, m)
            c = conditions(n, R)
            v, wit = evaluate(n, R)
            q = evaluate_quantified(n, R)
            frames.append(dict(n=n, k=k, id=f"F{n}.{k}", R=R, c=c, v=v, wit=wit, q=q))

    # ---- verification of correspondences and of the quantified reduction
    mism = []
    for f in frames:
        for s in SCHEMAS:
            if f["v"][s] != f["c"][SCHEMA_COND[s]]:
                mism.append((f["id"], s, "cond"))
            if f["v"][s] != f["q"][s]:
                mism.append((f["id"], s, "quant"))
    # implication checks: C implies U+, 5 implies U, B implies C, U+ iff U*
    impl = []
    for f in frames:
        c = f["c"]
        if c["C"] and not c["U+"]:
            impl.append((f["id"], "C=>U+,U*"))
        if c["5"] and not c["U"]:
            impl.append((f["id"], "5=>U"))
        if c["B"] and not c["C"]:
            impl.append((f["id"], "B=>C"))
        if c["U+"] != c["U*"]:
            impl.append((f["id"], "U+<=>U*"))
    if mism or impl:
        print("MISMATCH", mism[:20], impl[:20])
        sys.exit(1)

    total = len(frames)
    by_n = {n: sum(1 for f in frames if f["n"] == n) for n in range(1, NMAX + 1)}

    # ---- the listing
    L = []
    L.append("% generated by gen/generate.py -- do not edit")
    L.append("\\begingroup\\fontsize{6.6}{7.7}\\selectfont\\setlength{\\columnsep}{12pt}\\setlength{\\parindent}{0pt}")
    for n in range(1, NMAX + 1):
        fs = [f for f in frames if f["n"] == n]
        L.append(f"\\subsection*{{Frames with {n} world{'s' if n > 1 else ''} ({len(fs)} isomorphism classes)}}")
        L.append("\\begin{multicols}{2}\\raggedright")
        hdr = f"{'id':<8}{'successors':<{max(11, n * n + n)}}{'TB45D':<6}{'UPC':<4}{'S1..S8':<9}w*"
        L.append("\\texttt{" + tex_tt(hdr) + "}\\par")
        for f in fs:
            sstr = succ_str(n, f["R"])
            fl = flags(f["c"], ["T", "B", "4", "5", "D"])
            cd = ("U" if f["c"]["U"] else "-") + ("P" if f["c"]["U+"] else "-") + \
                 ("C" if f["c"]["C"] else "-")
            vs = "".join("+" if f["v"][s] else "-" for s in SCHEMAS)
            w = f["wit"]["S5"] or f["wit"]["S6"]
            if f["wit"]["S5"]:
                w0, vm = f["wit"]["S5"]
                wtxt = f"{w0}:{vm:0{n}b}"[::-1] if False else f"{w0}:" + "".join(str((vm >> i) & 1) for i in range(n))
            elif f["wit"]["S6"]:
                w0, vm = f["wit"]["S6"]
                wtxt = f"{w0}:" + "".join(str((vm >> i) & 1) for i in range(n)) + "'"
            else:
                wtxt = "ok"
            line = f"{f['id']:<8}{sstr:<{max(11, n * n + n)}}{fl:<6}{cd:<4}{vs:<9}{wtxt}"
            L.append("\\texttt{" + tex_tt(line) + "}\\par")
        L.append("\\end{multicols}")
    L.append("\\endgroup")
    open(os.path.join(HERE, "frames.tex"), "w").write("\n".join(L) + "\n")

    # ---- systems table: classes of frames defined by subsets of axioms
    systems = [
        ("K", []), ("KD", ["D"]), ("KT", ["T"]), ("KB", ["B"]), ("K4", ["4"]), ("K5", ["5"]),
        ("KDB", ["D", "B"]), ("KTB", ["T", "B"]), ("KD4", ["D", "4"]), ("S4", ["T", "4"]),
        ("K45", ["4", "5"]), ("KD5", ["D", "5"]), ("KD45", ["D", "4", "5"]), ("KB4", ["B", "4"]),
        ("S5", ["T", "B", "4"]),
    ]
    T = []
    T.append("% generated by gen/generate.py -- do not edit")
    T.append("\\begin{center}\\small\\begin{tabular}{@{}lrrrrrrrrr@{}}\\toprule")
    T.append("System & frames & S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8\\\\\\midrule")
    sysres = {}
    for name, ax in systems:
        fs = [f for f in frames if all(f["c"][a] for a in ax)]
        cells = []
        res = {}
        for s in SCHEMAS:
            k = sum(1 for f in fs if f["v"][s])
            res[s] = (k, len(fs))
            cells.append("\\textbf{all}" if k == len(fs) else str(k))
        sysres[name] = res
        T.append(f"{name} & {len(fs)} & " + " & ".join(cells) + "\\\\")
    T.append("\\bottomrule\\end{tabular}\\end{center}")
    open(os.path.join(HERE, "systems.tex"), "w").write("\n".join(T) + "\n")

    # ---- counts by combination of the five standard conditions
    combos = {}
    for f in frames:
        key = flags(f["c"], ["T", "B", "4", "5", "D"])
        combos.setdefault(key, []).append(f)
    C = []
    C.append("% generated by gen/generate.py -- do not edit")
    C.append("{\\footnotesize\\setlength{\\tabcolsep}{3.5pt}\\begin{longtable}{@{}lrrrrrrrrrrrrrrr@{}}\\toprule")
    C.append("TB45D & $n{=}1$ & $2$ & $3$ & $4$ & all & U & C & S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8\\\\\\midrule\\endhead")
    for key in sorted(combos, key=lambda k: (-sum(ch != '-' for ch in k), k)):
        fs = combos[key]
        cnt = [sum(1 for f in fs if f["n"] == n) for n in range(1, NMAX + 1)]
        u = sum(1 for f in fs if f["c"]["U"])
        cc = sum(1 for f in fs if f["c"]["C"])
        vals = [sum(1 for f in fs if f["v"][s]) for s in SCHEMAS]
        C.append("\\texttt{" + tex_tt(key) + "} & " + " & ".join(map(str, cnt)) + f" & {len(fs)} & {u} & {cc} & "
                 + " & ".join(map(str, vals)) + "\\\\")
    C.append("\\bottomrule\\end{longtable}}")
    open(os.path.join(HERE, "counts.tex"), "w").write("\n".join(C) + "\n")

    # ---- statistics macros
    def cnt(pred):
        return sum(1 for f in frames if pred(f))
    st = {
        "Total": total,
        "NOne": by_n[1], "NTwo": by_n[2], "NThree": by_n[3], "NFour": by_n[4],
        "NumB": cnt(lambda f: f["c"]["B"]),
        "NumC": cnt(lambda f: f["c"]["C"]),
        "NumU": cnt(lambda f: f["c"]["U"]),
        "NumFive": cnt(lambda f: f["c"]["5"]),
        "NumFour": cnt(lambda f: f["c"]["4"]),
        "NumSFive": cnt(lambda f: f["c"]["T"] and f["c"]["B"] and f["c"]["4"]),
        "NumCnotB": cnt(lambda f: f["c"]["C"] and not f["c"]["B"]),
        "NumUnotFive": cnt(lambda f: f["c"]["U"] and not f["c"]["5"]),
        "NumBnotU": cnt(lambda f: f["c"]["B"] and not f["c"]["U"]),
        "NumBnotFour": cnt(lambda f: f["c"]["B"] and not f["c"]["4"]),
        "NumSOneNotSThree": cnt(lambda f: f["v"]["S1"] and not f["v"]["S3"]),
        "NumSThreeNotSOne": cnt(lambda f: f["v"]["S3"] and not f["v"]["S1"]),
        "NumArgStar": cnt(lambda f: f["v"]["S5"] and f["v"]["S6"]),
        "NumArgOrig": cnt(lambda f: f["v"]["S1"] and f["v"]["S3"]),
        "NumSSeven": cnt(lambda f: f["v"]["S7"]),
        "NumSEight": cnt(lambda f: f["v"]["S8"]),
        "NumBnotSSeven": cnt(lambda f: f["c"]["B"] and not f["v"]["S7"]),
        "NumBnotSEight": cnt(lambda f: f["c"]["B"] and not f["v"]["S8"]),
        "NumCnotSEight": cnt(lambda f: f["c"]["C"] and not f["v"]["S8"]),
        "Checks": total * len(SCHEMAS) * 2,
        "Valuations": sum((1 << f["n"]) for f in frames),
        "QValuations": sum((1 << (2 * f["n"])) for f in frames),
    }
    with open(os.path.join(HERE, "stats.tex"), "w") as fh:
        fh.write("% generated by gen/generate.py -- do not edit\n")
        for k, v in st.items():
            fh.write(f"\\newcommand{{\\st{k}}}{{{v:,}}}\n".replace(",", "{,}"))
    for k, v in st.items():
        print(k, v)
    for name, res in sysres.items():
        print(name, res)


def tex_tt(s):
    out = []
    for ch in s:
        if ch == " ":
            out.append("~")
        elif ch in "#$%&_{}":
            out.append("\\" + ch)
        elif ch == "'":
            out.append("\\textquotesingle{}")
        elif ch == "-":
            out.append("-{}")
        elif ch == "*":
            out.append("*")
        else:
            out.append(ch)
    return "".join(out)


if __name__ == "__main__":
    main()
