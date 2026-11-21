"""A checker for labelled natural deduction in second-order modal logic (K plus relational rules).

Lines are ('at', w, phi) -- phi holds at world label w -- or ('R', w, v) -- v is accessible from w.
Each derivation line is a dict {f: line, rule: name, refs: [...], term/eigen: ...}.
Dependencies are computed in the style of Lemmon: every line depends on a set of assumption lines.

Formulas:
  ('bot',)  ('app', T, x)  ('pos', T)  ('not', A)  ('and', A, B)  ('or', A, B)  ('imp', A, B)  ('iff', A, B)
  ('all', x, A)  ('ex', x, A)  ('allp', Y, A)  ('exp', Y, A)  ('box', A)  ('dia', A)
  ('ess', T, x)  ('essS', T, x)                                 [defined]
Property terms: ('pv', Y)  ('pc', name)  ('lam', x, A)          [name in DEFS: defined constants]
Individual variables are strings; property variables are strings.
"""
import itertools

# ---------------------------------------------------------------- syntax utilities
QI = ("all", "ex")
QP = ("allp", "exp")


def fv_ind(A):
    t = A[0]
    if t == "bot":
        return set()
    if t == "app":
        return fv_term_ind(A[1]) | {A[2]}
    if t == "pos":
        return fv_term_ind(A[1])
    if t in ("ess", "essS"):
        return fv_term_ind(A[1]) | {A[2]}
    if t in ("not", "box", "dia"):
        return fv_ind(A[1])
    if t in ("and", "or", "imp", "iff"):
        return fv_ind(A[1]) | fv_ind(A[2])
    if t in QI:
        return fv_ind(A[2]) - {A[1]}
    if t in QP:
        return fv_ind(A[2])
    raise ValueError(A)


def fv_term_ind(T):
    if T[0] == "lam":
        return fv_ind(T[2]) - {T[1]}
    return set()


def fv_prop(A):
    t = A[0]
    if t == "bot":
        return set()
    if t == "app" or t == "pos" or t in ("ess", "essS"):
        return fv_term_prop(A[1])
    if t in ("not", "box", "dia"):
        return fv_prop(A[1])
    if t in ("and", "or", "imp", "iff"):
        return fv_prop(A[1]) | fv_prop(A[2])
    if t in QI:
        return fv_prop(A[2])
    if t in QP:
        return fv_prop(A[2]) - {A[1]}
    raise ValueError(A)


def fv_term_prop(T):
    if T[0] == "pv":
        return {T[1]}
    if T[0] == "lam":
        return fv_prop(T[2])
    return set()


_counter = itertools.count()


def fresh(base, avoid):
    i = 0
    while True:
        c = f"{base}{i}"
        if c not in avoid:
            return c
        i += 1


def subst_ind(A, x, y):
    """replace free individual variable x by variable y (capture-avoiding)"""
    t = A[0]
    if t == "bot":
        return A
    if t == "app":
        return ("app", subst_term_ind(A[1], x, y), y if A[2] == x else A[2])
    if t == "pos":
        return ("pos", subst_term_ind(A[1], x, y))
    if t in ("ess", "essS"):
        return (t, subst_term_ind(A[1], x, y), y if A[2] == x else A[2])
    if t in ("not", "box", "dia"):
        return (t, subst_ind(A[1], x, y))
    if t in ("and", "or", "imp", "iff"):
        return (t, subst_ind(A[1], x, y), subst_ind(A[2], x, y))
    if t in QI:
        b, body = A[1], A[2]
        if b == x:
            return A
        if b == y:
            nb = fresh("v_", fv_ind(body) | {x, y})
            body = subst_ind(body, b, nb)
            b = nb
        return (t, b, subst_ind(body, x, y))
    if t in QP:
        return (t, A[1], subst_ind(A[2], x, y))
    raise ValueError(A)


def subst_term_ind(T, x, y):
    if T[0] == "lam":
        b, body = T[1], T[2]
        if b == x:
            return T
        if b == y:
            nb = fresh("v_", fv_ind(body) | {x, y})
            body = subst_ind(body, b, nb)
            b = nb
        return ("lam", b, subst_ind(body, x, y))
    return T


def subst_prop(A, Y, S):
    """replace free property variable Y by property term S (capture-avoiding)"""
    t = A[0]
    if t == "bot":
        return A
    if t in ("app",):
        return ("app", subst_term_prop(A[1], Y, S), A[2])
    if t in ("ess", "essS"):
        return (t, subst_term_prop(A[1], Y, S), A[2])
    if t == "pos":
        return ("pos", subst_term_prop(A[1], Y, S))
    if t in ("not", "box", "dia"):
        return (t, subst_prop(A[1], Y, S))
    if t in ("and", "or", "imp", "iff"):
        return (t, subst_prop(A[1], Y, S), subst_prop(A[2], Y, S))
    if t in QI:
        b, body = A[1], A[2]
        if b in fv_term_ind(S):
            nb = fresh("v_", fv_ind(body) | fv_term_ind(S) | {b})
            body = subst_ind(body, b, nb)
            b = nb
        return (t, b, subst_prop(body, Y, S))
    if t in QP:
        b, body = A[1], A[2]
        if b == Y:
            return A
        if b in fv_term_prop(S):
            nb = fresh("V_", fv_prop(body) | fv_term_prop(S) | {b})
            body = subst_prop(body, b, ("pv", nb))
            b = nb
        return (t, b, subst_prop(body, Y, S))
    raise ValueError(A)


def subst_term_prop(T, Y, S):
    if T[0] == "pv":
        return S if T[1] == Y else T
    if T[0] == "lam":
        b, body = T[1], T[2]
        if b in fv_term_ind(S):
            nb = fresh("v_", fv_ind(body) | fv_term_ind(S) | {b})
            body = subst_ind(body, b, nb)
            b = nb
        return ("lam", b, subst_prop(body, Y, S))
    return T


def beta(A):
    t = A[0]
    if t == "bot":
        return A
    if t == "app":
        T = beta_term(A[1])
        if T[0] == "lam":
            return beta(subst_ind(T[2], T[1], A[2]))
        return ("app", T, A[2])
    if t == "pos":
        return ("pos", beta_term(A[1]))
    if t in ("ess", "essS"):
        return (t, beta_term(A[1]), A[2])
    if t in ("not", "box", "dia"):
        return (t, beta(A[1]))
    if t in ("and", "or", "imp", "iff"):
        return (t, beta(A[1]), beta(A[2]))
    if t in QI or t in QP:
        return (t, A[1], beta(A[2]))
    raise ValueError(A)


def beta_term(T):
    if T[0] == "lam":
        return ("lam", T[1], beta(T[2]))
    return T


def unfold(A, defs):
    """unfold every defined constant and defined predicate (definitions are not recursive)"""
    t = A[0]
    if t == "bot":
        return A
    if t == "app":
        return ("app", unfold_term(A[1], defs), A[2])
    if t == "pos":
        return ("pos", unfold_term(A[1], defs))
    if t in ("ess", "essS"):
        T = unfold_term(A[1], defs)
        Yv, xv, body = defs[t]
        B = subst_prop(subst_ind(body, xv, A[2]), Yv, T)
        return unfold(B, defs)
    if t in ("not", "box", "dia"):
        return (t, unfold(A[1], defs))
    if t in ("and", "or", "imp", "iff"):
        return (t, unfold(A[1], defs), unfold(A[2], defs))
    if t in QI or t in QP:
        return (t, A[1], unfold(A[2], defs))
    raise ValueError(A)


def unfold_term(T, defs):
    if T[0] == "pc":
        return unfold_term(defs[T[1]], defs)
    if T[0] == "lam":
        return ("lam", T[1], unfold(T[2], defs))
    return T


def alpha(A, ienv=None, penv=None, depth=None):
    """canonical renaming of bound variables"""
    ienv = ienv or {}
    penv = penv or {}
    depth = depth or [0]
    t = A[0]
    if t == "bot":
        return A
    if t == "app":
        return ("app", alpha_term(A[1], ienv, penv, depth), ienv.get(A[2], A[2]))
    if t == "pos":
        return ("pos", alpha_term(A[1], ienv, penv, depth))
    if t in ("ess", "essS"):
        return (t, alpha_term(A[1], ienv, penv, depth), ienv.get(A[2], A[2]))
    if t in ("not", "box", "dia"):
        return (t, alpha(A[1], ienv, penv, depth))
    if t in ("and", "or", "imp", "iff"):
        return (t, alpha(A[1], ienv, penv, depth), alpha(A[2], ienv, penv, depth))
    if t in QI:
        depth[0] += 1
        nb = f"#i{depth[0]}"
        e = dict(ienv)
        e[A[1]] = nb
        return (t, nb, alpha(A[2], e, penv, depth))
    if t in QP:
        depth[0] += 1
        nb = f"#p{depth[0]}"
        e = dict(penv)
        e[A[1]] = nb
        return (t, nb, alpha(A[2], ienv, e, depth))
    raise ValueError(A)


def alpha_term(T, ienv, penv, depth):
    if T[0] == "pv":
        return ("pv", penv.get(T[1], T[1]))
    if T[0] == "lam":
        depth[0] += 1
        nb = f"#i{depth[0]}"
        e = dict(ienv)
        e[T[1]] = nb
        return ("lam", nb, alpha(T[2], e, penv, depth))
    return T


def nf(A):
    return alpha(beta(A))


def nf_def(A, defs):
    return alpha(beta(unfold(A, defs)))


# ---------------------------------------------------------------- comprehension
def comprehension_ok(T):
    """property terms admissible in the finite models: variables, defined constants, and lambda terms whose
    body is built from atoms, Boolean connectives, boxes, diamonds and individual quantifiers, with at most
    one free individual variable in every subformula (no positivity, no property quantifier, no essence)."""
    if T[0] in ("pv", "pc"):
        return True
    ok = [True]

    def walk(A):
        t = A[0]
        if len(fv_ind(A)) > 1:
            ok[0] = False
        if t in ("pos", "allp", "exp", "ess", "essS"):
            ok[0] = False
            return
        if t == "app":
            if A[1][0] == "lam":
                ok[0] = False
            return
        if t == "bot":
            return
        if t in ("not", "box", "dia"):
            walk(A[1])
        elif t in ("and", "or", "imp", "iff"):
            walk(A[1])
            walk(A[2])
        elif t in QI:
            walk(A[2])
    walk(T[2])
    return ok[0]


# ---------------------------------------------------------------- checker
class Fail(Exception):
    pass


def labels_of(line):
    if line[0] == "R":
        return {line[1], line[2]}
    return {line[1]}


def free_ind_line(line):
    return fv_ind(line[2]) if line[0] == "at" else set()


def free_prop_line(line):
    return fv_prop(line[2]) if line[0] == "at" else set()


def check(lines, axioms, defs):
    deps = []
    used_rel = set()
    used_ax = set()
    res = {"ok": True, "error": None}
    try:
        for i, L in enumerate(lines):
            f = L["f"]
            r = L["rule"]
            refs = [k - 1 for k in L.get("refs", [])]
            for k in refs:
                if k < 0 or k >= i:
                    raise Fail(f"line {i+1}: bad reference {k+1}")
            g = lambda k: lines[k]["f"]

            def need(cond, msg):
                if not cond:
                    raise Fail(f"line {i+1} ({r}): {msg}")

            def at(line):
                need(line[0] == "at", "expected a labelled formula")
                return line[1], line[2]

            def eq(A, B):
                return nf(A) == nf(B)

            D = set()
            if r == "A":
                D = {i}
            elif r == "Ax":
                name = L["name"]
                need(name in axioms, "unknown axiom")
                w, A = at(f)
                need(eq(A, axioms[name]), "not the axiom " + name)
                used_ax.add(name)
            elif r == "Def":
                (j,) = refs
                w1, A1 = at(g(j))
                w2, A2 = at(f)
                need(w1 == w2, "label changed")
                need(nf_def(A1, defs) == nf_def(A2, defs), "not definitionally equal")
                D = deps[j]
            elif r == "AndI":
                j, k = refs
                w1, A1 = at(g(j))
                w2, A2 = at(g(k))
                w, A = at(f)
                need(w == w1 == w2 and A[0] == "and" and eq(A[1], A1) and eq(A[2], A2), "bad conjunction")
                D = deps[j] | deps[k]
            elif r == "AndE":
                (j,) = refs
                w1, A1 = at(g(j))
                w, A = at(f)
                need(w == w1 and A1[0] == "and" and (eq(A, A1[1]) or eq(A, A1[2])), "bad conjunct")
                D = deps[j]
            elif r == "OrI":
                (j,) = refs
                w1, A1 = at(g(j))
                w, A = at(f)
                need(w == w1 and A[0] == "or" and (eq(A[1], A1) or eq(A[2], A1)), "bad disjunct")
                D = deps[j]
            elif r == "ImpI":
                a, k = refs
                need(lines[a]["rule"] == "A", "discharged line is not an assumption")
                w1, A1 = at(g(a))
                w2, A2 = at(g(k))
                w, A = at(f)
                need(w == w1 == w2 and A[0] == "imp" and eq(A[1], A1) and eq(A[2], A2), "bad implication")
                D = deps[k] - {a}
            elif r == "ImpE":
                j, k = refs
                w1, A1 = at(g(j))
                w2, A2 = at(g(k))
                w, A = at(f)
                need(w == w1 == w2 and A1[0] == "imp" and eq(A1[1], A2) and eq(A1[2], A), "bad modus ponens")
                D = deps[j] | deps[k]
            elif r == "IffI":
                j, k = refs
                w1, A1 = at(g(j))
                w2, A2 = at(g(k))
                w, A = at(f)
                need(w == w1 == w2 and A[0] == "iff" and A1[0] == "imp" and A2[0] == "imp", "bad biconditional")
                need(eq(A1[1], A[1]) and eq(A1[2], A[2]) and eq(A2[1], A[2]) and eq(A2[2], A[1]), "bad sides")
                D = deps[j] | deps[k]
            elif r == "IffE":
                j, k = refs
                w1, A1 = at(g(j))
                w2, A2 = at(g(k))
                w, A = at(f)
                need(w == w1 == w2 and A1[0] == "iff", "not a biconditional")
                need((eq(A1[1], A2) and eq(A1[2], A)) or (eq(A1[2], A2) and eq(A1[1], A)), "bad sides")
                D = deps[j] | deps[k]
            elif r == "NotE":
                j, k = refs
                w1, A1 = at(g(j))
                w2, A2 = at(g(k))
                w, A = at(f)
                need(w == w1 == w2 and A == ("bot",), "conclusion must be falsum at the same label")
                need((A2[0] == "not" and eq(A2[1], A1)) or (A1[0] == "not" and eq(A1[1], A2)), "not contradictory")
                D = deps[j] | deps[k]
            elif r == "NotI":
                a, k = refs
                need(lines[a]["rule"] == "A", "discharged line is not an assumption")
                w1, A1 = at(g(a))
                w2, A2 = at(g(k))
                w, A = at(f)
                need(A2 == ("bot",) and w == w1 and A[0] == "not" and eq(A[1], A1), "bad negation introduction")
                D = deps[k] - {a}
            elif r == "RAA":
                a, k = refs
                need(lines[a]["rule"] == "A", "discharged line is not an assumption")
                w1, A1 = at(g(a))
                w2, A2 = at(g(k))
                w, A = at(f)
                need(A2 == ("bot",) and w == w1 and A1[0] == "not" and eq(A1[1], A), "bad reductio")
                D = deps[k] - {a}
            elif r == "EFQ":
                (j,) = refs
                w1, A1 = at(g(j))
                need(A1 == ("bot",), "not falsum")
                D = deps[j]
            elif r in ("AllI", "AllpI"):
                (j,) = refs
                w1, A1 = at(g(j))
                w, A = at(f)
                need(w == w1 and A[0] == ("all" if r == "AllI" else "allp"), "bad universal")
                e = L["eigen"]
                inst = subst_ind(A[2], A[1], e) if r == "AllI" else subst_prop(A[2], A[1], ("pv", e))
                need(eq(inst, A1), "premise is not an instance with the eigenvariable")
                fv = free_ind_line if r == "AllI" else free_prop_line
                for d in deps[j]:
                    need(e not in fv(lines[d]["f"]), f"eigenvariable {e} free in assumption {d+1}")
                need(e not in fv(f), "eigenvariable free in conclusion")
                D = deps[j]
            elif r in ("AllE", "AllpE"):
                (j,) = refs
                w1, A1 = at(g(j))
                w, A = at(f)
                need(w == w1 and A1[0] == ("all" if r == "AllE" else "allp"), "not a universal")
                if r == "AllE":
                    inst = subst_ind(A1[2], A1[1], L["term"])
                else:
                    need(comprehension_ok(L["term"]), "inadmissible comprehension term")
                    inst = subst_prop(A1[2], A1[1], L["term"])
                need(eq(inst, A), "not the instance")
                D = deps[j]
            elif r in ("ExI", "ExpI"):
                (j,) = refs
                w1, A1 = at(g(j))
                w, A = at(f)
                need(w == w1 and A[0] == ("ex" if r == "ExI" else "exp"), "not an existential")
                if r == "ExI":
                    inst = subst_ind(A[2], A[1], L["term"])
                else:
                    need(comprehension_ok(L["term"]), "inadmissible comprehension term")
                    inst = subst_prop(A[2], A[1], L["term"])
                need(eq(inst, A1), "premise is not the instance")
                D = deps[j]
            elif r in ("ExE", "ExpE"):
                j, a, k = refs
                need(lines[a]["rule"] == "A", "discharged line is not an assumption")
                w1, A1 = at(g(j))
                wa, Aa = at(g(a))
                need(A1[0] == ("ex" if r == "ExE" else "exp") and wa == w1, "not an existential")
                e = L["eigen"]
                inst = subst_ind(A1[2], A1[1], e) if r == "ExE" else subst_prop(A1[2], A1[1], ("pv", e))
                need(eq(inst, Aa), "assumption is not the instance")
                need(g(k) == f, "conclusion differs from the cited line")
                fv = free_ind_line if r == "ExE" else free_prop_line
                need(e not in fv(f), "eigenvariable free in conclusion")
                need(e not in fv(g(j)), "eigenvariable free in the existential")
                for d in (deps[k] - {a}) | deps[j]:
                    need(e not in fv(lines[d]["f"]), f"eigenvariable {e} free in assumption {d+1}")
                D = (deps[k] - {a}) | deps[j]
            elif r == "BoxI":
                a, k = refs
                need(lines[a]["rule"] == "A" and g(a)[0] == "R", "discharged line is not an accessibility assumption")
                _, w0, v = g(a)
                w2, A2 = at(g(k))
                w, A = at(f)
                need(w == w0 and w2 == v and v != w and A[0] == "box" and eq(A[1], A2), "bad box introduction")
                for d in deps[k] - {a}:
                    need(v not in labels_of(lines[d]["f"]), f"label {v} occurs in assumption {d+1}")
                D = deps[k] - {a}
            elif r == "BoxE":
                j, k = refs
                w1, A1 = at(g(j))
                need(g(k)[0] == "R" and g(k)[1] == w1, "no accessibility from the label")
                w, A = at(f)
                need(A1[0] == "box" and w == g(k)[2] and eq(A1[1], A), "bad box elimination")
                D = deps[j] | deps[k]
            elif r == "DiaI":
                j, k = refs
                need(g(j)[0] == "R", "first reference must be accessibility")
                _, w0, v = g(j)
                w2, A2 = at(g(k))
                w, A = at(f)
                need(w == w0 and w2 == v and A[0] == "dia" and eq(A[1], A2), "bad diamond introduction")
                D = deps[j] | deps[k]
            elif r == "DiaE":
                j, a1, a2, k = refs
                w1, A1 = at(g(j))
                need(A1[0] == "dia", "not a diamond")
                need(lines[a1]["rule"] == "A" and lines[a2]["rule"] == "A", "discharged lines must be assumptions")
                need(g(a1)[0] == "R" and g(a1)[1] == w1, "bad accessibility assumption")
                v = g(a1)[2]
                wa, Aa = at(g(a2))
                need(wa == v and v != w1 and eq(Aa, A1[1]), "bad witness assumption")
                need(g(k) == f, "conclusion differs from the cited line")
                need(v not in labels_of(f), "witness label in conclusion")
                for d in (deps[k] - {a1, a2}) | deps[j]:
                    need(v not in labels_of(lines[d]["f"]), f"label {v} occurs in assumption {d+1}")
                D = (deps[k] - {a1, a2}) | deps[j]
            elif r == "Sym":
                (j,) = refs
                need(g(j)[0] == "R" and f == ("R", g(j)[2], g(j)[1]), "bad symmetry step")
                used_rel.add("Sym")
                D = deps[j]
            elif r == "Rel":
                (j,) = refs
                need(not deps[j], "relabelling is allowed only for lines that depend on nothing")
                w1, A1 = at(g(j))
                w, A = at(f)
                need(eq(A, A1), "relabelling changed the formula")
            elif r == "Refl":
                need(f[0] == "R" and f[1] == f[2], "bad reflexivity step")
                used_rel.add("Refl")
            elif r == "Trans":
                j, k = refs
                need(g(j)[0] == "R" and g(k)[0] == "R" and g(j)[2] == g(k)[1] and f == ("R", g(j)[1], g(k)[2]),
                     "bad transitivity step")
                used_rel.add("Trans")
                D = deps[j] | deps[k]
            else:
                raise Fail(f"line {i+1}: unknown rule {r}")
            deps.append(frozenset(D))
    except Fail as e:
        res["ok"] = False
        res["error"] = str(e)
        return res
    res["deps"] = deps
    res["open"] = sorted(d + 1 for d in deps[-1])
    res["relrules"] = sorted(used_rel)
    res["axioms"] = sorted(used_ax)
    res["nlines"] = len(lines)
    res["nrules"] = len(set(L["rule"] for L in lines))
    return res


# ---------------------------------------------------------------- typesetting
CONST_TEX = {"G": "G", "NE": "\\mathit{NE}", "GS": "G_{\\!S}", "NES": "\\mathit{NE}_{\\!S}"}
LABEL_TEX = {"@": "@"}
RULE_TEX = {
    "A": "A", "Ax": "Ax", "Def": "Def", "AndI": "$\\wedge$I", "AndE": "$\\wedge$E", "OrI": "$\\vee$I",
    "ImpI": "$\\to$I", "ImpE": "$\\to$E", "IffI": "$\\leftrightarrow$I", "IffE": "$\\leftrightarrow$E",
    "NotI": "$\\neg$I", "NotE": "$\\neg$E", "RAA": "RAA", "EFQ": "EFQ", "AllI": "$\\forall$I",
    "AllE": "$\\forall$E", "AllpI": "$\\forall^2$I", "AllpE": "$\\forall^2$E", "ExI": "$\\exists$I",
    "ExE": "$\\exists$E", "ExpI": "$\\exists^2$I", "ExpE": "$\\exists^2$E", "BoxI": "$\\Box$I",
    "BoxE": "$\\Box$E", "DiaI": "$\\Diamond$I", "DiaE": "$\\Diamond$E", "Sym": "Sym", "Rel": "Rel", "Refl": "Refl",
    "Trans": "Trans",
}


def tex_term(T):
    if T[0] == "pv":
        return T[1]
    if T[0] == "pc":
        return CONST_TEX[T[1]]
    return f"\\lambda {T[1]}.\\,{tex(T[2], 0)}"


def tex_term_app(T):
    s = tex_term(T)
    return f"({s})" if T[0] == "lam" else s


PREC = {"iff": 1, "imp": 2, "or": 3, "and": 4}


def tex(A, ctx=0):
    t = A[0]
    if t == "bot":
        return "\\bot"
    if t == "app":
        return f"{tex_term_app(A[1])}({A[2]})"
    if t == "pos":
        return f"\\mathcal{{P}}({tex_term(A[1])})"
    if t == "ess":
        return f"\\mathrm{{Ess}}({tex_term(A[1])},{A[2]})"
    if t == "essS":
        return f"\\mathrm{{Ess}}_S({tex_term(A[1])},{A[2]})"
    if t == "not":
        return "\\neg " + tex(A[1], 9)
    if t == "box":
        return "\\Box " + tex(A[1], 9)
    if t == "dia":
        return "\\Diamond " + tex(A[1], 9)
    if t in PREC:
        op = {"iff": "\\leftrightarrow", "imp": "\\to", "or": "\\vee", "and": "\\wedge"}[t]
        p = PREC[t]
        s = f"{tex(A[1], p + 1)} {op} {tex(A[2], p + 1 if t != 'imp' else p)}"
        return f"({s})" if ctx > p else s
    if t in ("all", "allp"):
        return f"\\forall {A[1]}\\, {tex(A[2], 9)}"
    if t in ("ex", "exp"):
        return f"\\exists {A[1]}\\, {tex(A[2], 9)}"
    raise ValueError(A)


def tex_line(f):
    if f[0] == "R":
        return f"${f[1]}\\,R\\,{f[2]}$"
    return f"${f[1]}:\\ {tex(f[2])}$"


def typeset(lines, res, defs):
    out = ["% generated by gen/generate.py from gen/derivations.py; every line checked by gen/nd.py",
           "{\\footnotesize\\setlength{\\tabcolsep}{4pt}",
           "\\begin{longtable}{@{}r>{\\raggedright}p{0.12\\textwidth}p{0.55\\textwidth}>{\\raggedright\\arraybackslash}p{0.21\\textwidth}@{}}\\toprule",
           "no. & depends on & line & rule\\\\\\midrule\\endhead"]
    for i, L in enumerate(lines):
        dep = ",".join(str(d + 1) for d in sorted(res["deps"][i])) or "--"
        rr = RULE_TEX[L["rule"]]
        extra = []
        if L["rule"] == "Ax":
            rr += " " + L["name"]
        if L.get("refs"):
            extra.append(",".join(str(k) for k in L["refs"]))
        if "term" in L:
            T = L["term"]
            extra.append(f"$[{tex_term(T) if isinstance(T, tuple) else T}]$")
        if "eigen" in L:
            extra.append(f"$({L['eigen']})$")
        cell = rr + (" " + " ".join(extra) if extra else "")
        note = L.get("note")
        out.append(f"{i+1} & {dep} & {tex_line(L['f'])}" + (f" \\hfill{{\\itshape {note}}}" if note else "")
                   + f" & {cell}\\\\")
    out.append("\\bottomrule\\end{longtable}}")
    return "\n".join(out) + "\n"
