#!/usr/bin/env python3
"""Generator for ETH-12-a, Appendices A-C.

Implements the criterion of right action of Sections 3-7 (Definitions 3.1-3.15, Principle P1),
computes the concordance of virtues (Appendix A), the verdicts on the test cases
(Appendix B), and the mechanical checks (Appendix C). Python 3 standard library
only; deterministic. Every check is an assertion: a failure raises AssertionError
naming the check and the case.
"""
import itertools
import os
import re
from fractions import Fraction as Fr

OUT = os.path.dirname(os.path.abspath(__file__))

# ---------------------------------------------------------------- constants
GOODS = "WKARFBU"          # ETH-01: well-being, knowledge, achievement,
                           # relationships, fairness, beauty, autonomy
RHO = 3                    # respect multiplier (Definition 3.6, Assumption 3.7)
PI = 2                     # honor (partiality) multiplier (Definition 3.6)
GAMMA = 8                  # gravity threshold (Definition 3.10, Assumption 3.7)
M = 3                      # decency bound of the prerogative (Definitions 3.6, 3.13)


def fmt(x):
    x = Fr(x)
    if x.denominator == 1:
        return str(x.numerator)
    return f"{x.numerator}/{x.denominator}"


def tex(s):
    return (s.replace("\\", "\\textbackslash{}").replace("&", "\\&").replace("%", "\\%")
             .replace("_", "\\_").replace("#", "\\#").replace("{", "\\{").replace("}", "\\}")
             .replace("~", "\\textasciitilde{}").replace("^", "\\^{}"))


# ---------------------------------------------------------------- situations
class Eff:
    __slots__ = ("p", "n", "g", "d", "role", "tag", "consent")

    def __init__(self, p, g, d, role="a", tag="", n=1, consent=False):
        assert g in GOODS and role in "ira"
        self.p, self.n, self.g, self.d = p, n, g, Fr(d)
        self.role, self.tag, self.consent = role, tag, consent

    def code(self):
        s = self.p + (str(self.n) if self.n > 1 else "") + ":" + self.g
        s += ("+" if self.d > 0 else "") + fmt(self.d) + self.role
        if self.tag:
            s += "." + self.tag
        if self.consent:
            s += "c"
        return s


class Sit:
    def __init__(self, cid, schema, persons, options, params="", source="", title=""):
        # persons: name -> rel in {'self','close','str','agg'}
        self.id, self.schema, self.persons = cid, schema, persons
        self.options = options          # list of (name, [Eff])
        self.params, self.source, self.title = params, source, title
        self.persons.setdefault("a", "self")
        for _, effs in options:
            for e in effs:
                assert e.p in self.persons, (cid, e.p)

    def opt(self, name):
        return dict(self.options)[name]

    def names(self):
        return [o for o, _ in self.options]

    def profile(self):
        rl = {"close": "c", "str": "s", "agg": "g"}
        head = "[" + " ".join(f"{p}={rl[r]}" for p, r in sorted(self.persons.items()) if r != "self") + "] "
        return head + "; ".join(o + ": " + (" ".join(e.code() for e in effs) if effs else "--")
                         for o, effs in self.options)


def rel(s, p):
    return s.persons[p]


def is_other(s, p):
    return rel(s, p) in ("close", "str")


def tot(s, o, p):
    return sum(e.d for e in s.opt(o) if e.p == p)


def weight(s, e, lam, tagw=None):
    r = rel(s, e.p)
    if r == "self":
        w = Fr(lam)
        if tagw and e.tag in tagw:
            w = w * tagw[e.tag]
        return w
    if r == "agg":
        return Fr(1)
    w = Fr(1)
    if r == "close":
        w *= PI
    if e.d < 0 and e.role == "i" and not e.consent:
        w *= RHO
    return w


def value(s, o, lam, tagw=None):
    return sum(e.n * weight(s, e, lam, tagw) * e.d for e in s.opt(o))


def selfpart(s, o):
    return sum(e.n * e.d for e in s.opt(o) if rel(s, e.p) == "self")


def silenced(s, o):
    """Definition 3.10: persons on whom o imposes a grave, unconsented setback in W or U
    that they would not suffer on some alternative."""
    out = set()
    for e in s.opt(o):
        if (is_other(s, e.p) and e.role == "i" and e.d <= -GAMMA and e.g in "WU"
                and not e.consent):
            if any(tot(s, o2, e.p) > tot(s, o, e.p) for o2 in s.names() if o2 != o):
                out.add((e.p, e.n))
    return sum(n for _, n in out)


def doing(s, o):
    """Definition 3.10: number of non-aggressor others set back by the agent's doing."""
    ps = {}
    for e in s.opt(o):
        if is_other(s, e.p) and e.d < 0 and e.role in "ir":
            ps[e.p] = e.n
    return sum(ps.values())


def infringes(s, o):
    """Definition 3.11 (infringement)."""
    for e in s.opt(o):
        if is_other(s, e.p) and e.d < 0 and e.role in "ir" and not e.consent:
            return True
        if is_other(s, e.p) and e.d <= -GAMMA and e.role == "a":
            if any(tot(s, o2, e.p) > tot(s, o, e.p) for o2 in s.names() if o2 != o):
                return True
    return False


def imposes(s, o):
    """Clause (i) of Definition 3.11: o sets back another, not an aggressor, by an
    imposed or redirected effect without consent."""
    return any(is_other(s, e.p) and e.d < 0 and e.role in "ir" and not e.consent
               for e in s.opt(o))


def impartial_only(s):
    """Definition 3.13: the prerogative is idle in an apparent dilemma and wherever
    some option imposes or redirects a setback on another."""
    return apparent_dilemma(s) or any(imposes(s, o) for o in s.names())


def apparent_dilemma(s):
    return all(infringes(s, o) for o in s.names())


def lam_samples(s, cands):
    lines = {o: (value(s, o, 0), selfpart(s, o)) for o in cands}
    pts = {Fr(1), Fr(M)}
    for o1, o2 in itertools.combinations(cands, 2):
        (x1, y1), (x2, y2) = lines[o1], lines[o2]
        if y1 != y2:
            l = (x2 - x1) / (y1 - y2)
            if 1 < l < M:
                pts.add(l)
    pts = sorted(pts)
    mids = [(a + b) / 2 for a, b in zip(pts, pts[1:])]
    return sorted(set(pts) | set(mids))


def choose_at(s, cands, lam, tagw=None, lottery=False):
    best = max(value(s, o, lam, tagw) for o in cands)
    A = [o for o in cands if value(s, o, lam, tagw) == best]
    dmin = min(doing(s, o) for o in A)
    A = [o for o in A if doing(s, o) == dmin]
    if lottery and len(A) > 1:
        return ["lot(" + ", ".join(A) + ")"]
    return A


def characteristic(s, lams=None, tagw=None):
    """Definition 3.13: the characteristic set C(s) (computed by Lemma 5.1)."""
    smin = min(silenced(s, o) for o in s.names())
    O1 = [o for o in s.names() if silenced(s, o) == smin]
    ad = apparent_dilemma(s)
    if lams is None:
        lams = [Fr(1)] if impartial_only(s) else lam_samples(s, O1)
    out = []
    for l in lams:
        for o in choose_at(s, O1, l, tagw, lottery=ad):
            if o not in out:
                out.append(o)
    order = {o: i for i, o in enumerate(s.names())}
    out.sort(key=lambda o: order.get(o, len(order)))
    return out


def decent(s):
    """C at the decency bound lambda = M (or lambda = 1 in an apparent dilemma)."""
    return characteristic(s, lams=[Fr(1)] if impartial_only(s) else [Fr(M)])


def agent_choice(s, lam, tagw=None):
    """A fixed-weight agent (used for vicious agents): no range, same structure."""
    return characteristic(s, lams=[Fr(lam)], tagw=tagw)


def consequentialist(s):
    vals = {o: sum(e.n * e.d for e in effs) for o, effs in s.options}
    b = max(vals.values())
    return [o for o in s.names() if vals[o] == b]


def deont_forbidden(s, o):
    for e in s.opt(o):
        if e.d < 0 and e.role == "i" and rel(s, e.p) != "self" and not e.consent:
            if e.tag in ("dec", "prm"):
                return True
            if e.tag == "harm" and rel(s, e.p) != "agg":
                return True
    return False


def deontological(s):
    ok = [o for o in s.names() if not deont_forbidden(s, o)]
    if not ok:
        return []
    vals = {o: sum(e.n * e.d for e in s.opt(o)) for o in ok}
    b = max(vals.values())
    return [o for o in ok if vals[o] == b]


# ---------------------------------------------------------------- v-rule scorers
SCORERS = ["Be", "Ju", "Ho", "Fi", "Se"]
SCORER_NAMES = {"Be": "benevolence", "Ju": "justice", "Ho": "honesty",
                "Fi": "fidelity", "Se": "the self-regarding virtues"}


def scorer_of(s, e):
    r = rel(s, e.p)
    if r == "self":
        return "Se"
    if e.tag == "dec":
        return "Ho"
    if e.tag == "prm":
        return "Fi"
    if e.d < 0 and e.role in "ir":
        return "Ju"
    return "Be"


def score(s, o, v):
    sc = sum(e.n * weight(s, e, 1) * e.d for e in s.opt(o) if scorer_of(s, e) == v)
    if v == "Ju":
        return (-silenced(s, o), sc)
    return (sc,)


def engaged(s):
    return sorted({scorer_of(s, e) for _, effs in s.options for e in effs},
                  key=SCORERS.index)


def lexical(s, order):
    key = lambda o: tuple(x for v in order for x in score(s, o, v))
    best = max(key(o) for o in s.names())
    A = [o for o in s.names() if key(o) == best]
    dmin = min(doing(s, o) for o in A)
    A = [o for o in A if doing(s, o) == dmin]
    if apparent_dilemma(s) and len(A) > 1:
        return ["lot(" + ", ".join(A) + ")"]
    return A


# ---------------------------------------------------------------- cases
CASES = []


def add(s):
    CASES.append(s)
    return s


E = Eff
P = lambda **kw: dict(kw)

# Classic cases -------------------------------------------------------------
add(Sit("C01", "classic", P(x="str", f="str"),
        [("divert", [E("x", "W", -10, "r")]),
         ("stay", [E("f", "W", -10, "a", n=5)])],
        source="Foot 1967; Thomson 1985", title="Switch"))
add(Sit("C02", "classic", P(m="str", f="str"),
        [("push", [E("m", "W", -10, "i", "harm")]),
         ("stay", [E("f", "W", -10, "a", n=5)])],
        source="Thomson 1976, 1985", title="Footbridge"))
add(Sit("C03", "classic", P(x="str", f="str"),
        [("harvest", [E("x", "W", -10, "i", "harm")]),
         ("refrain", [E("f", "W", -10, "a", n=5)])],
        source="Thomson 1976", title="Transplant"))
add(Sit("C04", "classic", P(x="str", h="str"),
        [("frame", [E("x", "W", -10, "i", "harm"), E("x", "F", -4, "i", "harm")]),
         ("refuse", [E("h", "W", -10, "a", n=5)])],
        source="Foot 1967", title="Judge and mob"))
add(Sit("C05", "classic", P(v="str", w="str"),
        [("shoot", [E("v", "W", -10, "i", "harm")]),
         ("refuse", [E("v", "W", -10, "a"), E("w", "W", -10, "a", n=19)])],
        source="Williams 1973", title="Jim and the villagers"))
add(Sit("C06", "classic", P(f="close", m="agg"),
        [("truth", [E("f", "W", -10, "a")]),
         ("lie", [E("m", "K", -1, "i", "dec")])],
        source="Kant 1797", title="Murderer at the door"))
add(Sit("C07", "classic", P(f="close", m="agg"),
        [("truth", [E("f", "W", -10, "a")]),
         ("lie", [E("m", "K", -1, "i", "dec")]),
         ("evade", [E("f", "W", -5, "a")])],
        source="after Kant 1797", title="Murderer, evasion possible"))
add(Sit("C08", "classic", P(p="close", v="str"),
        [("keep", [E("v", "W", -8, "a")]),
         ("help", [E("p", "R", -1, "i", "prm")])],
        source="Ross 1930, ch. 2", title="Trivial promise and accident"))
add(Sit("C09", "classic", P(o="close", t="str"),
        [("return", [E("o", "W", -5, "a"), E("t", "W", -4, "a", n=2)]),
         ("withhold", [E("o", "U", -1, "i", "harm"), E("o", "F", -1, "i", "harm")])],
        source="Plato, Republic I 331c", title="Weapons and the madman"))
add(Sit("C10", "classic", P(x="close", y="close"),
        [("giveA", [E("x", "W", -10, "r")]),
         ("giveB", [E("y", "W", -10, "r")]),
         ("refuse", [E("x", "W", -10, "a"), E("y", "W", -10, "a")])],
        source="Styron 1979", title="Sophie's choice (balanced)"))
add(Sit("C11", "classic", P(w="close", s="str"),
        [("saveW", [E("s", "W", -10, "a")]),
         ("saveS", [E("w", "W", -10, "a")])],
        source="Williams 1981", title="Drowning spouse and stranger"))
add(Sit("C12", "classic", P(m="str", x="str"),
        [("jettison", [E("m", "W", -2, "i", "harm", n=3)]),
         ("keep", [E("x", "W", -5, "a", n=10)])],
        source="Aristotle, NE III.1", title="Cargo in a storm"))
add(Sit("C13", "classic", P(m="str", p="str"),
        [("restore", []),
         ("withhold", [E("m", "F", -2, "i", "harm"), E("m", "U", -2, "i", "harm"), E("p", "W", 1, "i", n=4)])],
        source="Hume, Treatise 3.2.2", title="Restoring a fortune to a miser"))
add(Sit("C14", "classic", P(l="str"),
        [("falsepromise", [E("l", "K", -2, "i", "dec"), E("l", "U", -2, "i", "dec"),
                           E("l", "W", -3, "i", "dec"), E("a", "W", 3, "i")]),
         ("refrain", [])],
        source="Kant, Groundwork 4:422", title="Lying promise"))
add(Sit("C15", "classic", P(c="str", s="str"),
        [("bomb", [E("c", "W", -10, "i", "harm", n=20)]),
         ("invade", [E("s", "W", -10, "a", n=40)])],
        source="Anscombe 1956", title="Bombing a city"))
add(Sit("C16", "classic", P(m="close", c="str"),
        [("stay", [E("a", "A", -2, "i")]),
         ("join", [E("m", "R", -2, "i"), E("m", "W", -3, "i"), E("c", "W", 1, "i", n=10)])],
        source="Sartre 1946", title="The student and his mother"))
add(Sit("C17", "classic", P(v="str"),
        [("rescue", [E("a", "W", -1, "i", "danger")]),
         ("pass", [E("v", "W", -10, "a")])],
        source="Singer 1972", title="Child in the pond"))
add(Sit("C18", "classic", P(v="str"),
        [("rescue", [E("a", "W", -6, "i", "danger")]),
         ("pass", [E("v", "W", -10, "a")])],
        source="after Urmson 1958", title="Risky rescue"))
add(Sit("C19", "classic", P(f="close"),
        [("blunt", [E("f", "K", 1, "i"), E("f", "W", -2, "i")]),
         ("tactful", [E("f", "K", 1, "i"), E("f", "W", -1, "i"), E("a", "W", -1, "i")]),
         ("whitelie", [E("f", "K", -2, "i", "dec"), E("f", "U", -2, "i", "dec")])],
        source="standard illustration", title="Hurtful truth to a friend"))


# Schema S1: redirection ---------------------------------------------------
def s1():
    for k in range(1, 11):
        for n in range(1, 11):
            add(Sit(f"R{k:02d}{n:02d}", "S1", P(x="str", f="str"),
                    [("divert", [E("x", "W", -10, "r", n=k)]),
                     ("stay", [E("f", "W", -10, "a", n=n)])], params=f"k={k} n={n}"))


# Schema S2: new threat, with and without the Pareto clause -----------------
def s2():
    for k in range(1, 11):
        for n in range(1, 11):
            add(Sit(f"N{k:02d}{n:02d}", "S2", P(x="str", f="str"),
                    [("impose", [E("x", "W", -10, "i", "harm", n=k)]),
                     ("refrain", [E("f", "W", -10, "a", n=n)])], params=f"k={k} n={n}"))
    for n in range(1, 11):
        add(Sit(f"NP{n:02d}", "S2", P(x="str", f="str"),
                [("impose", [E("x", "W", -10, "i", "harm")]),
                 ("refrain", [E("x", "W", -10, "a"), E("f", "W", -10, "a", n=n)])],
                params=f"doomed=1 n={n}"))
    for n in range(1, 11):
        add(Sit(f"NC{n:02d}", "S2", P(x="str", f="str"),
                [("impose", [E("x", "W", -10, "i", "harm", consent=True)]),
                 ("refrain", [E("f", "W", -10, "a", n=n)])], params=f"consent n={n}"))


# Schema S3: promise and aid ------------------------------------------------
def s3():
    for r in (1, 2, 3):
        for m in range(1, 11):
            for pr in ("close", "str"):
                for vr in ("close", "str"):
                    cid = f"P{r}{m:02d}{pr[0]}{vr[0]}"
                    pe = [E("p", "R", -r, "i", "prm")] + ([E("p", "U", -1, "i", "prm")] if r == 3 else [])
                    add(Sit(cid, "S3", P(p=pr, v=vr),
                            [("keep", [E("v", "W", -m, "a")]),
                             ("help", pe)], params=f"r={r} m={m} promisee={pr} victim={vr}"))


# Schema S4: protective deception --------------------------------------------
def s4():
    for h in (1, 2, 4, 6, 8, 10):
        for tr in ("close", "str"):
            for inq in ("agg", "inn"):
                for ev in (None, Fr(1, 4), Fr(1, 2), Fr(3, 4)):
                    cid = f"D{h:02d}{tr[0]}{inq[0]}{'x' if ev is None else int(ev * 4)}"
                    lie = ([E("q", "K", -1, "i", "dec")] if inq == "agg" else
                           [E("q", "K", -2, "i", "dec"), E("q", "U", -2, "i", "dec")])
                    opts = [("truth", [E("t", "W", -h, "a")]), ("lie", lie)]
                    if ev is not None:
                        opts.append(("evade", [E("t", "W", -h * (1 - ev), "a")]))
                    add(Sit(cid, "S4", P(t=tr, q=("agg" if inq == "agg" else "str")), opts,
                            params=f"h={h} third={tr} inquirer={inq} evade={'-' if ev is None else fmt(ev)}"))


# Schema S5: partiality ------------------------------------------------------
def s5():
    for n in range(1, 7):
        add(Sit(f"Q{n:02d}", "S5", P(c="close", s="str"),
                [("saveClose", [E("s", "W", -10, "a", n=n)]),
                 ("saveStrangers", [E("c", "W", -10, "a")])], params=f"close=1 strangers={n}"))
    for contrib in (5, 10, 20, 40):
        for ms in (1, 2, 3):
            add(Sit(f"Q{contrib:02d}{ms}", "S5", P(m="close", c="str"),
                    [("stay", [E("a", "A", -2, "i")]),
                     ("join", [E("m", "R", -ms, "i"), E("m", "W", -ms, "i"), E("c", "W", 1, "i", n=contrib)])],
                    params=f"Sartre: contribution={contrib} setback={ms}"))


# Schema S6: courage ---------------------------------------------------------
def s6():
    for r in range(1, 11):
        for b in range(1, 11):
            add(Sit(f"K{r:02d}{b:02d}", "S6", P(v="str"),
                    [("intervene", [E("a", "W", -r, "i", "danger")]),
                     ("hold", [E("v", "W", -b, "a")])], params=f"risk={r} benefit={b}"))


# Schema S7: liberality ------------------------------------------------------
def s7():
    for N in (1, 2, 3, 4):
        for rate in (Fr(1, 2), Fr(2), Fr(4)):
            for rr in ("close", "str"):
                opts = []
                for g in range(0, 5):
                    eff = []
                    if g:
                        eff.append(E("a", "W", -g, "i", "money"))
                        ben = rate * min(g, N)
                        eff.append(E("r", "W", ben, "i"))
                    opts.append((f"g{g}", eff))
                add(Sit(f"L{N}{int(rate * 2)}{rr[0]}", "S7", P(r=rr), opts,
                        params=f"need={N} rate={fmt(rate)} recipient={rr}"))


# Schema S8: hurtful truth ---------------------------------------------------
def s8():
    for k in (0, 1, 2, 4):
        for d in (1, 2, 4):
            for hr in ("close", "str"):
                opts = [("blunt", ([E("h", "K", k, "i")] if k else []) + [E("h", "W", -d, "i")]),
                        ("tactful", ([E("h", "K", k, "i")] if k else []) +
                         ([E("h", "W", -Fr(d, 2), "i")]) + [E("a", "W", -1, "i")]),
                        ("whitelie", [E("h", "K", -2, "i", "dec"), E("h", "U", -2, "i", "dec")]),
                        ("silence", ([E("h", "K", -k, "a")] if k else []))]
                add(Sit(f"T{k}{d}{hr[0]}", "S8", P(h=hr), opts, params=f"need-to-know={k} distress={d} hearer={hr}"))


# Schema S9: non-ideal agents (transposition) --------------------------------
NONIDEAL = []


def procrastinate(q, b, c):
    return [("accept", [E("e", "W", b * (1 - q), "i"), E("e", "R", -c * q, "i", "prm")]),
            ("decline", [E("e", "W", b - 1, "a")]),
            ("bind", [E("a", "W", -1, "i"), E("e", "W", b * (1 - q / 2), "i"),
                      E("e", "R", -c * q / 2, "i", "prm")])]


def liar(q, L):
    return [("usual", ([E("o", "K", -2 * q, "i", "dec", n=L), E("o", "U", -2 * q, "i", "dec", n=L)] if q else [])),
            ("regimen", [E("a", "W", -1, "i")] + ([E("o", "K", -q, "i", "dec", n=L), E("o", "U", -q, "i", "dec", n=L)] if q else [])),
            ("avoid", [E("a", "W", -2, "i"), E("a", "R", -1, "i")])]


def s9():
    for q in (Fr(0), Fr(1, 4), Fr(1, 2), Fr(3, 4), Fr(1)):
        for b in (2, 4, 6):
            for c in (2, 4, 6):
                cid = f"V{int(q * 4)}{b}{c}"
                s = add(Sit(cid, "S9", P(e="str"), procrastinate(q, b, c), params=f"q={fmt(q)} b={b} c={c}"))
                naive = Sit(cid + "n", "S9n", P(e="str"), procrastinate(Fr(0), b, c))
                NONIDEAL.append((s, naive))
    for q in (Fr(0), Fr(1, 8), Fr(1, 4), Fr(1, 2), Fr(3, 4)):
        for L in (1, 2, 4):
            cid = f"J{int(q * 8)}{L}"
            s = add(Sit(cid, "S9", P(o="str"), liar(q, L), params=f"q={fmt(q)} lies={L}"))
            naive = Sit(cid + "n", "S9n", P(o="str"), liar(Fr(0), L))
            NONIDEAL.append((s, naive))


# Schema S10: tragic choice (ETH-15-b) ----------------------------------------
def s10():
    ps = (Fr(1, 4), Fr(1, 2), Fr(3, 4), Fr(1))
    for pa in ps:
        for pb in ps:
            add(Sit(f"S{int(pa * 4)}{int(pb * 4)}", "S10", P(x="close", y="close"),
                    [("saveX", [E("y", "W", -10, "r"), E("x", "W", -10 * (1 - pa), "a")]),
                     ("saveY", [E("x", "W", -10, "r"), E("y", "W", -10 * (1 - pb), "a")]),
                     ("refuse", [E("x", "W", -10, "a"), E("y", "W", -10, "a")])],
                    params=f"pX={fmt(pa)} pY={fmt(pb)}"))


# Schema S11: temperance -----------------------------------------------------
def s11():
    for p in range(1, 6):
        for h in range(0, 6):
            for o in (0, 2):
                eff = [E("a", "W", p, "i", "pleasure")]
                if h:
                    eff.append(E("a", "W", -h, "i", "health"))
                if o:
                    eff.append(E("x", "W", -o, "i", "harm"))
                add(Sit(f"M{p}{h}{o}", "S11", P(x="str"),
                        [("indulge", eff), ("abstain", [])], params=f"pleasure={p} cost={h} others={o}"))


for f in (s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11):
    f()

ids = [s.id for s in CASES]
assert len(ids) == len(set(ids)), "duplicate ids"

# ---------------------------------------------------------------- vices
VICES = {
    "S6": [("coward", dict(lam=9, tagw=None)), ("rash", dict(lam=1, tagw={"danger": 0}))],
    "S7": [("prodigal", dict(lam=1, tagw={"money": 0})), ("mean", dict(lam=9, tagw=None))],
    "S11": [("self-indulgent", dict(lam=1, tagw={"pleasure": 3})),
            ("insensible", dict(lam=1, tagw={"pleasure": 0}))],
}

# ---------------------------------------------------------------- compute all
R = {}
for s in CASES:
    r = {}
    r["C"] = characteristic(s)
    r["dec"] = decent(s)
    r["sup"] = [o for o in r["C"] if o not in r["dec"]]
    r["cons"] = consequentialist(s)
    r["deo"] = deontological(s)
    r["ad"] = apparent_dilemma(s)
    r["sil"] = [o for o in s.names() if silenced(s, o)]
    r["eng"] = engaged(s)
    r["vals"] = {o: value(s, o, 1) for o in s.names()}
    r["vices"] = {}
    for name, kw in VICES.get(s.schema, []):
        r["vices"][name] = agent_choice(s, kw["lam"], kw["tagw"])
    R[s.id] = r

# ---------------------------------------------------------------- checks
CHECK = {}


def check(name, cond, cid):
    CHECK.setdefault(name, 0)
    assert cond, f"check {name} failed on {cid}"
    CHECK[name] += 1


for s in CASES:
    r = R[s.id]
    # T1 determinacy
    check("det", len(r["C"]) >= 1, s.id)
    # T2 uniqueness in apparent dilemmas (ETH-15)
    if r["ad"]:
        check("uniq", len(r["C"]) == 1, s.id)
    # silencing: no member of C silenced unless every option is
    smin = min(silenced(s, o) for o in s.names())
    check("sil", all(o.startswith("lot(") or silenced(s, o) == smin for o in r["C"]), s.id)
    # single-field agreement (Proposition 5.6)
    if len(r["eng"]) == 1:
        check("single", r["C"] == lexical(s, r["eng"]), s.id)
    # strict neutral agreement with consequentialism (no case in Appendix B qualifies)
    neutral = all(rel(s, e.p) == "str" and not (e.d < 0 and e.role in "ir")
                  for _, effs in s.options for e in effs)
    if neutral:
        cs = r["cons"]
        if r["ad"] and len(cs) > 1:
            check("neutral", r["C"] == ["lot(" + ", ".join(cs) + ")"], s.id)
        else:
            check("neutral", r["C"] == cs, s.id)
    # Proposition 5.11: no close, no doing, possibly self effects: cons subset of C
    weak = all(rel(s, e.p) in ("str", "self") and not (is_other(s, e.p) and e.d < 0 and e.role in "ir")
               for _, effs in s.options for e in effs)
    if weak and not r["ad"]:
        check("weakneutral", all(o in r["C"] for o in r["cons"]), s.id)
    # decency is part of C
    check("decsub", all(o in r["C"] for o in r["dec"]), s.id)

# Proposition 5.5 and ETH-03
for s in CASES:
    if s.schema == "S1":
        k, n = [int(x.split("=")[1]) for x in s.params.split()]
        check("drt", ("divert" in R[s.id]["C"]) == (k < n), s.id)
    if s.schema == "S2" and s.id.startswith("N") and s.id[1].isdigit():
        check("drt", "impose" not in R[s.id]["C"], s.id)
for cid, v in (("C01", "divert"), ("C02", "stay")):
    check("drt", R[cid]["C"] == [v], cid)
# Corollary 5.12 and ETH-04: lie permissible to the murderer when no evasion is possible
for s in CASES:
    if s.schema == "S4" and "inquirer=agg" in s.params and "evade=-" in s.params and "h=10" in s.params:
        check("eth04", "lie" in R[s.id]["C"], s.id)
check("eth04", "lie" in R["C06"]["C"], "C06")
# ETH-15-b: tragic choice
for s in CASES:
    if s.schema == "S10":
        pa, pb = [Fr(x.split("=")[1]) for x in s.params.split()]
        exp = ["lot(saveX, saveY)"] if pa == pb else (["saveX"] if pa > pb else ["saveY"])
        check("eth15b", R[s.id]["C"] == exp, s.id)
# ETH-18 / ETH-14: rescue required up to moderate cost, supererogatory beyond, waste beyond sainthood
for s in CASES:
    if s.schema == "S6":
        r_, b_ = [int(x.split("=")[1]) for x in s.params.split()]
        C = R[s.id]["C"]
        if b_ > M * r_:
            check("eth18", C == ["intervene"], s.id)
        elif b_ >= r_:
            check("eth18", C == ["intervene", "hold"] and
                  (("intervene" in R[s.id]["sup"]) == (b_ < M * r_)), s.id)
        else:
            check("eth18", "intervene" not in C, s.id)
# Transposition (Theorem 7.2): for q = 0 the transposed and naive verdicts coincide
for s, naive in NONIDEAL:
    if "q=0 " in s.params + " ":
        check("transp", R[s.id]["C"] == characteristic(naive), s.id)

# Vices are action-revealing (Proposition 6.3)
VICE_DEV = {}
for sch, vs in VICES.items():
    for name, _ in vs:
        dev = [s.id for s in CASES if s.schema == sch and
               not all(o in R[s.id]["C"] for o in R[s.id]["vices"][name])]
        assert dev, f"vice {name} never deviates"
        VICE_DEV[name] = dev

# Misperception (the characteristically clause)
CLASSICS = [s for s in CASES if s.schema == "classic"]
MIS = []
for s in CLASSICS:
    for oi, (o, effs) in enumerate(s.options):
        for ei, e in enumerate(effs):
            opts = [(o2, [x for j, x in enumerate(effs2) if not (o2 == o and j == ei)])
                    for o2, effs2 in s.options]
            pert = Sit(s.id + "m", "mis", dict(s.persons), opts)
            got = characteristic(pert)
            inside = all(x in R[s.id]["C"] for x in got)
            MIS.append((s, o, e, got, inside))
MIS_OUT = [m for m in MIS if not m[4]]
assert MIS_OUT, "misperception never matters"

# Uncodifiability (Theorem 5.8): every lexical order of the v-rules fails on a case
NOSELF = [s for s in CASES if not any(rel(s, e.p) == "self" for _, effs in s.options for e in effs)]
CODIFY = []
for order in itertools.permutations(SCORERS):
    wit = None
    nfail = 0
    for s in NOSELF:
        if lexical(s, order) != R[s.id]["C"]:
            nfail += 1
            if wit is None:
                wit = s
    assert wit is not None, f"order {order} codifies"
    CODIFY.append((order, wit, lexical(wit, order), nfail))
# the two witnesses used in the prose proof
assert R["P108ss"]["C"] == ["help"] and R["P102ss"]["C"] == ["keep"]
for order in itertools.permutations(SCORERS):
    if order.index("Fi") < order.index("Be"):
        assert lexical(Sit("x", "x", {"p": "str", "v": "str"}, CASES[ids.index("P108ss")].options), order) == ["keep"]
    else:
        assert lexical(Sit("x", "x", {"p": "str", "v": "str"}, CASES[ids.index("P102ss")].options), order) == ["help"]

# ---------------------------------------------------------------- dependency graphs
GRAPHS = {
    "ETH-12-a": {
        "good": ["idealized endorsement"],
        "idealized endorsement": [],
        "person": [], "option": [], "effect": ["good", "person", "option", "causal role"],
        "causal role": [], "relation": ["person"],
        "sphere": [], "mode": ["good"],
        "virtue": ["sphere", "good", "mode", "response weight"],
        "response weight": ["mode", "causal role", "relation"],
        "perception": ["effect"], "reliability": ["perception", "effect"],
        "practical wisdom": ["reliability"],
        "harmony": [],
        "virtuous agent": ["virtue", "practical wisdom", "harmony"],
        "normal conditions": ["perception"],
        "gravity": ["effect"], "silencing": ["gravity", "causal role", "relation"],
        "prerogative range": ["response weight"],
        "infringement": ["effect", "causal role", "gravity"],
        "apparent dilemma": ["infringement"],
        "impartial procedure": ["apparent dilemma"],
        "characteristic choice": ["virtuous agent", "normal conditions", "silencing",
                                  "prerogative range", "impartial procedure"],
        "transposition": ["effect", "perception"],
        "right action": ["characteristic choice", "transposition"],
        "supererogation": ["right action", "prerogative range"],
    },
    "naive": {
        "right action": ["virtuous agent"],
        "virtuous agent": ["virtue"],
        "virtue": ["right action"],
    },
    "Hursthouse (eudaimonist reading)": {
        "right action": ["virtuous agent"],
        "virtuous agent": ["virtue"],
        "virtue": ["eudaimonia"],
        "eudaimonia": ["virtuous activity"],
        "virtuous activity": ["virtue"],
    },
    "Hursthouse (naturalist reading)": {
        "right action": ["virtuous agent"],
        "virtuous agent": ["virtue"],
        "virtue": ["four ends", "rationality"],
        "four ends": ["species"], "rationality": ["species"], "species": [],
    },
    "Swanton (target-centered)": {
        "right action": ["target of virtue"],
        "target of virtue": ["virtue"],
        "virtue": ["field", "mode"], "field": [], "mode": [],
    },
    "Slote (agent-based)": {
        "right action": ["motive"],
        "motive": ["admirability"], "admirability": [],
    },
    "Driver (consequentialist)": {
        "virtue": ["good consequences"],
        "right action": ["good consequences"],
        "good consequences": [],
    },
}


def cycles(g):
    nodes = set(g) | {v for vs in g.values() for v in vs}
    color = {n: 0 for n in nodes}
    found = []

    def dfs(u, stack):
        color[u] = 1
        stack.append(u)
        for v in sorted(g.get(u, [])):
            if color[v] == 1:
                found.append(stack[stack.index(v):] + [v])
            elif color[v] == 0:
                dfs(v, stack)
        stack.pop()
        color[u] = 2

    for n in sorted(nodes):
        if color[n] == 0:
            dfs(n, [])
    return found


def ancestors(g, u):
    seen, todo = set(), list(g.get(u, []))
    while todo:
        v = todo.pop()
        if v not in seen:
            seen.add(v)
            todo += g.get(v, [])
    return seen


def topo(g):
    nodes = sorted(set(g) | {v for vs in g.values() for v in vs})
    depth = {}

    def d(u):
        if u not in depth:
            depth[u] = 0 if not g.get(u) else 1 + max(d(v) for v in g[u])
        return depth[u]
    for n in nodes:
        d(n)
    return depth


GRES = {}
for name, g in GRAPHS.items():
    cyc = cycles(g)
    upstream = {}
    for t in ("virtue", "virtuous agent"):
        if t in g:
            upstream[t] = "right action" in ancestors(g, t)
    GRES[name] = (cyc, upstream)
assert GRES["ETH-12-a"][0] == [] and not any(GRES["ETH-12-a"][1].values())
assert GRES["naive"][0] and GRES["Hursthouse (eudaimonist reading)"][0]
DEPTH = topo(GRAPHS["ETH-12-a"])

# Definitions in the framework, in the words of the written part (scanned for deontic vocabulary)
DEFTEXT = {
    "good": "what idealized reflective endorsement converges on; seven components",
    "effect": "a change in a good of a person on an option, with its causal role",
    "causal role": "imposed by a new threat, redirected from an existing threat, or allowed",
    "relation": "self, close, stranger or aggressor",
    "sphere": "a domain of feeling and action",
    "mode": "promote, respect, honor, appreciate, measure or perceive",
    "virtue": "a stable disposition of reliable sensitivity, in a sphere, to a field of goods in a mode",
    "response weight": "the weight a change receives from the modes engaged",
    "perception": "the profile of effects an agent takes a situation to have",
    "reliability": "agreement of perceived and actual profiles over a class of situations",
    "practical wisdom": "reliability over all situations in which goods are at stake",
    "harmony": "absence of contrary motivation",
    "virtuous agent": "an agent with the virtues, practical wisdom and harmony",
    "normal conditions": "perception is not defeated by deception, illness or duress",
    "silencing": "grave unconsented imposition on a person who could be spared",
    "prerogative range": "self-weight between one and the decency bound",
    "infringement": "imposed or redirected setback, or allowed grave avoidable setback, to another",
    "apparent dilemma": "every option is an infringement",
    "impartial procedure": "selection by lot among exactly tied options",
    "characteristic choice": "what the virtuous agent chooses acting in character under normal conditions",
    "transposition": "the situation with the agent's own dispositions entered as facts",
}
DEONTIC = re.compile(r"\b(right|rightly|wrong\w*|due|duty|duties|ought|obligat\w*|permiss\w*|"
                     r"forbid\w*|requir\w*|law|laws|rule|rules|obey|obedience|should|must)\b", re.I)
for k, t in DEFTEXT.items():
    assert not DEONTIC.search(t), f"deontic vocabulary in definition of {k}"

# ---------------------------------------------------------------- concordance
TAGRULES = {
    "danger": ("WARF", "measure"), "pleasure": ("W", "measure"), "money": ("WR", "promote"),
    "money-great": ("WAB", "appreciate"), "honor-great": ("AR", "measure"),
    "honor-small": ("A", "measure"), "anger": ("RF", "measure"), "selfpresent": ("K", "respect"),
    "amusement": ("WR", "measure"), "social": ("WR", "honor"), "shame": ("R", "measure"),
    "fortune": ("F", "respect"), "distribution": ("F", "respect"), "exchange": ("FU", "respect"),
    "deliberation": ("WKARFBU", "perceive"), "speech": ("KRU", "respect"), "need": ("W", "promote"),
    "promise": ("RU", "honor"), "polity": ("F", "respect"), "nations": ("RF", "respect"),
    "sexual": ("WR", "measure"), "kin": ("R", "honor"), "benefaction": ("R", "honor"),
    "learning": ("K", "perceive"), "punishment": ("WF", "measure"), "endurance": ("WA", "measure"),
    "creativity": ("AB", "create"), "love": ("WR", "love"), "respect": ("FU", "respect"),
    "selfregard": ("WKA", "promote"), "equity": ("F", "respect"), "selfknow": ("K", "respect"),
    "divine": ("", "\u2020"),
}
MODE_ORDER = ["promote", "respect", "honor", "appreciate", "create", "love", "measure", "perceive", "\u2020"]

II6 = "; feeling and acting at the right times, about the right things, toward the right people, for the right end and in the right way (II.6)"
CONC = [
    # id, source, location, virtue, tags, gloss, excess, deficiency, note
    ("Ar01", "Aristotle", "NE III.6--9", "courage", ["danger"], "mean concerning fear and confidence" + II6, "rashness", "cowardice", ""),
    ("Ar02", "Aristotle", "NE III.10--12", "temperance", ["pleasure"], "mean concerning bodily pleasures" + II6, "self-indulgence", "insensibility", ""),
    ("Ar03", "Aristotle", "NE IV.1", "liberality", ["money"], "mean in giving and taking wealth" + II6, "prodigality", "meanness", ""),
    ("Ar04", "Aristotle", "NE IV.2", "magnificence", ["money-great"], "fitting expenditure on a large scale" + II6, "vulgarity", "niggardliness", ""),
    ("Ar05", "Aristotle", "NE IV.3", "magnanimity", ["honor-great"], "claiming great honor when worthy of it" + II6, "vanity", "pusillanimity", ""),
    ("Ar06", "Aristotle", "NE IV.4", "proper ambition (unnamed)", ["honor-small"], "mean concerning small honors" + II6, "ambition", "unambitiousness", ""),
    ("Ar07", "Aristotle", "NE IV.5", "good temper", ["anger"], "mean concerning anger" + II6, "irascibility", "inirascibility", ""),
    ("Ar08", "Aristotle", "NE IV.7", "truthfulness", ["selfpresent"], "mean in presenting oneself" + II6, "boastfulness", "mock modesty", ""),
    ("Ar09", "Aristotle", "NE IV.8", "wittiness", ["amusement"], "mean in pleasantness in amusement" + II6, "buffoonery", "boorishness", ""),
    ("Ar10", "Aristotle", "NE IV.6", "friendliness (unnamed)", ["social"], "mean in pleasantness in social life" + II6, "obsequiousness; flattery", "quarrelsomeness", ""),
    ("Ar11", "Aristotle", "NE II.7; IV.9", "modesty", ["shame"], "mean in the feeling of shame" + II6, "bashfulness", "shamelessness", "quasi-virtue (a feeling)"),
    ("Ar12", "Aristotle", "NE II.7", "righteous indignation", ["fortune"], "pain at undeserved good fortune" + II6, "envy", "spite", "quasi-virtue (a feeling)"),
    ("Ar13", "Aristotle", "NE V.1--5", "justice", ["distribution", "exchange"], "mean in distribution and rectification" + II6, "taking too much", "(none)", "mean in another way (V.5)"),
    ("Ar14", "Aristotle", "NE VI.5", "practical wisdom", ["deliberation"], "reasoned capacity to act concerning human goods", "", "", "intellectual virtue"),
    ("Aq01", "Aquinas", "ST I-II q.57 a.4", "prudence", ["deliberation"], "right reason about things to be done", "", "", "cardinal"),
    ("Aq02", "Aquinas", "ST II-II q.58 a.1", "justice", ["distribution", "exchange"], "rendering to each his due by a constant and perpetual will", "", "", "cardinal"),
    ("Aq03", "Aquinas", "ST II-II q.123", "fortitude", ["danger", "endurance"], "firmness of mind in dangers, chiefly of death", "", "", "cardinal"),
    ("Aq04", "Aquinas", "ST II-II q.141", "temperance", ["pleasure", "sexual"], "moderation of desire for pleasures of touch", "", "", "cardinal"),
    ("Aq05", "Aquinas", "ST II-II qq.1--16", "faith", ["divine", "learning"], "assent of the intellect to divine truth", "", "", "theological"),
    ("Aq06", "Aquinas", "ST II-II qq.17--22", "hope", ["divine", "endurance"], "expectation of eternal happiness with divine help", "", "", "theological"),
    ("Aq07", "Aquinas", "ST II-II q.23 a.1", "charity", ["divine", "love"], "friendship of man with God, and with neighbor for God's sake", "", "", "theological"),
    ("Aq08", "Aquinas", "ST II-II q.49 a.1", "memory", ["deliberation"], "part of prudence: memory of the past", "", "", "part of prudence"),
    ("Aq09", "Aquinas", "ST II-II q.49 a.2", "understanding", ["deliberation"], "part of prudence: grasp of principles and particulars", "", "", "part of prudence"),
    ("Aq10", "Aquinas", "ST II-II q.49 a.3", "docility", ["learning"], "part of prudence: readiness to be taught", "", "", "part of prudence"),
    ("Aq11", "Aquinas", "ST II-II q.49 a.4", "shrewdness", ["deliberation"], "part of prudence: quick conjecture of means", "", "", "part of prudence"),
    ("Aq12", "Aquinas", "ST II-II q.49 a.5", "reasoning", ["deliberation"], "part of prudence: discursive reasoning", "", "", "part of prudence"),
    ("Aq13", "Aquinas", "ST II-II q.49 a.6", "foresight", ["deliberation"], "part of prudence: ordering present means to future ends", "", "", "part of prudence"),
    ("Aq14", "Aquinas", "ST II-II q.49 a.7", "circumspection", ["deliberation"], "part of prudence: attention to circumstances", "", "", "part of prudence"),
    ("Aq15", "Aquinas", "ST II-II q.49 a.8", "caution", ["deliberation", "danger"], "part of prudence: avoiding evils that mix with good", "", "", "part of prudence"),
    ("Aq16", "Aquinas", "ST II-II q.80", "religion", ["divine"], "potential part of justice: what is due to God", "", "", "part of justice"),
    ("Aq17", "Aquinas", "ST II-II q.80", "piety", ["kin"], "potential part of justice: what is due to parents and country", "", "", "part of justice"),
    ("Aq18", "Aquinas", "ST II-II q.80", "observance", ["honor-small"], "potential part of justice: honor shown to those in dignity", "", "", "part of justice"),
    ("Aq19", "Aquinas", "ST II-II q.80", "gratitude", ["benefaction"], "potential part of justice: return for benefits received", "", "", "part of justice"),
    ("Aq20", "Aquinas", "ST II-II q.80", "vindication", ["punishment"], "potential part of justice: repelling and punishing wrongs", "", "", "part of justice"),
    ("Aq21", "Aquinas", "ST II-II q.80", "truth", ["speech", "selfpresent"], "potential part of justice: showing oneself in word and deed as one is", "", "", "part of justice"),
    ("Aq22", "Aquinas", "ST II-II q.80", "affability", ["social"], "potential part of justice: becoming conduct in ordinary dealings", "", "", "part of justice"),
    ("Aq23", "Aquinas", "ST II-II q.80", "liberality", ["money"], "potential part of justice: right use of wealth toward others", "", "", "part of justice"),
    ("Aq24", "Aquinas", "ST II-II q.80", "epikeia", ["equity"], "potential part of justice: departing from the letter of law for its intent", "", "", "part of justice"),
    ("Aq25", "Aquinas", "ST II-II q.128", "magnanimity", ["honor-great"], "part of fortitude: stretching forth to great things", "", "", "part of fortitude"),
    ("Aq26", "Aquinas", "ST II-II q.128", "magnificence", ["money-great"], "part of fortitude: doing great works", "", "", "part of fortitude"),
    ("Aq27", "Aquinas", "ST II-II q.128", "patience", ["endurance"], "part of fortitude: enduring sorrows without being broken", "", "", "part of fortitude"),
    ("Aq28", "Aquinas", "ST II-II q.128", "perseverance", ["endurance"], "part of fortitude: persisting in a long good work", "", "", "part of fortitude"),
    ("Aq29", "Aquinas", "ST II-II q.143", "shamefacedness", ["shame"], "part of temperance: fear of disgrace", "", "", "part of temperance"),
    ("Aq30", "Aquinas", "ST II-II q.143", "abstinence", ["pleasure"], "part of temperance: moderation in food", "", "", "part of temperance"),
    ("Aq31", "Aquinas", "ST II-II q.143", "sobriety", ["pleasure"], "part of temperance: moderation in drink", "", "", "part of temperance"),
    ("Aq32", "Aquinas", "ST II-II q.143", "chastity", ["sexual"], "part of temperance: moderation of venereal pleasure", "", "", "part of temperance"),
    ("Aq33", "Aquinas", "ST II-II q.143", "continence", ["pleasure"], "part of temperance: resisting vehement desires", "", "", "part of temperance"),
    ("Aq34", "Aquinas", "ST II-II q.143", "meekness", ["anger"], "part of temperance: moderation of anger", "", "", "part of temperance"),
    ("Aq35", "Aquinas", "ST II-II q.143", "clemency", ["punishment"], "part of temperance: moderation of punishment", "", "", "part of temperance"),
    ("Aq36", "Aquinas", "ST II-II q.143", "modesty", ["selfpresent", "learning"], "part of temperance: moderation in lesser matters", "", "", "part of temperance"),
    ("Hu01", "Hume", "T 3.2.1--2", "justice", ["distribution"], "observance of the rules of property fixed by convention", "", "", "artificial"),
    ("Hu02", "Hume", "T 3.2.5", "fidelity to promises", ["promise"], "performing promises, under a convention", "", "", "artificial"),
    ("Hu03", "Hume", "T 3.2.7--10", "allegiance", ["polity"], "obedience to government", "", "", "artificial"),
    ("Hu04", "Hume", "T 3.2.11", "observance of the laws of nations", ["nations"], "keeping the laws of nations among sovereigns", "", "", "artificial"),
    ("Hu05", "Hume", "T 3.2.12", "chastity and modesty", ["sexual", "shame"], "conformity to a convention of sexual restraint", "", "", "artificial"),
    ("Hu06", "Hume", "T 3.3.1", "meekness", ["anger"], "social virtue: mildness of temper", "", "", "natural"),
    ("Hu07", "Hume", "T 3.3.1", "beneficence", ["need"], "social virtue: doing good to others", "", "", "natural"),
    ("Hu08", "Hume", "T 3.3.1", "charity", ["need"], "social virtue: relief of the distressed", "", "", "natural"),
    ("Hu09", "Hume", "T 3.3.1", "generosity", ["money"], "social virtue: liberality to others", "", "", "natural"),
    ("Hu10", "Hume", "T 3.3.1", "clemency", ["punishment"], "social virtue: mitigation of severity", "", "", "natural"),
    ("Hu11", "Hume", "T 3.3.1", "moderation", ["pleasure", "anger"], "social virtue: restraint of the passions", "", "", "natural"),
    ("Hu12", "Hume", "T 3.3.1", "equity", ["equity"], "social virtue: evenhandedness", "", "", "natural"),
    ("Hu13", "Hume", "T 3.3.2", "greatness of mind", ["honor-great", "selfregard"], "well-founded pride and self-esteem", "", "", "natural"),
    ("Hu14", "Hume", "T 3.3.3", "goodness and benevolence", ["need", "love"], "tender concern for others", "", "", "natural"),
    ("Hu15", "Hume", "T 3.3.4", "natural abilities (good sense)", ["deliberation"], "qualities of understanding esteemed like virtues", "", "", "natural"),
    ("Hs01", "Hursthouse", "1999, ch. 1", "honesty", ["speech"], "v-rule: do what is honest", "", "", "v-rule"),
    ("Hs02", "Hursthouse", "1999, ch. 1", "charity (benevolence)", ["need"], "v-rule: do what is charitable", "", "", "v-rule"),
    ("Hs03", "Hursthouse", "1999, ch. 1", "generosity", ["money"], "v-rule: do what is generous", "", "", "v-rule"),
    ("Hs04", "Hursthouse", "1999, ch. 9", "justice", ["distribution", "exchange"], "a trait a human being needs to live well", "", "", "naturalist ground"),
    ("Ft01", "Foot", "1978", "courage", ["danger"], "corrective of a temptation to fear", "", "", "corrective"),
    ("Ft02", "Foot", "1978", "temperance", ["pleasure"], "corrective of a temptation to pleasure", "", "", "corrective"),
    ("Ft03", "Foot", "1978", "charity", ["need"], "attachment to the good of others", "", "", "corrective"),
    ("Ft04", "Foot", "1978", "justice", ["distribution", "exchange"], "virtue concerning what others are owed", "", "", ""),
    ("Ft05", "Foot", "1978", "wisdom", ["deliberation"], "knowledge of means and of the worth of ends", "", "", ""),
    ("Ft06", "Foot", "2001, ch. 3", "fidelity", ["promise"], "keeping faith, needed by humans as stings by bees", "", "", "natural goodness"),
    ("An01", "Annas", "2011", "generosity", ["money", "need"], "skill-like disposition to give, learned and self-directed", "", "", "skill model"),
    ("An02", "Annas", "2011", "courage", ["danger"], "skill-like disposition to face danger", "", "", "skill model"),
    ("Sw01", "Swanton", "2003", "benevolence", ["need"], "promoting the good of others", "", "", "mode: promoting"),
    ("Sw02", "Swanton", "2003", "universal love", ["love"], "loving bonding with others", "", "", "mode: loving"),
    ("Sw03", "Swanton", "2003", "respect", ["respect"], "respecting the standing of persons", "", "", "mode: respecting"),
    ("Sw04", "Swanton", "2003", "creativity", ["creativity"], "creative response to value", "", "", "mode: creating"),
    ("Sw05", "Swanton", "2003", "self-love", ["selfregard"], "proper love of oneself", "", "", "mode: loving"),
    ("Ru01", "Russell", "2009", "practical intelligence", ["deliberation"], "phronesis, necessary for every virtue", "", "", "unity thesis"),
    ("Dr01", "Driver", "1989", "modesty", ["selfknow"], "underestimation of one's own worth", "", "", "virtue of ignorance"),
    ("Dr02", "Driver", "2001", "virtue (general)", ["need"], "trait that systematically produces good consequences", "", "", "consequentialist"),
]
CONV = re.compile(r"\bconvention\b", re.I)
CONC_ROWS = []
for cid, src, loc, name, tags, gloss, exc, dfc, note in CONC:
    goods = "".join(g for g in GOODS if any(g in TAGRULES[t][0] for t in tags))
    modes = [m for m in MODE_ORDER if any(TAGRULES[t][1] == m for t in tags)]
    resid = any(t == "divine" for t in tags)
    flag_d = bool(DEONTIC.search(gloss))
    flag_c = bool(CONV.search(gloss))
    conflict = "selfknow" in tags and "ignorance" in note
    recon = f"reliable sensitivity, in the sphere of {', '.join(tags)}, to {goods or '(none)'} in the mode of {', '.join(modes)}"
    assert not DEONTIC.search(recon), cid
    CONC_ROWS.append(dict(id=cid, src=src, loc=loc, name=name, tags=tags, gloss=gloss, exc=exc,
                          dfc=dfc, note=note, goods=goods, modes=modes, resid=resid,
                          fd=flag_d, fc=flag_c, conflict=conflict))
# coverage: every good is the field of some virtue in the concordance
for g in GOODS:
    assert any(g in r["goods"] for r in CONC_ROWS), g


# ---------------------------------------------------------------- write tables
def L(lst):
    return ", ".join(lst) if lst else "--"


def verdict(lst):
    return tex(L(lst)) if lst else "\\textit{none}"


SCHEMA_TITLES = {
    "classic": "Classic cases",
    "S1": "Schema S1: redirection of an existing threat",
    "S2": "Schema S2: introduction of a new threat",
    "S3": "Schema S3: promise and aid",
    "S4": "Schema S4: protective deception",
    "S5": "Schema S5: partiality",
    "S6": "Schema S6: risk to oneself (courage)",
    "S7": "Schema S7: giving (liberality)",
    "S8": "Schema S8: hurtful truth",
    "S9": "Schema S9: non-ideal agents",
    "S10": "Schema S10: tragic choice",
    "S11": "Schema S11: bodily pleasure (temperance)",
}

with open(os.path.join(OUT, "cases.tex"), "w") as f:
    f.write("% Generated by generate.py; do not edit.\n")
    for sch in ["classic", "S1", "S2", "S3", "S4", "S5", "S6", "S7", "S8", "S9", "S10", "S11"]:
        cs = [s for s in CASES if s.schema == sch]
        f.write(f"\\subsection*{{{SCHEMA_TITLES[sch]} ({len(cs)} cases)}}\n")
        vic = [n for n, _ in VICES.get(sch, [])]
        f.write("\\begin{casetable}\n")
        for s in cs:
            r = R[s.id]
            label = s.title + " (" + s.source + ")" if sch == "classic" else s.params
            prof = s.profile()
            vals = " ".join(f"{o}={fmt(v)}" for o, v in r["vals"].items())
            flags = []
            if r["ad"]:
                flags.append("AD")
            if r["sil"]:
                flags.append("sil:" + L(r["sil"]))
            if r["sup"]:
                flags.append("sup:" + L(r["sup"]))
            flags.append("v:" + "".join(x[0] + x[1] for x in r["eng"]))
            extra = ""
            if sch == "S9":
                naive = dict((a.id, b) for a, b in NONIDEAL)[s.id]
                extra = "naive: " + L(characteristic(naive))
            for vn in vic:
                extra += ("; " if extra else "") + vn + ": " + L(r["vices"][vn])
            f.write(f"{s.id} & {tex(label)} & {tex(prof)} & {tex(vals)} & "
                    f"\\textbf{{{verdict(r['C'])}}} & {verdict(r['cons'])} & {verdict(r['deo'])} & "
                    f"{tex(' '.join(flags))}{(' ' + tex(extra)) if extra else ''} \\\\\n")
        f.write("\\end{casetable}\n")

with open(os.path.join(OUT, "misperception.tex"), "w") as f:
    f.write("% Generated by generate.py; do not edit.\n\\begin{mistable}\n")
    for i, (s, o, e, got, inside) in enumerate(MIS, 1):
        f.write(f"\\texttt{{X{i:03d}}} & \\texttt{{{s.id}}} & {tex(o)} & \\texttt{{{tex(e.code())}}} & "
                f"{verdict(R[s.id]['C'])} & {verdict(got)} & {'yes' if inside else '\\textbf{no}'} \\\\\n")
    f.write("\\end{mistable}\n")

with open(os.path.join(OUT, "concordance.tex"), "w") as f:
    f.write("% Generated by generate.py; do not edit.\n\\begin{conctable}\n")
    for r in CONC_ROWS:
        ed = (r["exc"] + " / " + r["dfc"]) if r["exc"] or r["dfc"] else "--"
        fl = []
        if r["fd"]:
            fl.append("D")
        if r["fc"]:
            fl.append("C")
        if r["resid"]:
            fl.append("$\\dagger$")
        if r["conflict"]:
            fl.append("X")
        modes = ", ".join("$\\dagger$" if m == "\u2020" else m for m in r["modes"])
        f.write(f"\\texttt{{{r['id']}}} & {tex(r['src'])}, {tex(r['loc'])} & {tex(r['name'])} & "
                f"{tex(r['gloss'].split(';')[0] if r['src'] == 'Aristotle' else r['gloss'])} & {tex(ed)} & "
                f"{tex(' '.join(r['tags']))} & \\texttt{{{r['goods'] or '--'}}}{'$\\dagger$' if r['resid'] else ''} & "
                f"{modes} & {' '.join(fl) or '--'} & {tex(r['note']) or '--'} \\\\\n")
    f.write("\\end{conctable}\n")

with open(os.path.join(OUT, "rules.tex"), "w") as f:
    f.write("% Generated by generate.py; do not edit.\n")
    f.write("\\begin{center}\\scriptsize\\begin{longtable}{@{}>{\\ttfamily}l>{\\ttfamily}ll@{\\hspace{2em}}>{\\ttfamily}l>{\\ttfamily}ll@{}}\n")
    f.write("\\textbf{tag} & \\textbf{goods} & \\textbf{mode} & \\textbf{tag} & \\textbf{goods} & \\textbf{mode}\\\\ \\midrule\n")
    items = sorted(TAGRULES.items())
    half = (len(items) + 1) // 2
    for i in range(half):
        a = items[i]
        b = items[i + half] if i + half < len(items) else None
        cell = lambda t: (f"{tex(t[0])} & {t[1][0] or '--'} & {'$\\dagger$' if t[1][1] == chr(8224) else t[1][1]}")
        f.write(cell(a) + " & " + (cell(b) if b else " & & ") + " \\\\\n")
    f.write("\\end{longtable}\\end{center}\n")

with open(os.path.join(OUT, "codify.tex"), "w") as f:
    f.write("% Generated by generate.py; do not edit.\n\\begin{codtable}\n")
    for i, (order, wit, got, nfail) in enumerate(CODIFY, 1):
        f.write(f"\\texttt{{O{i:03d}}} & \\texttt{{{' > '.join(order)}}} & \\texttt{{{wit.id}}} & "
                f"{verdict(got)} & {verdict(R[wit.id]['C'])} & {nfail} \\\\\n")
    f.write("\\end{codtable}\n")

with open(os.path.join(OUT, "graphs.tex"), "w") as f:
    f.write("% Generated by generate.py; do not edit.\n")
    f.write("\\begin{center}\\footnotesize\\begin{longtable}{@{}p{0.3\\textwidth}p{0.42\\textwidth}l@{}}\n")
    f.write("\\textbf{node} & \\textbf{depends on} & \\textbf{depth}\\\\ \\midrule\n")
    g = GRAPHS["ETH-12-a"]
    for n in sorted(DEPTH, key=lambda x: (DEPTH[x], x)):
        f.write(f"{tex(n)} & {tex(', '.join(sorted(g.get(n, [])))) or '(primitive)'} & {DEPTH[n]} \\\\\n")
    f.write("\\end{longtable}\\end{center}\n")
    f.write("\\begin{center}\\footnotesize\\begin{longtable}{@{}p{0.27\\textwidth}p{0.47\\textwidth}p{0.18\\textwidth}@{}}\n")
    f.write("\\textbf{scheme} & \\textbf{cycles found} & \\textbf{right action upstream of virtue?}\\\\ \\midrule\n")
    for name, (cyc, up) in GRES.items():
        cs = "; ".join(" $\\to$ ".join(tex(x) for x in c) for c in cyc) or "none (acyclic)"
        ups = ", ".join(f"{tex(k)}: {'yes' if v else 'no'}" for k, v in up.items()) or "--"
        f.write(f"{tex(name)} & {cs} & {ups} \\\\\n")
    f.write("\\end{longtable}\\end{center}\n")

# ---------------------------------------------------------------- stats
def num(n):
    s = f"{n:,}".replace(",", "{,}")
    return s


st = {}
st["ncases"] = len(CASES)
st["nclassic"] = len(CLASSICS)
st["ngenerated"] = len(CASES) - len(CLASSICS)
for sch in ["S1", "S2", "S3", "S4", "S5", "S6", "S7", "S8", "S9", "S10", "S11"]:
    st["nsch" + ["", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
                 "ten", "eleven"][int(sch[1:])]] = sum(1 for s in CASES if s.schema == sch)
st["nad"] = sum(1 for s in CASES if R[s.id]["ad"])
st["nlot"] = sum(1 for s in CASES if any(o.startswith("lot(") for o in R[s.id]["C"]))
st["nunique"] = sum(1 for s in CASES if len(R[s.id]["C"]) == 1)
st["nlatitude"] = sum(1 for s in CASES if len(R[s.id]["C"]) > 1)
st["nsup"] = sum(1 for s in CASES if R[s.id]["sup"])
st["nsil"] = sum(1 for s in CASES if R[s.id]["sil"])
st["nconsagree"] = sum(1 for s in CASES if R[s.id]["C"] == R[s.id]["cons"])
st["nconsdis"] = len(CASES) - st["nconsagree"]
st["ndeoagree"] = sum(1 for s in CASES if R[s.id]["C"] == R[s.id]["deo"])
st["ndeodilemma"] = sum(1 for s in CASES if not R[s.id]["deo"])
st["ndeodis"] = len(CASES) - st["ndeoagree"]
st["nsingle"] = CHECK.get("single", 0)
st["nweak"] = CHECK.get("weakneutral", 0)
st["ndrt"] = CHECK.get("drt", 0)
st["neth"] = CHECK.get("eth04", 0)
st["nethfifteen"] = CHECK.get("eth15b", 0)
st["netheighteen"] = CHECK.get("eth18", 0)
st["ntransp"] = CHECK.get("transp", 0)
st["nnonideal"] = len(NONIDEAL)
st["nnaivediff"] = sum(1 for s, n in NONIDEAL if R[s.id]["C"] != characteristic(n))
st["nmis"] = len(MIS)
st["nmisout"] = len(MIS_OUT)
st["norders"] = len(CODIFY)
st["nnoself"] = len(NOSELF)
st["nconc"] = len(CONC_ROWS)
st["nconcD"] = sum(1 for r in CONC_ROWS if r["fd"])
st["nconcC"] = sum(1 for r in CONC_ROWS if r["fc"])
st["nconcR"] = sum(1 for r in CONC_ROWS if r["resid"])
st["nconcX"] = sum(1 for r in CONC_ROWS if r["conflict"])
st["ntags"] = len(TAGRULES)
st["ndefs"] = len(DEFTEXT)
st["ngraphnodes"] = len(DEPTH)
st["ngraphdepth"] = max(DEPTH.values())
st["nchecks"] = sum(CHECK.values())
st["nsilcheck"] = CHECK.get("sil", 0)
st["ndecsub"] = CHECK.get("decsub", 0)
GN = {"W": "wellbeing", "K": "knowledge", "A": "achievement", "R": "relationships",
      "F": "fairness", "B": "beauty", "U": "autonomy"}
for g in GOODS:
    st["ngood" + GN[g]] = sum(1 for r in CONC_ROWS if g in r["goods"])
for name, dev in VICE_DEV.items():
    st["nvice" + re.sub(r"[^a-z]", "", name)] = len(dev)
    st["firstvice" + re.sub(r"[^a-z]", "", name)] = dev[0]
# most frequent first witness
from collections import Counter
wc = Counter(w.id for _, w, _, _ in CODIFY)
st["nwitnesses"] = len(wc)
st["topwitness"], st["ntopwitness"] = wc.most_common(1)[0]


def macro(k):
    k2 = re.sub(r"\d", lambda m: "abcdefghij"[int(m.group())], k)
    return "\\st" + k2


with open(os.path.join(OUT, "stats.tex"), "w") as f:
    f.write("% Generated by generate.py; do not edit.\n")
    for k, v in st.items():
        f.write(f"\\newcommand{{{macro(k)}}}{{{num(v) if isinstance(v, int) else v}}}\n")

if __name__ == "__main__":
    print(len(CASES), "cases;", sum(CHECK.values()), "checks;", CHECK)
    print({k: v for k, v in st.items()})
