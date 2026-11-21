"""The derivations of Part B of REL-01-c, written as data and checked line by line by nd.check.

System AF (the filter emendation): axioms F1--F3, A3--A5 with Anderson's definitions of G, Ess, NE.
System SC (Scott's axioms): S1, F2 (= Scott's entailment axiom), S3, A4, S5 with Scott's definitions.
"""

# ---------------------------------------------------------------- syntax helpers
def pv(Y):
    return ("pv", Y)


G = ("pc", "G")
NE = ("pc", "NE")
GS = ("pc", "GS")
NES = ("pc", "NES")
BOT = ("bot",)


def app(T, x):
    return ("app", T, x)


def P(T):
    return ("pos", T)


def Not(A):
    return ("not", A)


def And(A, B):
    return ("and", A, B)


def Imp(A, B):
    return ("imp", A, B)


def Iff(A, B):
    return ("iff", A, B)


def All(x, A):
    return ("all", x, A)


def Ex(x, A):
    return ("ex", x, A)


def AllP(Y, A):
    return ("allp", Y, A)


def Box(A):
    return ("box", A)


def Dia(A):
    return ("dia", A)


def lam(x, A):
    return ("lam", x, A)


def Ess(T, x):
    return ("ess", T, x)


def EssS(T, x):
    return ("essS", T, x)


def at(w, A):
    return ("at", w, A)


def R(w, v):
    return ("R", w, v)


# ---------------------------------------------------------------- definitions and axioms
DEFS = {
    # Anderson: x is godlike iff the positive properties are exactly the properties x has necessarily
    "G": lam("x", AllP("Y", Iff(P(pv("Y")), Box(app(pv("Y"), "x"))))),
    # Anderson: Y is an essence of x iff the properties x has necessarily are exactly those Y necessarily entails
    "ess": ("Y", "x", AllP("Z", Iff(Box(app(pv("Z"), "x")),
                                    Box(All("y", Imp(app(pv("Y"), "y"), app(pv("Z"), "y"))))))),
    "NE": lam("x", AllP("Y", Imp(Ess(pv("Y"), "x"), Box(Ex("y", app(pv("Y"), "y")))))),
    # Scott
    "GS": lam("x", AllP("Y", Imp(P(pv("Y")), app(pv("Y"), "x")))),
    "essS": ("Y", "x", And(app(pv("Y"), "x"),
                           AllP("Z", Imp(app(pv("Z"), "x"),
                                         Box(All("y", Imp(app(pv("Y"), "y"), app(pv("Z"), "y")))))))),
    "NES": lam("x", AllP("Y", Imp(EssS(pv("Y"), "x"), Box(Ex("y", app(pv("Y"), "y")))))),
}

AXIOMS = {
    "F1": AllP("Y", AllP("Z", Imp(And(P(pv("Y")), P(pv("Z"))),
                                  P(lam("x", And(app(pv("Y"), "x"), app(pv("Z"), "x"))))))),
    "F2": AllP("Y", AllP("Z", Imp(And(P(pv("Y")), Box(All("x", Imp(app(pv("Y"), "x"), app(pv("Z"), "x"))))),
                                  P(pv("Z"))))),
    "F3": Not(P(lam("x", BOT))),
    "A3": P(G),
    "A4": AllP("Y", Imp(P(pv("Y")), Box(P(pv("Y"))))),
    "A5": P(NE),
    "S1": AllP("Y", Iff(P(lam("x", Not(app(pv("Y"), "x")))), Not(P(pv("Y"))))),
    "S3": P(GS),
    "S5": P(NES),
}


class D:
    def __init__(self):
        self.lines = []

    def add(self, f, rule, *refs, **kw):
        d = {"f": f, "rule": rule, "refs": list(refs)}
        d.update(kw)
        self.lines.append(d)
        return len(self.lines)


# ---------------------------------------------------------------- AF
def godlike_box(d, w, x, gline):
    """from w: G(x) (line gline) derive w: Def-unfolding and w: box G(x); returns (unfolded, boxline)"""
    u = d.add(at(w, AllP("Y", Iff(P(pv("Y")), Box(app(pv("Y"), x))))), "Def", gline)
    i = d.add(at(w, Iff(P(G), Box(app(G, x)))), "AllpE", u, term=G)
    a = d.add(at(w, P(G)), "Ax", name="A3")
    b = d.add(at(w, Box(app(G, x))), "IffE", i, a)
    return u, b


def deriv_af():
    d = D()
    EG = Ex("x", app(G, "x"))
    # Lemma: possibly something is godlike
    l1 = d.add(at("@", P(G)), "Ax", name="A3", note="G is positive")
    l2 = d.add(at("@", Not(Dia(EG))), "A", note="for reductio")
    l3 = d.add(R("@", "v"), "A")
    l4 = d.add(at("v", app(G, "a")), "A")
    l5 = d.add(at("v", EG), "ExI", l4, term="a")
    l6 = d.add(at("@", Dia(EG)), "DiaI", l3, l5)
    l7 = d.add(at("@", BOT), "NotE", l6, l2)
    l8 = d.add(at("v", BOT), "EFQ", l7)
    l9 = d.add(at("v", Imp(app(G, "a"), BOT)), "ImpI", l4, l8)
    l10 = d.add(at("v", All("x", Imp(app(G, "x"), BOT))), "AllI", l9, eigen="a")
    l11 = d.add(at("@", Box(All("x", Imp(app(G, "x"), BOT)))), "BoxI", l3, l10)
    l12 = d.add(at("@", AXIOMS["F2"]), "Ax", name="F2")
    l13 = d.add(at("@", AllP("Z", Imp(And(P(G), Box(All("x", Imp(app(G, "x"), app(pv("Z"), "x"))))), P(pv("Z"))))),
                "AllpE", l12, term=G)
    l14 = d.add(at("@", Imp(And(P(G), Box(All("x", Imp(app(G, "x"), BOT)))), P(lam("x", BOT)))),
                "AllpE", l13, term=lam("x", BOT))
    l15 = d.add(at("@", And(P(G), Box(All("x", Imp(app(G, "x"), BOT))))), "AndI", l1, l11)
    l16 = d.add(at("@", P(lam("x", BOT))), "ImpE", l14, l15)
    l17 = d.add(at("@", AXIOMS["F3"]), "Ax", name="F3")
    l18 = d.add(at("@", BOT), "NotE", l16, l17)
    l19 = d.add(at("@", Dia(EG)), "RAA", l2, l18, note="Lemma 4.1")
    # Main theorem
    l20 = d.add(R("@", "v"), "A")
    l21 = d.add(at("v", EG), "A")
    l22 = d.add(at("v", app(G, "g")), "A")
    l23, l26 = godlike_box(d, "v", "g", l22)
    l27 = d.add(R("v", "@"), "Sym", l20, note="symmetry")
    l28 = d.add(at("@", app(G, "g")), "BoxE", l26, l27)
    l29, l32 = godlike_box(d, "@", "g", l28)
    l33 = d.add(R("@", "u"), "A")
    l34 = d.add(at("u", app(G, "g")), "BoxE", l32, l33)
    l35 = d.add(at("u", EG), "ExI", l34, term="g")
    l36 = d.add(at("@", Box(EG)), "BoxI", l33, l35)
    # G is an essence of g at @
    Zg = app(pv("Z"), "g")
    ent = Box(All("y", Imp(app(G, "y"), app(pv("Z"), "y"))))
    l37 = d.add(at("@", Box(Zg)), "A")
    l38 = d.add(at("@", Iff(P(pv("Z")), Box(Zg))), "AllpE", l29, term=pv("Z"))
    l39 = d.add(at("@", P(pv("Z"))), "IffE", l38, l37)
    l40 = d.add(R("@", "u"), "A")
    l41 = d.add(at("u", app(G, "y")), "A")
    l42, l45 = godlike_box(d, "u", "y", l41)
    l46 = d.add(R("u", "@"), "Sym", l40)
    l47 = d.add(at("@", app(G, "y")), "BoxE", l45, l46)
    l48 = d.add(at("@", AllP("Y", Iff(P(pv("Y")), Box(app(pv("Y"), "y"))))), "Def", l47)
    l49 = d.add(at("@", Iff(P(pv("Z")), Box(app(pv("Z"), "y")))), "AllpE", l48, term=pv("Z"))
    l50 = d.add(at("@", Box(app(pv("Z"), "y"))), "IffE", l49, l39)
    l51 = d.add(at("u", app(pv("Z"), "y")), "BoxE", l50, l40)
    l52 = d.add(at("u", Imp(app(G, "y"), app(pv("Z"), "y"))), "ImpI", l41, l51)
    l53 = d.add(at("u", All("y", Imp(app(G, "y"), app(pv("Z"), "y")))), "AllI", l52, eigen="y")
    l54 = d.add(at("@", ent), "BoxI", l40, l53)
    l55 = d.add(at("@", Imp(Box(Zg), ent)), "ImpI", l37, l54)
    l56 = d.add(at("@", ent), "A")
    l57 = d.add(R("@", "u"), "A")
    l58 = d.add(at("u", All("y", Imp(app(G, "y"), app(pv("Z"), "y")))), "BoxE", l56, l57)
    l59 = d.add(at("u", Imp(app(G, "g"), Zg)), "AllE", l58, term="g")
    l60 = d.add(at("u", app(G, "g")), "BoxE", l32, l57)
    l61 = d.add(at("u", Zg), "ImpE", l59, l60)
    l62 = d.add(at("@", Box(Zg)), "BoxI", l57, l61)
    l63 = d.add(at("@", Imp(ent, Box(Zg))), "ImpI", l56, l62)
    l64 = d.add(at("@", Iff(Box(Zg), ent)), "IffI", l55, l63)
    l65 = d.add(at("@", AllP("Z", Iff(Box(Zg), ent))), "AllpI", l64, eigen="Z")
    l66 = d.add(at("@", Ess(G, "g")), "Def", l65, note="Lemma 4.3")
    # necessary existence
    l67 = d.add(at("v", Iff(P(NE), Box(app(NE, "g")))), "AllpE", l23, term=NE)
    l68 = d.add(at("v", P(NE)), "Ax", name="A5")
    l69 = d.add(at("v", Box(app(NE, "g"))), "IffE", l67, l68)
    l70 = d.add(at("@", app(NE, "g")), "BoxE", l69, l27, note="Lemma 4.4")
    l71 = d.add(at("@", And(app(G, "g"), Ess(G, "g"))), "AndI", l28, l66)
    body = And(And(app(G, "x"), Ess(G, "x")), app(NE, "x"))
    l72 = d.add(at("@", And(And(app(G, "g"), Ess(G, "g")), app(NE, "g"))), "AndI", l71, l70)
    l73 = d.add(at("@", Ex("x", body)), "ExI", l72, term="g")
    concl = And(Box(EG), Ex("x", body))
    l74 = d.add(at("@", concl), "AndI", l36, l73)
    l75 = d.add(at("@", concl), "ExE", l21, l22, l74, eigen="g")
    d.add(at("@", concl), "DiaE", l19, l20, l21, l75, note="Theorem 4.5")
    return d.lines


# ---------------------------------------------------------------- Scott
def deriv_scott():
    d = D()
    EGS = Ex("x", app(GS, "x"))
    notGS = lam("x", Not(app(GS, "x")))
    # Lemma S-a: possibly something is godlike (Scott)
    l1 = d.add(at("w", P(GS)), "Ax", name="S3")
    l2 = d.add(at("w", Not(Dia(EGS))), "A")
    l3 = d.add(R("w", "v"), "A")
    l4 = d.add(at("v", app(GS, "a")), "A")
    l5 = d.add(at("v", EGS), "ExI", l4, term="a")
    l6 = d.add(at("w", Dia(EGS)), "DiaI", l3, l5)
    l7 = d.add(at("w", BOT), "NotE", l6, l2)
    l8 = d.add(at("v", Not(app(GS, "a"))), "EFQ", l7)
    l9 = d.add(at("v", Imp(app(GS, "a"), Not(app(GS, "a")))), "ImpI", l4, l8)
    l10 = d.add(at("v", All("x", Imp(app(GS, "x"), Not(app(GS, "x"))))), "AllI", l9, eigen="a")
    l11 = d.add(at("w", Box(All("x", Imp(app(GS, "x"), Not(app(GS, "x")))))), "BoxI", l3, l10)
    l12 = d.add(at("w", AXIOMS["F2"]), "Ax", name="F2")
    l13 = d.add(at("w", AllP("Z", Imp(And(P(GS), Box(All("x", Imp(app(GS, "x"), app(pv("Z"), "x"))))),
                                     P(pv("Z"))))), "AllpE", l12, term=GS)
    l14 = d.add(at("w", Imp(And(P(GS), Box(All("x", Imp(app(GS, "x"), Not(app(GS, "x")))))), P(notGS))),
                "AllpE", l13, term=notGS)
    l15 = d.add(at("w", And(P(GS), Box(All("x", Imp(app(GS, "x"), Not(app(GS, "x"))))))), "AndI", l1, l11)
    l16 = d.add(at("w", P(notGS)), "ImpE", l14, l15)
    l17 = d.add(at("w", AXIOMS["S1"]), "Ax", name="S1")
    l18 = d.add(at("w", Iff(P(notGS), Not(P(GS)))), "AllpE", l17, term=GS)
    l19 = d.add(at("w", Not(P(GS))), "IffE", l18, l16)
    l20 = d.add(at("w", BOT), "NotE", l1, l19)
    lposs = d.add(at("w", Dia(EGS)), "RAA", l2, l20, note="possibility")
    # Lemma S-b: a Scott-godlike being has G_S as its Scott essence
    a1 = d.add(at("w", app(GS, "g")), "A")
    a2 = d.add(at("w", AllP("Y", Imp(P(pv("Y")), app(pv("Y"), "g")))), "Def", a1)
    a3 = d.add(at("w", app(pv("Z"), "g")), "A")
    a4 = d.add(at("w", Not(P(pv("Z")))), "A")
    a5 = d.add(at("w", AXIOMS["S1"]), "Ax", name="S1")
    nZ = lam("x", Not(app(pv("Z"), "x")))
    a6 = d.add(at("w", Iff(P(nZ), Not(P(pv("Z"))))), "AllpE", a5, term=pv("Z"))
    a7 = d.add(at("w", P(nZ)), "IffE", a6, a4)
    a8 = d.add(at("w", Imp(P(nZ), Not(app(pv("Z"), "g")))), "AllpE", a2, term=nZ)
    a9 = d.add(at("w", Not(app(pv("Z"), "g"))), "ImpE", a8, a7)
    a10 = d.add(at("w", BOT), "NotE", a3, a9)
    a11 = d.add(at("w", P(pv("Z"))), "RAA", a4, a10)
    a12 = d.add(at("w", AXIOMS["A4"]), "Ax", name="A4")
    a13 = d.add(at("w", Imp(P(pv("Z")), Box(P(pv("Z"))))), "AllpE", a12, term=pv("Z"))
    a14 = d.add(at("w", Box(P(pv("Z")))), "ImpE", a13, a11)
    a15 = d.add(R("w", "u"), "A")
    a16 = d.add(at("u", P(pv("Z"))), "BoxE", a14, a15)
    a17 = d.add(at("u", app(GS, "y")), "A")
    a18 = d.add(at("u", AllP("Y", Imp(P(pv("Y")), app(pv("Y"), "y")))), "Def", a17)
    a19 = d.add(at("u", Imp(P(pv("Z")), app(pv("Z"), "y"))), "AllpE", a18, term=pv("Z"))
    a20 = d.add(at("u", app(pv("Z"), "y")), "ImpE", a19, a16)
    a21 = d.add(at("u", Imp(app(GS, "y"), app(pv("Z"), "y"))), "ImpI", a17, a20)
    a22 = d.add(at("u", All("y", Imp(app(GS, "y"), app(pv("Z"), "y")))), "AllI", a21, eigen="y")
    ent = Box(All("y", Imp(app(GS, "y"), app(pv("Z"), "y"))))
    a23 = d.add(at("w", ent), "BoxI", a15, a22)
    a24 = d.add(at("w", Imp(app(pv("Z"), "g"), ent)), "ImpI", a3, a23)
    a25 = d.add(at("w", AllP("Z", Imp(app(pv("Z"), "g"), ent))), "AllpI", a24, eigen="Z")
    a26 = d.add(at("w", And(app(GS, "g"), AllP("Z", Imp(app(pv("Z"), "g"), ent)))), "AndI", a1, a25)
    a27 = d.add(at("w", EssS(GS, "g")), "Def", a26)
    a28 = d.add(at("w", Imp(app(GS, "g"), EssS(GS, "g"))), "ImpI", a1, a27)
    lessence = d.add(at("w", All("x", Imp(app(GS, "x"), EssS(GS, "x")))), "AllI", a28, eigen="g",
                     note="essence lemma")
    # Lemma S-c: a Scott-godlike being exists necessarily
    b1 = d.add(at("w", app(GS, "g")), "A")
    b2 = d.add(at("w", AllP("Y", Imp(P(pv("Y")), app(pv("Y"), "g")))), "Def", b1)
    b3 = d.add(at("w", Imp(P(NES), app(NES, "g"))), "AllpE", b2, term=NES)
    b4 = d.add(at("w", P(NES)), "Ax", name="S5")
    b5 = d.add(at("w", app(NES, "g")), "ImpE", b3, b4)
    b6 = d.add(at("w", AllP("Y", Imp(EssS(pv("Y"), "g"), Box(Ex("y", app(pv("Y"), "y")))))), "Def", b5)
    b7 = d.add(at("w", Imp(EssS(GS, "g"), Box(Ex("y", app(GS, "y"))))), "AllpE", b6, term=GS)
    b8 = d.add(at("w", Imp(app(GS, "g"), EssS(GS, "g"))), "AllE", lessence, term="g")
    b9 = d.add(at("w", EssS(GS, "g")), "ImpE", b8, b1)
    b10 = d.add(at("w", Box(Ex("y", app(GS, "y")))), "ImpE", b7, b9)
    b11 = d.add(at("w", Imp(app(GS, "g"), Box(Ex("y", app(GS, "y"))))), "ImpI", b1, b10)
    lnec = d.add(at("w", All("x", Imp(app(GS, "x"), Box(Ex("y", app(GS, "y")))))), "AllI", b11, eigen="g",
                 note="necessary existence lemma")
    # Theorem S: something is Scott-godlike, at an arbitrary world
    EyGS = Ex("y", app(GS, "y"))
    c1 = d.add(R("w", "v"), "A")
    c2 = d.add(at("v", EGS), "A")
    c3 = d.add(at("v", app(GS, "h")), "A")
    c4 = d.add(at("v", All("x", Imp(app(GS, "x"), Box(EyGS)))), "Rel", lnec)
    c5 = d.add(at("v", Imp(app(GS, "h"), Box(EyGS))), "AllE", c4, term="h")
    c6 = d.add(at("v", Box(EyGS)), "ImpE", c5, c3)
    c7 = d.add(R("v", "w"), "Sym", c1, note="symmetry")
    c8 = d.add(at("w", EyGS), "BoxE", c6, c7)
    c9 = d.add(at("w", EyGS), "ExE", c2, c3, c8, eigen="h")
    lthm = d.add(at("w", EyGS), "DiaE", lposs, c1, c2, c9, note="theorem (Scott)")
    # Sobel's collapse, for the propositions 'something is Y'
    EY = Ex("x", app(pv("Y"), "x"))
    q = lam("z", EY)
    e1 = d.add(at("w", EY), "A")
    e2 = d.add(at("w", app(GS, "h")), "A")
    e3 = d.add(at("w", All("x", Imp(app(GS, "x"), EssS(GS, "x")))), "Rel", lessence)
    e4 = d.add(at("w", Imp(app(GS, "h"), EssS(GS, "h"))), "AllE", e3, term="h")
    e5 = d.add(at("w", EssS(GS, "h")), "ImpE", e4, e2)
    entq = Box(All("y", Imp(app(GS, "y"), EY)))
    e6 = d.add(at("w", And(app(GS, "h"), AllP("Z", Imp(app(pv("Z"), "h"),
                                                     Box(All("y", Imp(app(GS, "y"), app(pv("Z"), "y")))))))),
               "Def", e5)
    e7 = d.add(at("w", AllP("Z", Imp(app(pv("Z"), "h"), Box(All("y", Imp(app(GS, "y"), app(pv("Z"), "y"))))))),
               "AndE", e6)
    e8 = d.add(at("w", Imp(EY, entq)), "AllpE", e7, term=q, note="comprehension")
    e9 = d.add(at("w", entq), "ImpE", e8, e1)
    e10 = d.add(at("w", entq), "ExE", lthm, e2, e9, eigen="h")
    e11 = d.add(R("w", "u"), "A")
    e12 = d.add(at("u", All("y", Imp(app(GS, "y"), EY))), "BoxE", e10, e11)
    e13 = d.add(at("u", EyGS), "Rel", lthm)
    e14 = d.add(at("u", app(GS, "k")), "A")
    e15 = d.add(at("u", Imp(app(GS, "k"), EY)), "AllE", e12, term="k")
    e16 = d.add(at("u", EY), "ImpE", e15, e14)
    e17 = d.add(at("u", EY), "ExE", e13, e14, e16, eigen="k")
    e18 = d.add(at("w", Box(EY)), "BoxI", e11, e17)
    e19 = d.add(at("w", Imp(EY, Box(EY))), "ImpI", e1, e18)
    d.add(at("w", AllP("Y", Imp(EY, Box(EY)))), "AllpI", e19, eigen="Y", note="collapse")
    return d.lines


# ---------------------------------------------------------------- further derivations
def deriv_positive():
    """every positive property is possibly instantiated (general form of Lemma 4.1)"""
    d = D()
    Y = pv("Y")
    EY = Ex("x", app(Y, "x"))
    l1 = d.add(at("w", P(Y)), "A")
    l2 = d.add(at("w", Not(Dia(EY))), "A")
    l3 = d.add(R("w", "v"), "A")
    l4 = d.add(at("v", app(Y, "a")), "A")
    l5 = d.add(at("v", EY), "ExI", l4, term="a")
    l6 = d.add(at("w", Dia(EY)), "DiaI", l3, l5)
    l7 = d.add(at("w", BOT), "NotE", l6, l2)
    l8 = d.add(at("v", BOT), "EFQ", l7)
    l9 = d.add(at("v", Imp(app(Y, "a"), BOT)), "ImpI", l4, l8)
    l10 = d.add(at("v", All("x", Imp(app(Y, "x"), BOT))), "AllI", l9, eigen="a")
    l11 = d.add(at("w", Box(All("x", Imp(app(Y, "x"), BOT)))), "BoxI", l3, l10)
    l12 = d.add(at("w", AXIOMS["F2"]), "Ax", name="F2")
    l13 = d.add(at("w", AllP("Z", Imp(And(P(Y), Box(All("x", Imp(app(Y, "x"), app(pv("Z"), "x"))))),
                                     P(pv("Z"))))), "AllpE", l12, term=Y)
    l14 = d.add(at("w", Imp(And(P(Y), Box(All("x", Imp(app(Y, "x"), BOT)))), P(lam("x", BOT)))),
                "AllpE", l13, term=lam("x", BOT))
    l15 = d.add(at("w", And(P(Y), Box(All("x", Imp(app(Y, "x"), BOT))))), "AndI", l1, l11)
    l16 = d.add(at("w", P(lam("x", BOT))), "ImpE", l14, l15)
    l17 = d.add(at("w", AXIOMS["F3"]), "Ax", name="F3")
    l18 = d.add(at("w", BOT), "NotE", l16, l17)
    l19 = d.add(at("w", Dia(EY)), "RAA", l2, l18)
    l20 = d.add(at("w", Imp(P(Y), Dia(EY))), "ImpI", l1, l19)
    d.add(at("w", AllP("Y", Imp(P(Y), Dia(EY)))), "AllpI", l20, eigen="Y")
    return d.lines


def deriv_anderson():
    """Anderson's first axiom follows from F1, F2 and F3"""
    d = D()
    Y = pv("Y")
    nY = lam("x", Not(app(Y, "x")))
    conj = lam("x", And(app(Y, "x"), Not(app(Y, "x"))))
    body = And(app(Y, "x"), Not(app(Y, "x")))
    l1 = d.add(at("w", P(Y)), "A")
    l2 = d.add(at("w", P(nY)), "A")
    l3 = d.add(at("w", AXIOMS["F1"]), "Ax", name="F1")
    l4 = d.add(at("w", AllP("Z", Imp(And(P(Y), P(pv("Z"))), P(lam("x", And(app(Y, "x"), app(pv("Z"), "x"))))))),
               "AllpE", l3, term=Y)
    l5 = d.add(at("w", Imp(And(P(Y), P(nY)), P(conj))), "AllpE", l4, term=nY)
    l6 = d.add(at("w", And(P(Y), P(nY))), "AndI", l1, l2)
    l7 = d.add(at("w", P(conj)), "ImpE", l5, l6)
    l8 = d.add(R("w", "v"), "A")
    l9 = d.add(at("v", And(app(Y, "a"), Not(app(Y, "a")))), "A")
    l10 = d.add(at("v", app(Y, "a")), "AndE", l9)
    l11 = d.add(at("v", Not(app(Y, "a"))), "AndE", l9)
    l12 = d.add(at("v", BOT), "NotE", l10, l11)
    l13 = d.add(at("v", Imp(And(app(Y, "a"), Not(app(Y, "a"))), BOT)), "ImpI", l9, l12)
    l14 = d.add(at("v", All("x", Imp(body, BOT))), "AllI", l13, eigen="a")
    l15 = d.add(at("w", Box(All("x", Imp(body, BOT)))), "BoxI", l8, l14)
    l16 = d.add(at("w", AXIOMS["F2"]), "Ax", name="F2")
    l17 = d.add(at("w", AllP("Z", Imp(And(P(conj), Box(All("x", Imp(body, app(pv("Z"), "x"))))), P(pv("Z"))))),
                "AllpE", l16, term=conj)
    l18 = d.add(at("w", Imp(And(P(conj), Box(All("x", Imp(body, BOT)))), P(lam("x", BOT)))),
                "AllpE", l17, term=lam("x", BOT))
    l19 = d.add(at("w", And(P(conj), Box(All("x", Imp(body, BOT))))), "AndI", l7, l15)
    l20 = d.add(at("w", P(lam("x", BOT))), "ImpE", l18, l19)
    l21 = d.add(at("w", AXIOMS["F3"]), "Ax", name="F3")
    l22 = d.add(at("w", BOT), "NotE", l20, l21)
    l23 = d.add(at("w", Not(P(nY))), "NotI", l2, l22)
    l24 = d.add(at("w", Imp(P(Y), Not(P(nY)))), "ImpI", l1, l23)
    d.add(at("w", AllP("Y", Imp(P(Y), Not(P(nY))))), "AllpI", l24, eigen="Y")
    return d.lines


def deriv_indisc():
    """any two godlike beings have the same necessary properties (no frame condition)"""
    d = D()
    Z = pv("Z")
    l1 = d.add(at("w", app(G, "b")), "A")
    l2 = d.add(at("w", app(G, "c")), "A")
    l3 = d.add(at("w", AllP("Y", Iff(P(pv("Y")), Box(app(pv("Y"), "b"))))), "Def", l1)
    l4 = d.add(at("w", AllP("Y", Iff(P(pv("Y")), Box(app(pv("Y"), "c"))))), "Def", l2)
    l5 = d.add(at("w", Iff(P(Z), Box(app(Z, "b")))), "AllpE", l3, term=Z)
    l6 = d.add(at("w", Iff(P(Z), Box(app(Z, "c")))), "AllpE", l4, term=Z)
    l7 = d.add(at("w", Box(app(Z, "b"))), "A")
    l8 = d.add(at("w", P(Z)), "IffE", l5, l7)
    l9 = d.add(at("w", Box(app(Z, "c"))), "IffE", l6, l8)
    l10 = d.add(at("w", Imp(Box(app(Z, "b")), Box(app(Z, "c")))), "ImpI", l7, l9)
    l11 = d.add(at("w", Box(app(Z, "c"))), "A")
    l12 = d.add(at("w", P(Z)), "IffE", l6, l11)
    l13 = d.add(at("w", Box(app(Z, "b"))), "IffE", l5, l12)
    l14 = d.add(at("w", Imp(Box(app(Z, "c")), Box(app(Z, "b")))), "ImpI", l11, l13)
    l15 = d.add(at("w", Iff(Box(app(Z, "b")), Box(app(Z, "c")))), "IffI", l10, l14)
    l16 = d.add(at("w", AllP("Z", Iff(Box(app(Z, "b")), Box(app(Z, "c"))))), "AllpI", l15, eigen="Z")
    l17 = d.add(at("w", Imp(app(G, "c"), AllP("Z", Iff(Box(app(Z, "b")), Box(app(Z, "c")))))), "ImpI", l2, l16)
    l18 = d.add(at("w", Imp(app(G, "b"), Imp(app(G, "c"), AllP("Z", Iff(Box(app(Z, "b")), Box(app(Z, "c"))))))),
                "ImpI", l1, l17)
    l19 = d.add(at("w", All("y", Imp(app(G, "b"), Imp(app(G, "y"),
                                                      AllP("Z", Iff(Box(app(Z, "b")), Box(app(Z, "y")))))))),
                "AllI", l18, eigen="c")
    d.add(at("w", All("x", All("y", Imp(app(G, "x"), Imp(app(G, "y"),
                                                         AllP("Z", Iff(Box(app(Z, "x")), Box(app(Z, "y"))))))))),
          "AllI", l19, eigen="b")
    return d.lines


def deriv_converse():
    """the analogue of the converse argument: possibly nothing is godlike -> nothing is godlike (any frame)"""
    d = D()
    EG = Ex("x", app(G, "x"))
    l1 = d.add(at("w", Dia(Not(EG))), "A")
    l2 = d.add(at("w", EG), "A")
    l3 = d.add(at("w", app(G, "b")), "A")
    _, l7 = godlike_box(d, "w", "b", l3)
    l8 = d.add(R("w", "v"), "A")
    l9 = d.add(at("v", Not(EG)), "A")
    l10 = d.add(at("v", app(G, "b")), "BoxE", l7, l8)
    l11 = d.add(at("v", EG), "ExI", l10, term="b")
    l12 = d.add(at("v", BOT), "NotE", l11, l9)
    l13 = d.add(at("w", BOT), "EFQ", l12)
    l14 = d.add(at("w", BOT), "DiaE", l1, l8, l9, l13)
    l15 = d.add(at("w", BOT), "ExE", l2, l3, l14, eigen="b")
    l16 = d.add(at("w", Not(EG)), "NotI", l2, l15)
    d.add(at("w", Imp(Dia(Not(EG)), Not(EG))), "ImpI", l1, l16)
    return d.lines


DERIVATIONS = {
    "af": ("The main theorem of AF", deriv_af),
    "scott": ("Modal collapse in Scott's system", deriv_scott),
    "positive": ("Positive properties are possibly instantiated", deriv_positive),
    "anderson": ("Anderson's first axiom from the filter axioms", deriv_anderson),
    "indisc": ("Godlike beings share their necessary properties", deriv_indisc),
    "converse": ("The converse argument", deriv_converse),
}
