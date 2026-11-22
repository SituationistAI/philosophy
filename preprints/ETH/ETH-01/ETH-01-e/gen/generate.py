"""Generator for ETH-01-e, Errata to On the Good, Volume IV (Fairness).

Run `python3 generate.py` in this directory.  Writes skeleton.tex, stats.tex
and vol04.tex.  Deterministic (random.Random(SEED)).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from errata_engine import (Book, Chapter, Item, Volume, Generator, Entry, ROMAN,  # noqa: E402
                           build_items, build_displays, latex_chapter, forread,
                           transpose_digits)

SEED = 20261008
HERE = os.path.dirname(os.path.abspath(__file__))

BIB = {
    "Anderson1999": dict(authors=[("Anderson", "E.~S.")], year=1999, title="What is the point of equality?",
                         journal="Ethics", vol="109(2)", pages="287--337", topic="democratic equality"),
    "Arneson1989": dict(authors=[("Arneson", "R.~J.")], year=1989,
                        title="Equality and equal opportunity for welfare",
                        journal="Philosophical Studies", vol="56(1)", pages="77--93",
                        topic="equal opportunity for welfare"),
    "Atkinson1970": dict(authors=[("Atkinson", "A.~B.")], year=1970, title="On the measurement of inequality",
                         journal="Journal of Economic Theory", vol="2(3)", pages="244--263",
                         topic="the measurement of inequality"),
    "Barry1989": dict(authors=[("Barry", "B.")], year=1989, title="Theories of Justice",
                      publisher="University of California Press"),
    "Broome1990": dict(authors=[("Broome", "J.")], year=1990, title="Fairness",
                       journal="Proceedings of the Aristotelian Society", vol="91", pages="87--101",
                       topic="the claims account of fairness"),
    "Broome1991": dict(authors=[("Broome", "J.")], year=1991, title="Weighing Goods",
                       publisher="Basil Blackwell"),
    "Cohen1989": dict(authors=[("Cohen", "G.~A.")], year=1989, title="On the currency of egalitarian justice",
                      journal="Ethics", vol="99(4)", pages="906--944",
                      topic="access to advantage"),
    "Crisp2003": dict(authors=[("Crisp", "R.")], year=2003, title="Equality, priority, and compassion",
                      journal="Ethics", vol="113(4)", pages="745--763", topic="the sufficiency view"),
    "Diamond1967": dict(authors=[("Diamond", "P.~A.")], year=1967,
                        title="Cardinal welfare, individualistic ethics, and interpersonal comparison of utility: Comment",
                        journal="Journal of Political Economy", vol="75(5)", pages="765--766",
                        no_errata=True),
    "Dworkin1981": dict(authors=[("Dworkin", "R.")], year=1981,
                        title="What is equality? Part 2: Equality of resources",
                        journal="Philosophy \\& Public Affairs", vol="10(4)", pages="283--345",
                        topic="equality of resources"),
    "Elster1989": dict(authors=[("Elster", "J.")], year=1989, title="Solomonic Judgements",
                       publisher="Cambridge University Press"),
    "Feinberg1970": dict(authors=[("Feinberg", "J.")], year=1970, title="Doing and Deserving",
                         publisher="Princeton University Press"),
    "Frankfurt1987": dict(authors=[("Frankfurt", "H.")], year=1987, title="Equality as a moral ideal",
                          journal="Ethics", vol="98(1)", pages="21--43", topic="the doctrine of sufficiency"),
    "Harsanyi1955": dict(authors=[("Harsanyi", "J.~C.")], year=1955,
                         title="Cardinal welfare, individualistic ethics, and interpersonal comparisons of utility",
                         journal="Journal of Political Economy", vol="63(4)", pages="309--321",
                         topic="the aggregation theorem"),
    "Hart1955": dict(authors=[("Hart", "H.~L.~A.")], year=1955, title="Are there any natural rights?",
                     journal="The Philosophical Review", vol="64(2)", pages="175--191",
                     topic="the principle of fair play"),
    "Hirose2015": dict(authors=[("Hirose", "I.")], year=2015, title="Egalitarianism", publisher="Routledge"),
    "Holtug2010": dict(authors=[("Holtug", "N.")], year=2010, title="Persons, Interests, and Justice",
                       publisher="Oxford University Press"),
    "Hooker2005": dict(authors=[("Hooker", "B.")], year=2005, title="Fairness",
                       journal="Ethical Theory and Moral Practice", vol="8(4)", pages="329--352",
                       topic="fairness as a family of requirements"),
    "Kagan2012": dict(authors=[("Kagan", "S.")], year=2012, title="The Geometry of Desert",
                      publisher="Oxford University Press"),
    "Kamm1993": dict(authors=[("Kamm", "F.~M.")], year=1993,
                     title="Morality, Mortality, Volume I: Death and Whom to Save from It",
                     publisher="Oxford University Press"),
    "McKerlie1994": dict(authors=[("McKerlie", "D.")], year=1994, title="Equality and priority",
                         journal="Utilitas", vol="6(1)", pages="25--42", topic="the priority view"),
    "Miller1999": dict(authors=[("Miller", "D.")], year=1999, title="Principles of Social Justice",
                       publisher="Harvard University Press"),
    "Moore1903": dict(authors=[("Moore", "G.~E.")], year=1903, title="Principia Ethica",
                      publisher="Cambridge University Press"),
    "Nozick1974": dict(authors=[("Nozick", "R.")], year=1974, title="Anarchy, State, and Utopia",
                       publisher="Basic Books"),
    "Otsuka2009": dict(authors=[("Otsuka", "M."), ("Voorhoeve", "A.")], year=2009,
                       title="Why it matters that some are worse off than others: An argument against the priority view",
                       journal="Philosophy \\& Public Affairs", vol="37(2)", pages="171--199",
                       topic="the argument against the priority view"),
    "Parfit1984": dict(authors=[("Parfit", "D.")], year=1984, title="Reasons and Persons",
                       publisher="Clarendon Press",
                       slips=[(r"Parfit (1984, ch.~17) (the non-identity problem)",
                               r"Parfit (1984, ch.~16) (the non-identity problem)")]),
    "Parfit1997": dict(authors=[("Parfit", "D.")], year=1997, title="Equality and priority",
                       journal="Ratio", vol="10(3)", pages="202--221", no_errata=True,
                       topic="the levelling-down objection"),
    "Rawls1958": dict(authors=[("Rawls", "J.")], year=1958, title="Justice as fairness",
                      journal="The Philosophical Review", vol="67(2)", pages="164--194",
                      topic="justice as fairness"),
    "Rawls1971": dict(authors=[("Rawls", "J.")], year=1971, title="A Theory of Justice",
                      publisher="Harvard University Press",
                      slips=[(r"Rawls (1971, \S 45) (justice between generations)",
                              r"Rawls (1971, \S 44) (justice between generations)")]),
    "Ross1930": dict(authors=[("Ross", "W.~D.")], year=1930, title="The Right and the Good",
                     publisher="Clarendon Press"),
    "Scanlon1998": dict(authors=[("Scanlon", "T.~M.")], year=1998, title="What We Owe to Each Other",
                        publisher="Harvard University Press"),
    "Sen1973": dict(authors=[("Sen", "A.")], year=1973, title="On Economic Inequality",
                    publisher="Clarendon Press"),
    "Sher1987": dict(authors=[("Sher", "G.")], year=1987, title="Desert", publisher="Princeton University Press"),
    "Sidgwick1907": dict(authors=[("Sidgwick", "H.")], year=1907, title="The Methods of Ethics (7th ed.)",
                         publisher="Macmillan"),
    "Stone2011": dict(authors=[("Stone", "P.")], year=2011,
                      title="The Luck of the Draw: The Role of Lotteries in Decision Making",
                      publisher="Oxford University Press"),
    "Taurek1977": dict(authors=[("Taurek", "J.~M.")], year=1977, title="Should the numbers count?",
                       journal="Philosophy \\& Public Affairs", vol="6(4)", pages="293--316",
                       topic="the numbers problem"),
    "Temkin1993": dict(authors=[("Temkin", "L.~S.")], year=1993, title="Inequality",
                       publisher="Oxford University Press"),
    "Wasserman1996": dict(authors=[("Wasserman", "D.")], year=1996,
                          title="Let them eat chances: Probability and distributive justice",
                          journal="Economics and Philosophy", vol="12(1)", pages="29--49",
                          topic="the value of chances"),
    "Aristotle": dict(authors=[("Aristotle", "")], year=-330, classic=True, title="Nicomachean Ethics",
                      slips=[(r"Aristotle, \emph{Nicomachean Ethics} V.4 (distributive justice)",
                              r"Aristotle, \emph{Nicomachean Ethics} V.3 (distributive justice)")]),
}

PUB = ["Clarendon Press", "Oxford University Press", "Cambridge University Press",
       "Harvard University Press", "Princeton University Press"]
PUBLISHER_CONFUSIONS = {p: [q for q in PUB if q != p] for p in PUB}
PUBLISHER_CONFUSIONS.update({"Basil Blackwell": ["Routledge"], "Routledge": ["Basil Blackwell"],
                             "Macmillan": ["Routledge"], "Basic Books": ["Harvard University Press"],
                             "University of California Press": ["Princeton University Press"]})

EXTRA_WORDS = """
absolutely abstract accordingly account achieve additional address adequate admittedly
advantage alternative although ambiguity analysis anticipate apparent application approach
argued arguably assertion assessment attribute available beneficial between capacity
carefully category certainly challenge circumstance claimed clarify classical combination
comparable comparison complete conception concerned condition conditional conjecture
connection consensus considerable constraint construction contemporary context contrary
contrast contribution controversy convention conviction correctly corresponding criterion
critical decisive defended deficiency definition deliberate denial dependence describe
description desirable despite determinate develop development difference different
difficulty dilemma directly disagreement discussion dispute distinguish doctrine
effectively elsewhere emphasis empirical employed encounter entirely equally equivalent
especially essential establish evaluate eventually evidence evident exactly example
exception explanation explicit expression extension familiar formulation framework
fundamental further generally genuine guarantee however identical identify illustrate
immediate implication implicit importance impossible including inconsistent indeed
indicate individual inevitable initially instance instead intended interest intrinsic
introduce intuitive judgement knowledge language latter literature logically maintain
manifest material meaning mechanism mention merely method modest moreover motivation
namely naturally neither notation nothing notion objection objective observation obtain
obvious occasionally omitted opponent opposite ordinary original otherwise paradigm
paragraph particularly perhaps permissible perspective phenomenon plausible position
practical precisely preference premise presence presumably previous primarily principal
probable problem procedure proceed process proponent proposal prospect provided purpose
question rather reasonable recognize reference regarded regardless remainder remarkable
represent requirement resemblance response restriction rigorous satisfied scenario section
sentence sequence serious significant similarly situation slightly solution something
specific statement straightforward strategy strength strictly structure subsequent succeed
successful suggestion suppose systematic technical tendency terminology theorem thereby
thorough tradition transition treatment ultimately undermine understanding uniform
universal unless validity variation various version virtually whereas whenever
argument conclusion consequently nevertheless independently interpretation distinction
consideration assumption demonstrate preliminary occurrence necessary accommodate separate
definitely existence relevance inference coherence consistent independent commitment
committed occurred referred acknowledge analogous appropriate consequence hypothesis
particular presupposition principle proposition questionable receive relevant
respectively sufficient therefore throughout unnecessary whether irrelevant persuasive"""
EXTRA_WORDS = [w for w in EXTRA_WORDS.split() if len(w) >= 6]

GROUPS = {
    "GEN": dict(terms=EXTRA_WORDS,
                inserts=[(r"the second occurrence of \emph{the}", "DELETE"),
                         (r"the second occurrence of \emph{of}", "DELETE"),
                         (r"the second occurrence of \emph{is}", "DELETE"),
                         (r"the second occurrence of \emph{that}", "DELETE"),
                         (r"the second occurrence of \emph{a}", "DELETE")]),
    "INTRO": dict(terms=["introduction", "summary", "chapter", "volume", "preceding", "following",
                         "organization", "overview"]),
    "FAIR": dict(
        terms=["fairness", "claims", "satisfaction", "proportion", "proportional", "lottery",
               "indivisible", "impartial", "allocation", "distribution", "procedure", "consent",
               "arbitrary", "weighted", "entitlement", "surrogate", "chances"],
        formulas=[r"\frac{s_{[[i1]]}}{c_{[[i1]]}} = \frac{s_{[[i2]]}}{c_{[[i2]]}}",
                  r"\pi_{[[i1]]} = c_{[[i1]]} \Big/ \sum_{[[i2]]} c_{[[i2]]}",
                  r"c_{[[i1]]} = c_{[[i2]]} \to \pi_{[[i1]]} = \pi_{[[i2]]}",
                  r"\sum_{[[i1]]} s_{[[i1]]} \leq S",
                  r"s_{[[i1]]} \leq c_{[[i1]]}",
                  r"\sum_{[[i1]]} \pi_{[[i1]]} = 1",
                  r"F([[x1]]) > F([[x2]]) \wedge [[x1]]_{-F} = [[x2]]_{-F} \to V([[x1]]) > V([[x2]])",
                  r"c_{[[i1]]} > c_{[[i2]]} \to \pi_{[[i1]]} > \pi_{[[i2]]}",
                  r"u_{[[i1]]}(L) = \pi_{[[i1]]}\, u_{[[i1]]}(g)"],
        swaps=[(r"in proportion to their urgency", r"in proportion to their strength"),
               (r"an equal-chance lottery is unfair when the claims are equal",
                r"an equal-chance lottery is fair when the claims are equal"),
               (r"the stronger claim is satisfied only in part", r"the weaker claim is satisfied only in part"),
               (r"ex post fairness of the lottery", r"ex ante fairness of the lottery"),
               (r"outcome fairness", r"procedural fairness"),
               (r"a claim is a reason to give the good to whoever can use it best",
                r"a claim is a reason owed to the candidate herself")],
        inserts=[(r"claims", r"to the good"), (r"lottery", r"with chances proportional to the claims")],
        index_terms=["fairness", "claims", "lotteries", "indivisible goods", "proportional satisfaction",
                     "weighted lotteries"]),
    "EQ": dict(
        terms=["equality", "priority", "prioritarian", "egalitarian", "sufficiency", "threshold",
               "levelling", "inequality", "concave", "Pareto", "telic", "deontic"],
        formulas=[r"V([[x1]]) = \sum_{[[i1]]} f(w_{[[i1]]}([[x1]])), \quad f'' < 0",
                  r"\min_{[[i1]]} w_{[[i1]]}([[x1]]) > \min_{[[i1]]} w_{[[i1]]}([[x2]]) \to [[x1]] \succ [[x2]]",
                  r"G([[x1]]) = \frac{1}{2n^{2}\bar{w}} \sum_{[[i1]]} \sum_{[[i2]]} |w_{[[i1]]} - w_{[[i2]]}|",
                  r"w_{[[i1]]}([[x1]]) \geq w_{[[i1]]}([[x2]]) \text{ for all } [[i1]] \to W([[x1]]) \geq W([[x2]])",
                  r"w_{[[i1]]}([[x1]]) < w_{[[i1]]}([[x2]]) \text{ for all } [[i1]]",
                  r"w_{[[i1]]}([[x1]]) \geq \theta \text{ for all } [[i1]]",
                  r"G([[x1]]) < G([[x2]]) \wedge W([[x1]]) < W([[x2]])"],
        swaps=[(r"the egalitarian view that a benefit matters more the worse off its recipient is in absolute terms",
                r"the prioritarian view that a benefit matters more the worse off its recipient is in absolute terms"),
               (r"levelling up", r"levelling down"),
               (r"a strictly convex transformation of well-being", r"a strictly concave transformation of well-being"),
               (r"relative position", r"absolute level"),
               (r"deontic egalitarianism", r"telic egalitarianism")],
        inserts=[(r"worse off", r"than others"), (r"threshold", r"of sufficiency")],
        index_terms=["equality", "priority view", "levelling-down objection", "sufficiency",
                     "measurement of inequality"]),
    "VALUE": dict(
        terms=["isolation", "supervenience", "profile", "component", "endorsement", "idealized",
               "reflective", "convergence", "outcome", "irreducible", "pluralism", "monism"],
        formulas=[r"[[x1]]_{-F} = [[x2]]_{-F} \wedge [[x1]]_{F} \neq [[x2]]_{F} \wedge V([[x1]]) \neq V([[x2]])",
                  r"[[x1]] \succ [[x2]] \iff V([[x1]]) > V([[x2]])",
                  r"\forall [[x1]]\,\forall [[x2]]\,([[x1]]|_{S} = [[x2]]|_{S} \to V([[x1]]) = V([[x2]]))",
                  r"[[x1]]|_{S} = [[x2]]|_{S} \wedge V([[x1]]) \neq V([[x2]])",
                  r"W_{[[i1]]}([[x1]]) = W_{[[i1]]}([[x2]]) \text{ for all } [[i1]] \wedge F([[x1]]) \neq F([[x2]])"],
        swaps=[(r"supervenes on every set of components that omits fairness",
                r"does not supervene on any set of components that omits fairness"),
               (r"Definition~3.2 of Volume~I (the isolation test)", r"Definition~4.1 of Volume~I (the isolation test)"),
               (r"Definition~4.1 of Volume~I (the good)", r"Definition~3.2 of Volume~I (the good)"),
               (r"Theorem~5.2 of Volume~I (the isolation results)", r"Assumption~5.1 of Volume~I (the isolation results)"),
               (r"Assumption~5.1 of Volume~I (plurality)", r"Theorem~5.2 of Volume~I (plurality)"),
               (r"a good for persons", r"a good of outcomes")],
        inserts=[(r"isolation test", r"relative to the other six components"),
                 (r"idealized reflective endorsement", r"from the impartial standpoint")],
        index_terms=["isolation test", "supervenience", "idealized reflective endorsement",
                     "goods of outcomes"]),
    "DESERT": dict(
        terms=["desert", "deserving", "merit", "responsibility", "entitlement", "proportionality"],
        formulas=[r"d_{[[i1]]} > d_{[[i2]]} \to s_{[[i1]]} \geq s_{[[i2]]}",
                  r"F([[x1]]) = -\sum_{[[i1]]} |s_{[[i1]]} - d_{[[i1]]}|",
                  r"s_{[[i1]]} / d_{[[i1]]} = s_{[[i2]]} / d_{[[i2]]}"],
        swaps=[(r"desert-insensitive", r"desert-sensitive"),
               (r"comparative desert", r"noncomparative desert")],
        inserts=[(r"desert", r"of the recipient")],
        index_terms=["desert", "comparative desert"]),
    "GENER": dict(
        terms=["generations", "intergenerational", "savings", "discounting", "posterity",
               "non-identity", "contemporaries"],
        formulas=[r"\sum_{t} \delta^{t} w_{t}([[x1]]), \quad \delta = 1",
                  r"w_{t+1}([[x1]]) \geq w_{t}([[x1]])",
                  r"F([[x1]]) \neq F([[x2]]) \wedge \sum_{t} w_{t}([[x1]]) = \sum_{t} w_{t}([[x2]])"],
        swaps=[(r"a positive pure rate of time preference", r"a zero pure rate of time preference")],
        inserts=[(r"generations", r"that do not overlap")],
        index_terms=["future generations", "non-identity problem", "just savings"]),
    "AGG": dict(
        terms=["aggregation", "numbers", "contractualist", "tie-breaking", "individualist",
               "pairwise", "redundancy"],
        formulas=[r"\pi_{A} = \frac{n_{A}}{n_{A} + n_{B}}",
                  r"\pi_{A} = \pi_{B} = \tfrac{1}{2}",
                  r"n_{A} > n_{B} \to A \succ B"],
        swaps=[(r"the numbers do not count", r"the numbers count"),
               (r"the tie-breaking argument assumes aggregation", r"the tie-breaking argument does not assume aggregation")],
        inserts=[(r"pairwise comparison", r"of individual claims")],
        index_terms=["the numbers", "tie-breaking argument", "aggregation"]),
    "PROC": dict(
        terms=["procedural", "impartiality", "consent", "legitimacy", "reciprocity", "cooperation"],
        formulas=[r"P([[x1]]) \wedge \neg P([[x2]]) \wedge [[x1]]_{-F} = [[x2]]_{-F}"],
        swaps=[(r"pure procedural justice", r"imperfect procedural justice")],
        inserts=[(r"procedure", r"to which everyone consented")],
        index_terms=["procedural fairness", "fair play"]),
}

CHAPTERS = [
    ("Fairness as a component of the good", 1165, ["INTRO", "FAIR"],
     ["Broome1990", "Rawls1971", "Moore1903", "Ross1930", "Sidgwick1907", "Hooker2005"], "Fairness as a component"),
    ("The isolation test for fairness", 1186, ["VALUE", "FAIR"],
     ["Moore1903", "Broome1990", "Hooker2005", "Ross1930"], "The isolation test"),
    ("Fairness and equality", 1219, ["EQ"],
     ["Temkin1993", "Frankfurt1987", "Anderson1999", "Sen1973", "Atkinson1970", "Dworkin1981"], "Fairness and equality"),
    ("Lotteries and indivisible goods", 1248, ["FAIR"],
     ["Broome1990", "Diamond1967", "Harsanyi1955", "Wasserman1996", "Stone2011", "Elster1989"], "Lotteries"),
    ("Claims and their satisfaction", 1284, ["FAIR"],
     ["Broome1990", "Broome1991", "Hooker2005", "Kamm1993"], "Claims"),
    ("Priority, sufficiency and levelling down", 1322, ["EQ"],
     ["Parfit1997", "Temkin1993", "McKerlie1994", "Crisp2003", "Frankfurt1987", "Otsuka2009", "Holtug2010"],
     "Priority and sufficiency"),
    ("Procedural and outcome fairness", 1361, ["PROC", "FAIR"],
     ["Rawls1958", "Rawls1971", "Nozick1974", "Hart1955", "Barry1989"], "Procedural fairness"),
    ("Fairness across generations", 1393, ["GENER"], ["Parfit1984", "Rawls1971", "Barry1989"],
     "Fairness across generations"),
    ("Fairness and desert", 1421, ["DESERT"],
     ["Feinberg1970", "Sher1987", "Kagan2012", "Miller1999", "Aristotle"], "Fairness and desert"),
    ("Fairness is not a component of well-being", 1447, ["VALUE", "EQ"],
     ["Arneson1989", "Cohen1989", "Parfit1984", "Scanlon1998", "Hirose2015"], "Fairness and well-being"),
    ("Aggregation and the numbers", 1478, ["AGG"],
     ["Taurek1977", "Kamm1993", "Scanlon1998", "Otsuka2009"], "Aggregation and the numbers"),
    ("Summary: fairness in the list of goods", 1508, ["INTRO", "VALUE"],
     ["Broome1990", "Rawls1971", "Temkin1993"], "Summary"),
    ("Bibliography", 1521, [], [], "Bibliography", "bib"),
    ("Index of names", 1549, [], [], "Index of names", "names"),
    ("Index of subjects", 1553, [], [], "Index of subjects", "subjects"),
]
VSTART, VEND = 1161, 1559

ITEM_OVERRIDES = {2: {6: ("Theorem", 1203)}, 4: {5: ("Proposition", 1268), 8: ("Theorem", 1276)},
                  10: {4: ("Theorem", 1459)}}
DISPLAY_OVERRIDES = {2: {4: 1197}}
RESERVED = [1197, 1198, 1203, 1252, 1268, 1276, 1349, 1351, 1459, 1515]
POINTERS = [
    (2, 1197, 10, r"display (2.4)", r"\textit{see} Erratum~E1"),
    (4, 1252, 9, r"l.~9", r"\textit{see} Erratum~E3"),
    (4, 1268, 1, r"Proposition~4.5", r"\textit{see} Erratum~E2"),
    (6, 1349, 38, r"l.~3 from foot", r"\textit{see} Erratum~E4"),
    (10, 1459, 1, r"proof of Theorem~10.4", r"\textit{see} Erratum~E5"),
    (12, 1515, 18, r"l.~18", r"\textit{see} Erratum~E6"),
    (13, 1528, 0, r"Diamond, P.~A. (1967)", r"\textit{see} Erratum~E3"),
]

TOPICS = [("well-being", 2, None), ("knowledge", 2, None), ("achievement", 3, None),
          ("relationships", 3, None), ("beauty", 5, None), ("autonomy", 5, None),
          ("the completeness of the list", 6, None),
          ("the method of isolation", 1, 4), ("idealized reflective endorsement", 1, 3),
          ("incommensurability and parity", 1, 6), ("the refutation of monism", 1, 7),
          ("the formal argument for plurality", 1, 5), ("the concept of the good", 1, 2),
          ("the seven components introduced", 1, 8),
          ("lotteries", 4, 4), ("the claims account", 4, 5), ("levelling down", 4, 6),
          ("procedural fairness", 4, 7), ("desert", 4, 9), ("fairness across generations", 4, 8),
          ("the numbers", 4, 11), ("fairness and equality", 4, 3)]

VOL1_ITEMS = [("Definition", "3.1"), ("Definition", "3.2"), ("Definition", "4.1"),
              ("Assumption", "5.1"), ("Theorem", "5.2"), ("Corollary", "5.3"), ("Corollary", "5.4")]

DENSITY = 3.0
DENSITY_BACK = {"bib": 1.0, "names": 6.0, "subjects": 4.0}
MIX_DISC = [("formula", 18), ("typo", 36), ("xref", 13), ("xref_out", 5), ("pageref", 5),
            ("cite", 11), ("swap", 6), ("insert", 6), ("topic", 4)]
MIX_INTRO = [("typo", 48), ("topic", 14), ("xref_out", 6), ("cite", 14), ("pageref", 6),
             ("swap", 6), ("insert", 6)]


def build():
    rng = __import__("random").Random(SEED)
    chapters = []
    for k, spec in enumerate(CHAPTERS, 1):
        title, start, groups, cites, short = spec[:5]
        special = spec[5] if len(spec) > 5 else None
        end = (CHAPTERS[k][1] - 1) if k < len(CHAPTERS) else VEND
        num = k if not special else 0
        c = Chapter(4, num, title, start, end, groups, cites, special)
        c.short = short
        if not special:
            dens = 0.15 if groups[0] == "INTRO" else 0.33
            build_items(c, rng, dens, ITEM_OVERRIDES.get(k, {}))
            build_displays(c, rng, 0.5 if groups[0] != "INTRO" else 0.2, DISPLAY_OVERRIDES.get(k, {}))
        chapters.append(c)
    vol = Volume(4, "Fairness", VSTART, VEND, chapters)
    vol1 = Chapter(1, 0, "Volume I", 1, 402, [], [])
    vol1.items = [Item(k, n, None, 1, int(n.split(".")[0]), i) for i, (k, n) in enumerate(VOL1_ITEMS, 1)]
    book = Book([vol], True, GROUPS, BIB, TOPICS, {1: 10, 4: 12}, PUBLISHER_CONFUSIONS,
                lambda v, c: [vol1], RESERVED)
    book.all_volume_nums = [1, 2, 3, 4, 5, 6]
    book.protected = {"5.3", "5.4"}
    book.typo_limit = 2
    return book, vol


def main():
    book, vol = build()
    gen = Generator(book, SEED)
    parts = []
    nent = 0
    # front matter: one misprint in the Contents
    c = gen.rng.choice([c for c in vol.chapters if c.num > 1])
    wrong = transpose_digits(c.start, gen.rng, vol.start, vol.end)
    parts.append(r"\subsection*{{Front matter \hfill \normalfont\small pp.~{}--{}}}".format(
        gen.P(vol.start), gen.P(vol.chapters[0].start - 1)) + "\n\\begin{errlist}\n" +
        r"{} & Contents, Chapter~{} & {} \\".format(gen.P(vol.start + 2), c.num,
                                                  forread(gen.P(wrong), gen.P(c.start))) +
        "\n\\end{errlist}\n")
    nent += 1
    gen.counts["xref"] = gen.counts.get("xref", 0) + 1
    for k, c in enumerate(vol.chapters, 1):
        if c.special:
            n = int(round(c.pages * DENSITY_BACK[c.special]))
            es = gen.chapter_entries(vol, c, n, [(c.special, 1)])
        else:
            mix = MIX_INTRO if c.groups[0] == "INTRO" else MIX_DISC
            es = gen.chapter_entries(vol, c, int(round(c.pages * DENSITY)), mix)
            if gen.rng.random() < 0.25:
                rh = gen.running_head(vol, c)
                if rh:
                    es.append(rh)
        for e in es:
            assert c.start <= e.page <= c.end
        ptrs = [(p[1], p[2], p[3], p[4]) for p in POINTERS if p[0] == k]
        tex, cnt = latex_chapter(c, es, gen.P, ptrs)
        parts.append(tex)
        nent += cnt - len(ptrs)
    with open(os.path.join(HERE, "vol04.tex"), "w", encoding="utf-8") as f:
        f.write("% generated by generate.py -- do not edit\n" + "\n".join(parts))
    lines = [r"% generated by generate.py -- do not edit", r"\begin{skeltab}",
             r" & Front matter & {}--{} \\".format(gen.P(vol.start), gen.P(vol.chapters[0].start - 1))]
    for c in vol.chapters:
        lines.append(r"{} & {} & {}--{} \\".format("" if c.special else c.num, c.title,
                                                   gen.P(c.start), gen.P(c.end)))
    lines.append(r"\end{skeltab}")
    with open(os.path.join(HERE, "skeleton.tex"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
    labels = [("typo", "Typographical errors (spelling, running heads)"),
              ("wording", "Wrong word or phrase"), ("omission", "Omitted or repeated words"),
              ("formula", "Misprinted formulas and symbols"),
              ("xref", "Cross-references and page references"),
              ("citation", "Citations in the text"), ("bibliography", "Bibliography"),
              ("index", "Indices")]
    rows = [r"% generated by generate.py -- do not edit", r"\begin{tabular}{@{}lr@{}}", r"\toprule"]
    for key, lab in labels:
        rows.append(r"{} & {} \\".format(lab, gen.counts.get(key, 0)))
    rows += [r"\midrule", r"Total & {} \\".format(sum(gen.counts.values())), r"\bottomrule", r"\end{tabular}"]
    with open(os.path.join(HERE, "stats.tex"), "w", encoding="utf-8") as f:
        f.write("\n".join(rows) + "\n")
    print("entries:", nent, gen.counts)
    print("Diamond bib page:", book.bib_page("Diamond1967", vol.chapters[12]))


if __name__ == "__main__":
    main()
