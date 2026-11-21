"""Generator for REL-01-h, Corrigenda to On the Existence of God, Volumes III-XI.

Run `python3 generate.py` in this directory.  Writes skeleton.tex, stats.tex
and vol03.tex ... vol11.tex.  Deterministic (random.Random(SEED)).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from errata_engine import (Book, Chapter, Item, Volume, Generator, ROMAN,  # noqa: E402
                           build_items, build_displays, build_lemma_items,
                           latex_chapter, fmt_page)

SEED = 20261007
HERE = os.path.dirname(os.path.abspath(__file__))

# ---------------------------------------------------------------------------
# bibliography (real works; only details we are sure of)
# ---------------------------------------------------------------------------

OUP_LIKE = ["Clarendon Press", "Oxford University Press", "Cambridge University Press",
            "Cornell University Press", "Princeton University Press", "Harvard University Press"]

BIB = {
    "Adams1972": dict(authors=[("Adams", "R.~M.")], year=1972, title="Must God create the best?",
                      journal="The Philosophical Review", vol="81(3)", pages="317--332",
                      topic="whether God must create the best"),
    "Alston1989": dict(authors=[("Alston", "W.~P.")], year=1989,
                       title="Divine Nature and Human Language", publisher="Cornell University Press"),
    "Anderson1990": dict(authors=[("Anderson", "C.~A.")], year=1990,
                         title="Some emendations of Gödel's ontological proof",
                         journal="Faith and Philosophy", vol="7(3)", pages="291--303",
                         topic="the emended positivity axioms"),
    "Barcan1946": dict(authors=[("Barcan", "R.~C.")], year=1946,
                       title="A functional calculus of first order based on strict implication",
                       journal="The Journal of Symbolic Logic", vol="11(1)", pages="1--16",
                       topic="the Barcan formula"),
    "Barrett2004": dict(authors=[("Barrett", "J.~L.")], year=2004,
                        title="Why Would Anyone Believe in God?", publisher="AltaMira Press"),
    "Benzmuller2014": dict(authors=[("Benzmüller", "C."), ("Woltzenlogel Paleo", "B.")], year=2014,
                           title="Automating Gödel's ontological proof of God's existence with higher-order automated theorem provers",
                           inbook="Proceedings of the 21st European Conference on Artificial Intelligence (ECAI 2014)",
                           eds="T.~Schaub, G.~Friedrich and B.~O'Sullivan (Eds.)", pages="93--98",
                           publisher="IOS Press"),
    "Bergmann2001": dict(authors=[("Bergmann", "M.")], year=2001,
                         title="Skeptical theism and Rowe's new evidential argument from evil",
                         journal="Noûs", vol="35(2)", pages="278--296",
                         topic="sceptical theism"),
    "Blackburn2001": dict(authors=[("Blackburn", "P."), ("de Rijke", "M."), ("Venema", "Y.")], year=2001,
                          title="Modal Logic", publisher="Cambridge University Press"),
    "Chandler1976": dict(authors=[("Chandler", "H.~S.")], year=1976,
                         title="Plantinga and the contingently possible",
                         journal="Analysis", vol="36(2)", pages="106--109",
                         topic="the failure of S4 for metaphysical modality"),
    "Chellas1980": dict(authors=[("Chellas", "B.~F.")], year=1980,
                        title="Modal Logic: An Introduction", publisher="Cambridge University Press"),
    "Craig1979": dict(authors=[("Craig", "W.~L.")], year=1979,
                      title="The Kalām Cosmological Argument", publisher="Macmillan"),
    "Draper1989": dict(authors=[("Draper", "P.")], year=1989,
                       title="Pain and pleasure: An evidential problem for theists",
                       journal="Noûs", vol="23(3)", pages="331--350",
                       topic="the hypothesis of indifference"),
    "Fine1994": dict(authors=[("Fine", "K.")], year=1994, title="Essence and modality",
                     journal="Philosophical Perspectives", vol="8", pages="1--16",
                     topic="essence and modality"),
    "Fitting1998": dict(authors=[("Fitting", "M."), ("Mendelsohn", "R.~L.")], year=1998,
                        title="First-Order Modal Logic", publisher="Kluwer Academic Publishers"),
    "Fitting2002": dict(authors=[("Fitting", "M.")], year=2002,
                        title="Types, Tableaus, and Gödel's God", publisher="Kluwer Academic Publishers"),
    "Frankfurt1964": dict(authors=[("Frankfurt", "H.~G.")], year=1964, title="The logic of omnipotence",
                          journal="The Philosophical Review", vol="73(2)", pages="262--263",
                          topic="the paradox of the stone"),
    "Gale1999": dict(authors=[("Gale", "R.~M."), ("Pruss", "A.~R.")], year=1999,
                     title="A new cosmological argument", journal="Religious Studies",
                     vol="35(4)", pages="461--476", topic="a weak principle of sufficient reason"),
    "Gallin1975": dict(authors=[("Gallin", "D.")], year=1975,
                       title="Intensional and Higher-Order Modal Logic", publisher="North-Holland"),
    "Godel1995": dict(authors=[("Gödel", "K.")], year=1995, title="Ontological proof",
                      inbook="Collected Works, Volume III: Unpublished Essays and Lectures",
                      eds="S.~Feferman et al. (Eds.)", pages="403--404",
                      publisher="Oxford University Press", no_errata=True),
    "Grim1983": dict(authors=[("Grim", "P.")], year=1983, title="Some neglected problems of omniscience",
                     journal="American Philosophical Quarterly", vol="20(3)",
                     topic="the Cantorian argument against omniscience"),
    "Grim1991": dict(authors=[("Grim", "P.")], year=1991, title="The Incomplete Universe",
                     publisher="MIT Press"),
    "Hajek2002": dict(authors=[("Hájek", "P.")], year=2002,
                      title="A new small emendation of Gödel's ontological proof",
                      journal="Studia Logica", vol="71", pages="149--164"),
    "Hartshorne1962": dict(authors=[("Hartshorne", "C.")], year=1962, title="The Logic of Perfection",
                           publisher="Open Court"),
    "Hasker1989": dict(authors=[("Hasker", "W.")], year=1989, title="God, Time, and Knowledge",
                       publisher="Cornell University Press"),
    "Henkin1950": dict(authors=[("Henkin", "L.")], year=1950, title="Completeness in the theory of types",
                       journal="The Journal of Symbolic Logic", vol="15(2)", pages="81--91",
                       topic="general models of type theory"),
    "Hick1966": dict(authors=[("Hick", "J.")], year=1966, title="Evil and the God of Love",
                     publisher="Macmillan"),
    "Hoffman2002": dict(authors=[("Hoffman", "J."), ("Rosenkrantz", "G.~S.")], year=2002,
                        title="The Divine Attributes", publisher="Blackwell"),
    "HughesCresswell1996": dict(authors=[("Hughes", "G.~E."), ("Cresswell", "M.~J.")], year=1996,
                                title="A New Introduction to Modal Logic", publisher="Routledge"),
    "Kenny1979": dict(authors=[("Kenny", "A.")], year=1979, title="The God of the Philosophers",
                      publisher="Clarendon Press"),
    "Koons1997": dict(authors=[("Koons", "R.~C.")], year=1997, title="A new look at the cosmological argument",
                      journal="American Philosophical Quarterly", vol="34(2)", pages="193--211",
                      topic="the cosmological argument from contingency"),
    "Kraay2010": dict(authors=[("Kraay", "K.~J.")], year=2010,
                      title="Theism, possible worlds, and the multiverse",
                      journal="Philosophical Studies", vol="147(3)", pages="355--368",
                      topic="the theistic multiverse"),
    "Kretzmann1966": dict(authors=[("Kretzmann", "N.")], year=1966, title="Omniscience and immutability",
                          journal="The Journal of Philosophy", vol="63(14)", pages="409--421",
                          topic="omniscience and change"),
    "Kripke1963a": dict(authors=[("Kripke", "S.~A.")], year=1963, suffix="a",
                        title="Semantical analysis of modal logic I: Normal modal propositional calculi",
                        journal="Zeitschrift für mathematische Logik und Grundlagen der Mathematik",
                        vol="9", pages="67--96"),
    "Kripke1963b": dict(authors=[("Kripke", "S.~A.")], year=1963, suffix="b",
                        title="Semantical considerations on modal logic",
                        journal="Acta Philosophica Fennica", vol="16", pages="83--94"),
    "Kripke1980": dict(authors=[("Kripke", "S.~A.")], year=1980, title="Naming and Necessity",
                       publisher="Harvard University Press"),
    "Leftow2012": dict(authors=[("Leftow", "B.")], year=2012, title="God and Necessity",
                       publisher="Oxford University Press"),
    "Leslie1989": dict(authors=[("Leslie", "J.")], year=1989, title="Universes", publisher="Routledge"),
    "Lewis1970": dict(authors=[("Lewis", "D.")], year=1970, title="Anselm and actuality",
                      journal="Noûs", vol="4(2)", pages="175--188",
                      topic="the indexical reading of actuality"),
    "Mackie1955": dict(authors=[("Mackie", "J.~L.")], year=1955, title="Evil and omnipotence",
                       journal="Mind", vol="64(254)", pages="200--212",
                       topic="the logical problem of evil"),
    "Mackie1982": dict(authors=[("Mackie", "J.~L.")], year=1982, title="The Miracle of Theism",
                       publisher="Clarendon Press"),
    "Malcolm1960": dict(authors=[("Malcolm", "N.")], year=1960, title="Anselm's ontological arguments",
                        journal="The Philosophical Review", vol="69(1)", pages="41--62",
                        topic="Anselm's second argument"),
    "Mann1982": dict(authors=[("Mann", "W.~E.")], year=1982, title="Divine simplicity",
                     journal="Religious Studies", vol="18(4)", pages="451--471",
                     topic="the property account of simplicity"),
    "Mavrodes1963": dict(authors=[("Mavrodes", "G.~I.")], year=1963,
                         title="Some puzzles concerning omnipotence",
                         journal="The Philosophical Review", vol="72(2)", pages="221--223",
                         topic="the paradox of the stone"),
    "Morris1987": dict(authors=[("Morris", "T.~V.")], year=1987, title="Anselmian Explorations",
                       publisher="University of Notre Dame Press"),
    "Oppenheimer2011": dict(authors=[("Oppenheimer", "P.~E."), ("Zalta", "E.~N.")], year=2011,
                            title="A computationally-discovered simplification of the ontological argument",
                            journal="Australasian Journal of Philosophy", vol="89(2)", pages="333--349",
                            topic="the computational simplification of Anselm's argument"),
    "Oppy1995": dict(authors=[("Oppy", "G.")], year=1995, title="Ontological Arguments and Belief in God",
                     publisher="Cambridge University Press"),
    "Oppy2006": dict(authors=[("Oppy", "G.")], year=2006, title="Arguing about Gods",
                     publisher="Cambridge University Press"),
    "Pike1965": dict(authors=[("Pike", "N.")], year=1965, title="Divine omniscience and voluntary action",
                     journal="The Philosophical Review", vol="74(1)", pages="27--46",
                     topic="foreknowledge and voluntary action"),
    "Pike1969": dict(authors=[("Pike", "N.")], year=1969, title="Omnipotence and God's ability to sin",
                     journal="American Philosophical Quarterly", vol="6(3)", pages="208--216",
                     topic="omnipotence and the ability to sin"),
    "Plantinga1967": dict(authors=[("Plantinga", "A.")], year=1967, title="God and Other Minds",
                          publisher="Cornell University Press"),
    "Plantinga1974a": dict(authors=[("Plantinga", "A.")], year=1974, suffix="a",
                           title="God, Freedom, and Evil", publisher="Harper \\& Row"),
    "Plantinga1974b": dict(authors=[("Plantinga", "A.")], year=1974, suffix="b",
                           title="The Nature of Necessity", publisher="Clarendon Press"),
    "Plantinga1980": dict(authors=[("Plantinga", "A.")], year=1980, title="Does God Have a Nature?",
                          publisher="Marquette University Press"),
    "Plantinga2011": dict(authors=[("Plantinga", "A.")], year=2011, title="Where the Conflict Really Lies",
                          publisher="Oxford University Press"),
    "Pruss2006": dict(authors=[("Pruss", "A.~R.")], year=2006,
                      title="The Principle of Sufficient Reason: A Reassessment",
                      publisher="Cambridge University Press"),
    "Rowe1975": dict(authors=[("Rowe", "W.~L.")], year=1975, title="The Cosmological Argument",
                     publisher="Princeton University Press"),
    "Rowe1979": dict(authors=[("Rowe", "W.~L.")], year=1979,
                     title="The problem of evil and some varieties of atheism",
                     journal="American Philosophical Quarterly", vol="16(4)", pages="335--341",
                     topic="the evidential argument from evil"),
    "Rowe2004": dict(authors=[("Rowe", "W.~L.")], year=2004, title="Can God Be Free?",
                     publisher="Clarendon Press"),
    "Salmon1989": dict(authors=[("Salmon", "N.")], year=1989, title="The logic of what might have been",
                       journal="The Philosophical Review", vol="98(1)", pages="3--34",
                       topic="the rejection of S4"),
    "Savage1967": dict(authors=[("Savage", "C.~W.")], year=1967, title="The paradox of the stone",
                       journal="The Philosophical Review", vol="76(1)", pages="74--79",
                       topic="the paradox of the stone"),
    "Schellenberg1993": dict(authors=[("Schellenberg", "J.~L.")], year=1993,
                             title="Divine Hiddenness and Human Reason",
                             publisher="Cornell University Press"),
    "Sobel1987": dict(authors=[("Sobel", "J.~H.")], year=1987, title="Gödel's ontological proof",
                      inbook="On Being and Saying: Essays for Richard Cartwright",
                      eds="J.~J. Thomson (Ed.)", pages="241--261", publisher="MIT Press"),
    "Sobel2004": dict(authors=[("Sobel", "J.~H.")], year=2004,
                      title="Logic and Theism: Arguments for and against Beliefs in God",
                      publisher="Cambridge University Press"),
    "Street2006": dict(authors=[("Street", "S.")], year=2006,
                       title="A Darwinian dilemma for realist theories of value",
                       journal="Philosophical Studies", vol="127(1)", pages="109--166",
                       topic="the Darwinian dilemma"),
    "Stump1981": dict(authors=[("Stump", "E."), ("Kretzmann", "N.")], year=1981, title="Eternity",
                      journal="The Journal of Philosophy", vol="78(8)", pages="429--458",
                      topic="atemporal eternity"),
    "Swinburne1993": dict(authors=[("Swinburne", "R.")], year=1993,
                          title="The Coherence of Theism (rev. ed.)", publisher="Clarendon Press"),
    "Swinburne2004": dict(authors=[("Swinburne", "R.")], year=2004,
                          title="The Existence of God (2nd ed.)", publisher="Clarendon Press"),
    "vanInwagen1977": dict(authors=[("van Inwagen", "P.")], year=1977, title="Ontological arguments",
                           journal="Noûs", vol="11(4)", pages="375--395",
                           topic="the symmetry of the modal ontological argument"),
    "vanInwagen2006": dict(authors=[("van Inwagen", "P.")], year=2006, title="The Problem of Evil",
                           publisher="Clarendon Press"),
    "Wierenga1989": dict(authors=[("Wierenga", "E.~R.")], year=1989, title="The Nature of God",
                         publisher="Cornell University Press"),
    "Williamson2013": dict(authors=[("Williamson", "T.")], year=2013, title="Modal Logic as Metaphysics",
                           publisher="Oxford University Press"),
    "Wykstra1984": dict(authors=[("Wykstra", "S.~J.")], year=1984,
                        title="The Humean obstacle to evidential arguments from suffering: On avoiding the evils of `appearance'",
                        journal="International Journal for Philosophy of Religion", vol="16(2)",
                        pages="73--93", topic="the condition of reasonable epistemic access"),
    "Zagzebski1991": dict(authors=[("Zagzebski", "L.~T.")], year=1991,
                          title="The Dilemma of Freedom and Foreknowledge",
                          publisher="Oxford University Press"),
    # classics: cited by work and section; only section slips are generated
    "Anselm": dict(authors=[("Anselm", "")], year=1078, classic=True, title="Proslogion",
                   slips=[(r"\emph{Proslogion}~4 (that God cannot be conceived not to exist)",
                           r"\emph{Proslogion}~3 (that God cannot be conceived not to exist)")]),
    "Gaunilo": dict(authors=[("Gaunilo", "")], year=1079, classic=True, title="Pro insipiente",
                    slips=[(r"Gaunilo, \emph{Pro insipiente}~5 (the lost island)",
                            r"Gaunilo, \emph{Pro insipiente}~6 (the lost island)")]),
    "Descartes": dict(authors=[("Descartes", "R.")], year=1641, classic=True, title="Meditationes",
                      slips=[(r"Descartes, Meditation~III (the supremely perfect being whose essence includes existence)",
                              r"Descartes, Meditation~V (the supremely perfect being whose essence includes existence)")]),
    "Kant": dict(authors=[("Kant", "I.")], year=1781, classic=True, title="Kritik der reinen Vernunft",
                 slips=[(r"Kant, A592/B602", r"Kant, A592/B620")]),
    "Leibniz": dict(authors=[("Leibniz", "G.~W.")], year=1714, classic=True, title="Monadologie",
                    slips=[(r"Leibniz, \emph{Monadology}~\S 54 (the necessary being exists if it is possible)",
                            r"Leibniz, \emph{Monadology}~\S 45 (the necessary being exists if it is possible)")]),
    "Hume": dict(authors=[("Hume", "D.")], year=1779, classic=True, title="Dialogues",
                 slips=[(r"Hume, \emph{Dialogues}, Part~XI (the a priori argument)",
                         r"Hume, \emph{Dialogues}, Part~IX (the a priori argument)"),
                        (r"Hume, \emph{Dialogues}, Part~IX (the argument from evil)",
                         r"Hume, \emph{Dialogues}, Parts~X--XI (the argument from evil)")]),
    "Aquinas": dict(authors=[("Aquinas", "T.")], year=1274, classic=True, title="Summa Theologiae",
                    slips=[(r"\emph{Summa Theologiae} I, q.~3, a.~2 (the five ways)",
                            r"\emph{Summa Theologiae} I, q.~2, a.~3 (the five ways)"),
                           (r"\emph{Summa Theologiae} I, q.~25, a.~4 (whether God is omnipotent)",
                            r"\emph{Summa Theologiae} I, q.~25, a.~3 (whether God is omnipotent)")]),
    "Spinoza": dict(authors=[("Spinoza", "B.")], year=1677, classic=True, title="Ethica",
                    slips=[(r"Spinoza, \emph{Ethics} I, P14 (God necessarily exists)",
                            r"Spinoza, \emph{Ethics} I, P11 (God necessarily exists)")]),
}

PUBLISHER_CONFUSIONS = {p: [q for q in OUP_LIKE if q != p] for p in OUP_LIKE}
PUBLISHER_CONFUSIONS["Routledge"] = ["Blackwell"]
PUBLISHER_CONFUSIONS["Blackwell"] = ["Routledge"]
PUBLISHER_CONFUSIONS["MIT Press"] = ["Harvard University Press", "Cambridge University Press"]
PUBLISHER_CONFUSIONS["Macmillan"] = ["Routledge"]
PUBLISHER_CONFUSIONS["Kluwer Academic Publishers"] = ["North-Holland"]
PUBLISHER_CONFUSIONS["North-Holland"] = ["Kluwer Academic Publishers"]

EXTRA_WORDS = """
absolutely abstract accordingly according account achieve additional address adequate
admittedly advantage alternative although ambiguity ambiguous analysis anticipate apparent
apparently application approach argued arguably assertion assessment attribute available
believe beneficial between capacity carefully category certainly challenge circumstance
claimed clarify classical combination comparable comparison complete conception concerned
condition conditional conjecture connection conscious consensus considerable constraint
construction contemporary content context contingent contrary contrast contribution
controversy convention conviction correctly corresponding criterion critical currently
decisive defended defender deficiency definition deliberate denial dependence describe
description desirable despite determinate develop development difference different
difficulty dilemma directly disagreement discussion dispute distinguish divine doctrine
effectively elsewhere emphasis empirical employed encounter entirely equally equivalent
especially essential establish evaluate eventually evidence evident exactly example
exception exclusion exercise explanation explicit expression extension external
familiar formulation fortiori framework fundamental further generally genuine government
guarantee hitherto however identical identify illustrate immediate implication implicit
importance impossible including inconsistent indeed indicate individual inevitable
initially instance instead intended interest intrinsic introduce intuitive invariant
judgement knowledge language latter literature logically maintain manifest material
meaning mechanism mention merely method modest moreover motivation namely naturally
neither notation nothing notion objection objective observation obtain obvious
occasionally omitted opponent opposite ordinary original otherwise paradigm paragraph
particularly perhaps permissible perspective phenomenon plausible position possession
practical precisely preference premise presence presumably previous primarily principal
probable problem procedure proceed process proponent proposal prospect provided purpose
question quantifier rather reasonable recognize reference regarded regardless remainder
remarkable represent requirement resemblance resistance response restriction rigorous
satisfied scenario section sentence sequence serious significant similarly simplicity
situation slightly solution something specific statement straightforward strategy
strength strictly structure subsequent succeed successful suggestion suppose surely
systematic technical tendency terminology theorem thereby thorough tradition transition
treatment ultimately undermine understanding uniform universal unless validity variation
various version virtually whereas whenever withdrawn"""
EXTRA_WORDS = [w for w in EXTRA_WORDS.split() if len(w) >= 6]

# ---------------------------------------------------------------------------
# vocabulary groups
# ---------------------------------------------------------------------------

GROUPS = {
    "GEN": dict(
        terms=["argument", "conclusion", "consequently", "nevertheless", "independently",
               "interpretation", "distinction", "consideration", "assumption", "demonstrate",
               "preliminary", "occurrence", "necessary", "accommodate", "separate", "definitely",
               "existence", "relevance", "inference", "coherence", "consistent", "independent",
               "dependent", "parallel", "recommend", "occasion", "philosophical", "theological",
               "metaphysical", "epistemic", "substantive", "contradiction", "controversial",
               "commitment", "committed", "occurred", "referred", "transferred", "acknowledge",
               "analogous", "appropriate", "consequence", "embarrassment", "hypothesis",
               "hypotheses", "immediately", "particular", "presupposition", "principle",
               "proposition", "questionable", "receive", "relevant", "respectively",
               "sufficient", "symmetric", "therefore", "throughout", "tradition", "unnecessary",
               "whether", "conceivable", "accessible", "irrelevant", "persuasive", "derivation"]
              + EXTRA_WORDS,
        inserts=[(r"the second occurrence of \emph{the}", "DELETE"),
                 (r"the second occurrence of \emph{of}", "DELETE"),
                 (r"the second occurrence of \emph{is}", "DELETE"),
                 (r"the second occurrence of \emph{that}", "DELETE"),
                 (r"the second occurrence of \emph{a}", "DELETE"),
                 (r"the second occurrence of \emph{to}", "DELETE")]),
    "INTRO": dict(terms=["introduction", "summary", "chapter", "volume", "preceding", "following",
                         "organization", "presentation", "overview"],
                  index_terms=[]),
    "MODAL": dict(
        terms=["accessibility", "reflexivity", "symmetry", "transitivity", "Euclidean",
               "equivalence", "necessity", "possibility", "semantics", "valuation", "schema",
               "characteristic", "metaphysical", "modality", "validity", "soundness",
               "completeness", "frame", "correspondence"],
        formulas=[r"[[w1]]R[[w2]] \wedge [[w2]]R[[w3]] \to [[w1]]R[[w3]]",
                  r"[[w1]]R[[w2]] \to [[w2]]R[[w1]]",
                  r"([[w1]]R[[w2]] \wedge [[w1]]R[[w3]]) \to [[w2]]R[[w3]]",
                  r"\pos\nec [[p1]] \to \nec [[p1]]",
                  r"\nec [[p1]] \to \nec\nec [[p1]]",
                  r"\pos [[p1]] \to \nec\pos [[p1]]",
                  r"\nec([[p1]] \to [[p2]]) \to (\nec [[p1]] \to \nec [[p2]])",
                  r"[[p1]] \to \nec\pos [[p1]]",
                  r"\pos\pos [[p1]] \to \pos [[p1]]",
                  r"[[w1]] \models \nec [[p1]] \iff \forall [[w2]]\,([[w1]]R[[w2]] \to [[w2]] \models [[p1]])",
                  r"[[w1]] \models \pos [[p1]] \iff \exists [[w2]]\,([[w1]]R[[w2]] \wedge [[w2]] \models [[p1]])",
                  r"\nec([[p1]] \wedge [[p2]]) \leftrightarrow (\nec [[p1]] \wedge \nec [[p2]])",
                  r"\pos([[p1]] \vee [[p2]]) \leftrightarrow (\pos [[p1]] \vee \pos [[p2]])",
                  r"\neg\pos [[p1]] \leftrightarrow \nec\neg [[p1]]",
                  r"\pos\nec [[p1]] \to [[p1]]",
                  r"\nec [[p1]] \wedge \pos [[p2]] \to \pos([[p1]] \wedge [[p2]])"],
        swaps=[(r"$[[w1]]R[[w2]]$ by reflexivity", r"$[[w1]]R[[w1]]$ by reflexivity"),
               (r"$[[w2]]R[[w1]]$ by transitivity", r"$[[w2]]R[[w1]]$ by symmetry"),
               (r"$[[w1]]R[[w3]]$ by symmetry", r"$[[w1]]R[[w3]]$ by transitivity"),
               (r"the axiom T, $[[p1]] \to \nec\pos [[p1]]$", r"the axiom B, $[[p1]] \to \nec\pos [[p1]]$"),
               (r"the axiom 4, $\nec [[p1]] \to [[p1]]$", r"the axiom T, $\nec [[p1]] \to [[p1]]$"),
               (r"the axiom B, $\nec [[p1]] \to \nec\nec [[p1]]$", r"the axiom 4, $\nec [[p1]] \to \nec\nec [[p1]]$"),
               (r"the axiom 4, $\pos [[p1]] \to \nec\pos [[p1]]$", r"the axiom 5, $\pos [[p1]] \to \nec\pos [[p1]]$"),
               (r"true at some world accessible from $[[w1]]$ (the clause for $\nec$)",
                r"true at every world accessible from $[[w1]]$ (the clause for $\nec$)"),
               (r"a reflexive and transitive frame validates B",
                r"a reflexive and symmetric frame validates B"),
               (r"Euclidean and symmetric", r"Euclidean and reflexive")],
        inserts=[(r"accessible", r"from $[[w1]]$"), (r"true at every world", r"accessible from $[[w1]]$"),
                 (r"S5 conditions", r"on $R$")],
        index_terms=["accessibility relation", "S5", "Euclidean relation", "axiom B",
                     "axiom 4", "axiom 5", "Kripke semantics", "frame correspondence"]),
    "MG": dict(
        terms=["maximal", "greatness", "excellence", "omnipotent", "omniscient", "morally",
               "perfect", "necessarily", "instantiated", "existence", "maximally"],
        formulas=[r"\mathrm{MG}([[x1]],[[w1]]) \iff \forall [[w2]]\,([[w1]]R[[w2]] \to E([[x1]],[[w2]]) \wedge \mathrm{ME}([[x1]],[[w2]]))",
                  r"\mathrm{MG}([[x1]],[[w1]]) \wedge [[w1]]R[[w2]] \to \mathrm{MG}([[x1]],[[w2]])",
                  r"@ \in \pos\,\exists [[x1]]\, \mathrm{MG}([[x1]],\cdot)",
                  r"@ \in \nec\,\exists [[x1]]\, \mathrm{MG}([[x1]],\cdot)",
                  r"\pos\exists [[x1]]\,\mathrm{MG}([[x1]]) \to \nec\exists [[x1]]\,\mathrm{MG}([[x1]])",
                  r"\pos\neg\exists [[x1]]\,\mathrm{MG}([[x1]]) \to \neg\exists [[x1]]\,\mathrm{MG}([[x1]])",
                  r"\mathrm{ME}([[x1]],[[w1]]) \iff \mathrm{Op}([[x1]],[[w1]]) \wedge \mathrm{Os}([[x1]],[[w1]]) \wedge \mathrm{MP}([[x1]],[[w1]])",
                  r"\mathrm{NE}([[x1]],[[w1]]) \iff \forall [[w2]]\,([[w1]]R[[w2]] \to E([[x1]],[[w2]]))",
                  r"\mathrm{NME}([[x1]],[[w1]]) \iff \forall [[w2]]\,([[w1]]R[[w2]] \to \mathrm{ME}([[x1]],[[w2]]))",
                  r"\exists [[x1]]\,\mathrm{MG}([[x1]],[[w1]]) \to \exists [[x1]]\,(E([[x1]],[[w1]]) \wedge \mathrm{ME}([[x1]],[[w1]]))",
                  r"\pos G \to \neg\pos\neg G",
                  r"\nec(G \to \nec G)",
                  r"\neg(\pos G \wedge \pos\neg G)",
                  r"\mathrm{MG}([[x1]],[[w1]]) \to \mathrm{NE}([[x1]],[[w1]]) \wedge \mathrm{NME}([[x1]],[[w1]])"],
        swaps=[(r"exists and is maximally excellent at some world accessible from $[[w1]]$",
                r"exists and is maximally excellent at every world accessible from $[[w1]]$"),
               (r"necessary existence and maximal excellence", r"necessary existence and necessary maximal excellence"),
               (r"possibly maximally excellent", r"possibly maximally great"),
               (r"the converse premise, Assumption~3.1 of Volume~I", r"the possibility premise, Assumption~3.1 of Volume~I"),
               (r"Theorem~3.4 of Volume~I, the converse argument", r"Proposition~4.1 of Volume~I, the converse argument"),
               (r"Proposition~4.1 of Volume~I, the main result", r"Theorem~3.4 of Volume~I, the main result"),
               (r"Definition~2.2 of Volume~I (maximal greatness)", r"Definition~2.4 of Volume~I (maximal greatness)"),
               (r"Definition~2.4 of Volume~I (maximal excellence)", r"Definition~2.2 of Volume~I (maximal excellence)")],
        inserts=[(r"maximally excellent", r"at $[[w1]]$"), (r"exists", r"at every world accessible from $[[w1]]$")],
        index_terms=["maximal greatness", "maximal excellence", "necessary existence",
                     "possibility premise", "converse premise"]),
    "FILTER": dict(
        terms=["property", "filter", "intersection", "entailment", "conjunction", "positive",
               "positivity", "great-making", "perfection", "instantiable", "compossible",
               "godlike", "essence", "jointly"],
        formulas=[r"[[f1]], [[f2]] \in \mathcal{P} \Rightarrow [[f1]] \sqcap [[f2]] \in \mathcal{P}",
                  r"[[f1]] \in \mathcal{P} \wedge \nec\forall [[x1]]\,([[f1]][[x1]] \to [[f2]][[x1]]) \Rightarrow [[f2]] \in \mathcal{P}",
                  r"\emptyset \notin \mathcal{P}",
                  r"\mathrm{NE}, \mathrm{NME} \in \mathcal{P}",
                  r"\mathcal{P}_0 \subseteq \mathcal{P} \Rightarrow \exists [[x1]]\,\exists [[w1]]\,\forall [[f1]] \in \mathcal{P}_0\; [[f1]]([[x1]],[[w1]])",
                  r"\mathrm{Pos}([[f1]]) \to \pos\exists [[x1]]\,[[f1]][[x1]]",
                  r"\mathrm{Pos}(\neg [[f1]]) \leftrightarrow \neg\mathrm{Pos}([[f1]])",
                  r"\mathrm{G}[[x1]] \leftrightarrow \forall [[f1]]\,(\mathrm{Pos}([[f1]]) \to [[f1]][[x1]])",
                  r"\mathrm{G}[[x1]] \leftrightarrow \forall [[f1]]\,(\mathrm{Pos}([[f1]]) \leftrightarrow \nec [[f1]][[x1]])",
                  r"\mathrm{Pos}([[f1]]) \wedge \mathrm{Pos}([[f2]]) \to \mathrm{Pos}([[f1]] \sqcap [[f2]])",
                  r"\nec\exists [[x1]]\,\mathrm{G}[[x1]]",
                  r"\mathrm{Pos}([[f1]]) \to \nec\mathrm{Pos}([[f1]])",
                  r"\mathcal{P}_0 = \{\mathrm{NE}, \mathrm{NME}\} \subseteq \mathcal{P}"],
        swaps=[(r"closed under disjunction", r"closed under conjunction"),
               (r"the empty property belongs to $\mathcal{P}$", r"the empty property does not belong to $\mathcal{P}$"),
               (r"jointly instantiated at some accessible world", r"jointly instantiated at some one accessible world"),
               (r"every infinite subfamily", r"every finite subfamily"),
               (r"godlike in Gödel's sense", r"godlike in Anderson's sense"),
               (r"closed under entailment and under conjunction (the finite intersection property)",
                r"jointly instantiable in every finite subfamily (the finite intersection property)")],
        inserts=[(r"great-making properties", r"jointly"), (r"proper filter", r"of properties")],
        index_terms=["proper filter", "finite intersection property", "positive property",
                     "great-making property", "godlikeness"]),
    "EPIST": dict(
        terms=["conceivability", "conceivable", "evidence", "support", "symmetry", "credence",
               "probability", "justification", "intuition", "coherent", "defeater", "converse",
               "rational", "a priori"],
        formulas=[r"P(\pos G) > P(\pos\neg G)",
                  r"P(\pos G \mid C) > P(\pos G)",
                  r"P(\pos G) + P(\pos\neg G) \leq 1",
                  r"P(G) = P(\pos G)",
                  r"\mathrm{Conc}([[p1]]) \to \pos [[p1]]",
                  r"\neg\mathrm{Conc}(\neg [[p1]]) \wedge \mathrm{Conc}([[p1]])",
                  r"P([[p1]] \mid [[p2]]) = P([[p2]] \mid [[p1]])\,P([[p1]])/P([[p2]])",
                  r"P(\pos\neg G \mid A) = P(\pos\neg G)"],
        swaps=[(r"positive conceivability", r"negative conceivability"),
               (r"negatively conceivable", r"positively conceivable"),
               (r"evidence of absence", r"absence of evidence"),
               (r"the converse premise is better supported", r"the possibility premise is better supported"),
               (r"bears on the possibility premise", r"bears on the converse premise")],
        inserts=[(r"conceivable", r"on ideal reflection"), (r"supported", r"independently of the conclusion")],
        index_terms=["conceivability", "evidence of absence", "parody objections",
                     "symmetry objection", "ancestral premise"]),
    "ATTR": dict(
        terms=["omnipotence", "omniscience", "perfection", "goodness", "power", "task",
               "knowledge", "proposition", "Cantorian", "compossibility", "attribute",
               "wrongdoing", "aseity", "independence"],
        formulas=[r"\mathrm{Op}([[x1]]) \leftrightarrow \forall t\,(\mathrm{Task}(t) \wedge \neg Q(t,[[x1]]) \to \mathrm{Can}([[x1]],t))",
                  r"\mathrm{Os}([[x1]]) \leftrightarrow \forall [[p1]]\,([[p1]] \to K_{[[x1]]}[[p1]])",
                  r"K_{[[x1]]}[[p1]] \to [[p1]]",
                  r"K_{[[x1]]}[[p1]] \to K_{[[x1]]}K_{[[x1]]}[[p1]]",
                  r"\neg K_{[[x1]]}[[p1]] \to K_{[[x1]]}\neg K_{[[x1]]}[[p1]]",
                  r"\mathrm{MP}([[x1]]) \to \neg\pos\,\mathrm{Wrong}([[x1]],a)",
                  r"\mathrm{Can}([[x1]],t) \to \pos\,\mathrm{Does}([[x1]],t)",
                  r"\nec(\mathrm{Op}([[x1]]) \wedge \mathrm{Os}([[x1]]) \wedge \mathrm{MP}([[x1]]))",
                  r"\mathrm{Os}([[x1]]) \wedge \mathrm{Os}([[x2]]) \to \forall [[p1]]\,(K_{[[x1]]}[[p1]] \leftrightarrow K_{[[x2]]}[[p1]])",
                  r"\neg Q(t,[[x1]]) \wedge \mathrm{Task}(t) \to \mathrm{Can}([[x1]],t)",
                  r"\mathrm{NE}([[x1]]) \to \neg\exists [[x2]]\,D([[x1]],[[x2]])"],
        swaps=[(r"tasks whose description quantifies over the agent's own powers",
                r"tasks whose description does not quantify over the agent's own powers"),
               (r"knows every false proposition", r"knows no false proposition"),
               (r"can do wrong but never does", r"cannot do wrong"),
               (r"omniscience entails omnipotence", r"omnipotence entails omniscience"),
               (r"the paradox of the stone shows a limitation", r"the paradox of the stone shows no limitation")],
        inserts=[(r"every task", r"whose description does not quantify over the agent's own powers"),
                 (r"every true proposition", r"(plurally quantified)")],
        index_terms=["omnipotence", "omniscience", "moral perfection", "paradox of the stone",
                     "Cantorian argument", "aseity", "compossibility"]),
    "EXIST": dict(
        terms=["existence", "predicate", "actualism", "necessitism", "domain", "constant",
               "contingent", "quantifier", "Barcan", "rigidity", "reference", "denotation"],
        formulas=[r"\forall [[x1]]\,\nec [[f1]][[x1]] \to \nec\forall [[x1]]\,[[f1]][[x1]]",
                  r"\nec\forall [[x1]]\,[[f1]][[x1]] \to \forall [[x1]]\,\nec [[f1]][[x1]]",
                  r"[[w1]]R[[w2]] \to D_{[[w1]]} \subseteq D_{[[w2]]}",
                  r"[[w1]]R[[w2]] \to D_{[[w2]]} \subseteq D_{[[w1]]}",
                  r"\nec\forall [[x1]]\,\nec\exists [[x2]]\,([[x2]] = [[x1]])",
                  r"E([[x1]],[[w1]]) \leftrightarrow [[x1]] \in D_{[[w1]]}",
                  r"\exists [[x1]]\,\pos [[f1]][[x1]] \to \pos\exists [[x1]]\,[[f1]][[x1]]",
                  r"\pos\exists [[x1]]\,[[f1]][[x1]] \to \exists [[x1]]\,\pos [[f1]][[x1]]",
                  r"\nec(\exists [[x1]]\,\mathrm{MG}([[x1]]) \to E(g))"],
        swaps=[(r"increasing domains validate the Barcan formula", r"increasing domains validate the converse Barcan formula"),
               (r"a variable domain validates necessitism", r"a constant domain validates necessitism"),
               (r"the converse Barcan formula", r"the Barcan formula"),
               (r"de dicto", r"de re"), (r"actualism", r"necessitism")],
        inserts=[(r"domain", r"of the world $[[w1]]$"), (r"exists", r"at $[[w1]]$")],
        index_terms=["Barcan formula", "converse Barcan formula", "necessitism", "actualism",
                     "existence predicate", "variable domains"]),
    "EVIL": dict(
        terms=["suffering", "gratuitous", "evidential", "noseeum", "inscrutable", "theodicy",
               "defence", "hiddenness", "nonresistant", "signalling", "equilibrium", "revelation",
               "freedom", "response", "sceptical"],
        formulas=[r"P(E \mid T) < P(E \mid \neg T)",
                  r"P(T \mid E) = P(E \mid T)\,P(T)/P(E)",
                  r"P(N \mid \neg S) \approx P(N)",
                  r"P(\neg S \mid \neg N) \approx 1",
                  r"\pos(T \wedge E)",
                  r"T \to \neg\exists e\,\mathrm{Grat}(e)",
                  r"u_G(h, r) \geq u_G(v, r)",
                  r"\sigma^{*}(h) = 1",
                  r"u_C(\mathrm{free}) > u_C(\mathrm{assured})",
                  r"\exists [[w1]]\,(T([[w1]]) \wedge E([[w1]]))"],
        swaps=[(r"the logical problem of evil succeeds", r"the logical problem of evil fails"),
               (r"evidence of a gratuitous evil", r"evidence of the absence of a justifying good"),
               (r"unambiguous revelation would enlarge the freedom of response",
                r"unambiguous revelation would constrain the freedom of response"),
               (r"a separating equilibrium", r"a pooling equilibrium"),
               (r"the noseeum inference is warranted", r"the noseeum inference is unwarranted")],
        inserts=[(r"intense suffering", r"that it could prevent"), (r"equilibrium", r"of the signalling game")],
        index_terms=["problem of evil", "noseeum inference", "sceptical theism", "divine hiddenness",
                     "signalling game", "free-will defence"]),
    "SCI": dict(
        terms=["naturalism", "cosmology", "multiverse", "fine-tuning", "normalizable",
               "evolutionary", "debunking", "cognitive", "likelihood", "selection", "physics"],
        formulas=[r"P(E \mid T)/P(E \mid \neg T) < 1",
                  r"P(T \mid E) < P(T)",
                  r"P(B \mid T) = P(B \mid \neg T)",
                  r"\int_{0}^{\infty} \rho(c)\, dc = 1",
                  r"P(T \mid B) = P(T)"],
        swaps=[(r"a normalizable measure over the constants", r"no normalizable measure over the constants"),
               (r"debunks the possibility premise", r"does not bear on the possibility premise"),
               (r"a posteriori premise", r"a priori premise")],
        inserts=[(r"measure", r"over the space of physical constants")],
        index_terms=["fine-tuning", "multiverse", "evolutionary debunking", "naturalism",
                     "cognitive science of religion"]),
    "IDENT": dict(
        terms=["identity", "indiscernible", "indiscernibility", "simplicity", "uniqueness",
               "haecceity", "composition", "distinctness", "godlike", "intrinsic"],
        formulas=[r"\forall [[f1]]\,([[f1]][[x1]] \leftrightarrow [[f1]][[x2]]) \to [[x1]] = [[x2]]",
                  r"\mathrm{MG}([[x1]]) \wedge \mathrm{MG}([[x2]]) \to [[x1]] = [[x2]]",
                  r"\nec\forall [[f1]]\,(\mathrm{GM}([[f1]]) \to ([[f1]][[x1]] \leftrightarrow [[f1]][[x2]]))",
                  r"\exists [[x1]]\,\forall [[x2]]\,(\mathrm{MG}([[x2]]) \leftrightarrow [[x2]] = [[x1]])",
                  r"[[x1]] = [[x2]] \to \nec([[x1]] = [[x2]])",
                  r"[[x1]] \neq [[x2]] \to \nec([[x1]] \neq [[x2]])",
                  r"\mathrm{Op}([[x1]]) \wedge \mathrm{Op}([[x2]]) \wedge [[x1]] \neq [[x2]] \to \bot"],
        swaps=[(r"weakly discernible", r"strongly discernible"),
               (r"the necessity of distinctness", r"the necessity of identity"),
               (r"an omnipotent being could cooperate with any other", r"an omnipotent being could thwart any other")],
        inserts=[(r"indiscernible", r"at every accessible world")],
        index_terms=["divine simplicity", "identity of indiscernibles", "uniqueness",
                     "necessity of identity"]),
    "AGENCY": dict(
        terms=["agency", "creation", "conservation", "causal", "intention", "providence",
               "foreknowledge", "counterfactual", "timeless", "freedom", "undetermined"],
        formulas=[r"\mathcal{M}_1 \models \mathrm{Causes}(g,e) \wedge \mathcal{M}_2 \models \neg\mathrm{Causes}(g,e)",
                  r"\mathrm{Causes}(g,e) \to \mathrm{Wills}(g,e)",
                  r"\pos\,\mathrm{Creates}(g,[[w1]]) \wedge \pos\,\neg\mathrm{Creates}(g,[[w1]])",
                  r"V([[w1]]) < V([[w2]]) \to \neg\mathrm{Chooses}(g,[[w1]])",
                  r"\forall [[w1]]\,\exists [[w2]]\,V([[w2]]) > V([[w1]])",
                  r"K_g [[p1]] \to [[p1]]",
                  r"(C \mathrel{\Box\!\!\to} K_g [[p1]]) \wedge \neg(K_g [[p1]] \mathrel{\Box\!\!\to} C)"],
        swaps=[(r"the main result fixes the causal role", r"the main result leaves the causal role undetermined"),
               (r"choices depend counterfactually on foreknowledge", r"foreknowledge depends counterfactually on free choices"),
               (r"in time", r"timeless")],
        inserts=[(r"causal role", r"of the maximally great being")],
        index_terms=["divine agency", "creation", "conservation", "foreknowledge",
                     "best possible world", "providence"]),
    "DEP": dict(
        terms=["dependence", "well-founded", "contingent", "dependee", "grounding", "ancestral"],
        formulas=[r"D([[x1]],[[x2]]) \wedge D([[x2]],[[x3]]) \to D([[x1]],[[x3]])",
                  r"\neg D([[x1]],[[x1]])",
                  r"\forall [[x1]]\,(\neg\mathrm{NE}([[x1]]) \to \exists [[x2]]\,D([[x1]],[[x2]]))",
                  r"\mathrm{NE}([[x1]]) \wedge \neg\exists [[x2]]\,D([[x1]],[[x2]]) \to \mathrm{ME}([[x1]])"],
        swaps=[(r"a contingent dependee", r"a necessary dependee")],
        inserts=[(r"dependee", r"in every accessible world")],
        index_terms=["dependence", "well-foundedness", "Identification premise"]),
    "HOL": dict(
        terms=["abstraction", "comprehension", "extensional", "intensional", "higher-order",
               "type", "Henkin", "general model"],
        formulas=[r"(\lambda [[x1]].\,[[f1]][[x1]] \wedge [[f2]][[x1]])(a) \leftrightarrow [[f1]]a \wedge [[f2]]a",
                  r"\exists [[f1]]\,\nec\forall [[x1]]\,([[f1]][[x1]] \leftrightarrow [[f2]][[x1]])",
                  r"[[f1]] \sqcap [[f2]] = \lambda [[x1]].\,[[f1]][[x1]] \wedge [[f2]][[x1]]",
                  r"\nec\forall [[x1]]\,([[f1]][[x1]] \to [[f2]][[x1]]) \to ([[f1]] \sqcap [[f2]] = [[f1]])"],
        swaps=[(r"standard models", r"general (Henkin) models"), (r"extensional", r"intensional")],
        inserts=[(r"comprehension", r"for intensional properties")],
        index_terms=["property abstraction", "general models", "comprehension"]),
    "LEAN": dict(
        terms=["module", "declaration", "axiom", "namespace", "theorem", "tactic"],
        formulas=[], swaps=[], inserts=[],
        index_terms=["Lean modules", "print axioms"]),
}

# Lean identifiers (Volume X, Chapter 8); used as typo material
GROUPS["LEAN"]["terms"] += ["necessary_existence", "converse_argument",
                            "maximal_greatness_rigid", "possibility_premise"]

# ---------------------------------------------------------------------------
# skeleton
# ---------------------------------------------------------------------------

CI = ["Plantinga1974b", "Malcolm1960", "Oppy1995", "Hartshorne1962"]

VOLS = [
    (3, "The Possibility Premise", 791, 1401, [
        ("Introduction: the problem of the two premises", 795, ["INTRO", "MG"], CI + ["vanInwagen1977"], "The two premises"),
        ("Conceivability and possibility", 811, ["EPIST"], ["Descartes", "Kripke1980", "Williamson2013"], "Conceivability and possibility"),
        ("The epistemology of modal premises", 858, ["EPIST", "MODAL"], ["Williamson2013", "vanInwagen1977", "Swinburne2004"], "Epistemology of modal premises"),
        ("Positive and negative conceivability", 902, ["EPIST"], ["Descartes", "Leibniz", "Oppy1995"], "Positive and negative conceivability"),
        ("From coherence to possibility", 951, ["FILTER", "MG"], ["Leibniz", "Godel1995", "Anderson1990", "Sobel1987", "Oppy1995"], "From coherence to possibility"),
        ("The converse premise and the evidence of absence", 1014, ["EPIST", "MG"], ["Plantinga1974b", "vanInwagen1977", "Oppy2006", "Rowe1975"], "The converse premise"),
        ("Symmetry-breaking: the asymmetry of support", 1078, ["EPIST", "MG"], ["vanInwagen1977", "Oppy2006", "Sobel2004", "Plantinga1974b"], "The asymmetry of support"),
        ("Parodies: islands, devils and the maximally evil being", 1139, ["EPIST", "MG"], ["Gaunilo", "Anselm", "Oppy1995", "Plantinga1974a"], "Parodies"),
        ("The ancestral premise and weaker modal logics", 1196, ["MODAL", "MG"], ["Salmon1989", "Chandler1976", "HughesCresswell1996", "Williamson2013"], "The ancestral premise"),
        ("Leibniz's problem and the compossibility of perfections", 1251, ["FILTER", "ATTR"], ["Leibniz", "Godel1995", "Morris1987", "Hartshorne1962"], "Leibniz's problem"),
        ("Probabilistic assessments of the possibility premise", 1302, ["EPIST"], ["Swinburne2004", "Sobel2004", "Oppy2006"], "Probabilistic assessments"),
        ("Conclusion of Volume III", 1371, ["INTRO", "EPIST"], ["Plantinga1974b", "vanInwagen1977"], "Conclusion of Volume III"),
    ]),
    (4, "The Divine Attributes", 1402, 1757, [
        ("Introduction", 1405, ["INTRO"], ["Morris1987", "Wierenga1989"], "Introduction"),
        ("Maximal excellence and its components", 1412, ["MG", "ATTR"], ["Plantinga1974b", "Morris1987", "Hoffman2002", "Anselm"], "Maximal excellence"),
        ("Omnipotence", 1447, ["ATTR"], ["Aquinas", "Mavrodes1963", "Savage1967", "Frankfurt1964", "Wierenga1989", "Hoffman2002"], "Omnipotence"),
        ("Omniscience", 1496, ["ATTR"], ["Grim1983", "Grim1991", "Kretzmann1966", "Wierenga1989", "Swinburne1993"], "Omniscience"),
        ("Moral perfection", 1541, ["ATTR"], ["Pike1969", "Morris1987", "Swinburne1993", "Adams1972"], "Moral perfection"),
        ("The compossibility of the attributes", 1583, ["ATTR", "FILTER"], ["Pike1969", "Hoffman2002", "Morris1987", "Leibniz"], "Compossibility of the attributes"),
        ("Necessary existence and aseity", 1631, ["ATTR", "EXIST"], ["Leftow2012", "Pruss2006", "Plantinga1980", "Fine1994"], "Necessary existence and aseity"),
        ("Godlikeness and maximal greatness", 1672, ["FILTER", "MG"], ["Godel1995", "Anderson1990", "Hajek2002", "Sobel2004", "Fitting2002"], "Godlikeness and maximal greatness"),
        ("The coherence of maximal excellence: summary", 1729, ["INTRO", "ATTR"], ["Morris1987", "Swinburne1993"], "Coherence of maximal excellence"),
    ]),
    (5, "Objections from Logic and Semantics", 1758, 2204, [
        ("Introduction", 1761, ["INTRO"], ["Oppy1995", "Sobel2004"], "Introduction"),
        ("Existence as a predicate", 1770, ["EXIST"], ["Kant", "Descartes", "Malcolm1960", "Oppy1995"], "Existence as a predicate"),
        ("The question-begging objection", 1812, ["MG", "EPIST"], ["Rowe1975", "Oppy1995", "Plantinga1974b", "Sobel2004", "vanInwagen1977"], "The question-begging objection"),
        ("Definitions and existential import", 1875, ["EXIST", "MG"], ["Anselm", "Gaunilo", "Lewis1970", "Oppy1995"], "Definitions and existential import"),
        ("Actualism, necessitism and the Barcan formula", 1913, ["EXIST", "MODAL"], ["Barcan1946", "Williamson2013", "HughesCresswell1996", "Fitting1998"], "The Barcan formula"),
        ("The S5 objection revisited", 1968, ["MODAL"], ["Salmon1989", "Chandler1976", "Kripke1963a", "Kripke1963b", "Williamson2013"], "The S5 objection revisited"),
        ("Modal collapse", 2029, ["FILTER", "MODAL"], ["Sobel1987", "Anderson1990", "Hajek2002", "Fitting2002", "Godel1995"], "Modal collapse"),
        ("Semantic objections: rigidity and reference to God", 2081, ["EXIST"], ["Kripke1980", "Lewis1970", "Alston1989"], "Semantic objections"),
        ("Paraconsistent and intuitionistic variants", 2127, ["MODAL"], ["Blackburn2001", "Chellas1980", "HughesCresswell1996"], "Paraconsistent variants"),
        ("Summary", 2189, ["INTRO"], ["Oppy1995", "Sobel2004"], "Summary"),
    ]),
    (6, "Objections from Evil and Hiddenness", 2205, 2602, [
        ("Introduction", 2208, ["INTRO"], ["Mackie1955", "Rowe1979"], "Introduction"),
        ("The logical problem of evil", 2215, ["EVIL", "MODAL"], ["Mackie1955", "Plantinga1974a", "Hume", "Pike1969"], "The logical problem of evil"),
        ("The structure of logical space and the free-will defence", 2259, ["EVIL", "MODAL"], ["Plantinga1974a", "Plantinga1974b", "vanInwagen2006", "Hick1966"], "Logical space and the free-will defence"),
        ("The evidential problem of evil", 2312, ["EVIL"], ["Rowe1979", "Draper1989", "Hume", "vanInwagen2006"], "The evidential problem of evil"),
        ("The noseeum inference", 2361, ["EVIL"], ["Wykstra1984", "Bergmann2001", "Rowe1979"], "The noseeum inference"),
        ("Divine hiddenness", 2414, ["EVIL"], ["Schellenberg1993", "Hick1966"], "Divine hiddenness"),
        ("Hiddenness as a signalling equilibrium", 2459, ["EVIL"], ["Schellenberg1993", "Swinburne2004"], "Hiddenness as a signalling equilibrium"),
        ("Evil, the possibility premise and the converse", 2511, ["EVIL", "MG"], ["Rowe1979", "Plantinga1974b", "Oppy2006"], "Evil and the converse premise"),
        ("Summary", 2581, ["INTRO"], ["Mackie1982", "vanInwagen2006"], "Summary"),
    ]),
    (7, "Objections from the Sciences", 2603, 2914, [
        ("Introduction", 2606, ["INTRO"], ["Mackie1982", "Plantinga2011"], "Introduction"),
        ("Naturalism and the modal argument", 2613, ["SCI", "MG"], ["Plantinga2011", "Mackie1982", "Oppy2006"], "Naturalism and the modal argument"),
        ("Cosmology and the beginning of the universe", 2651, ["SCI", "DEP"], ["Craig1979", "Koons1997", "Gale1999", "Rowe1975"], "Cosmology"),
        ("Fine-tuning and the multiverse", 2699, ["SCI"], ["Leslie1989", "Kraay2010", "Swinburne2004"], "Fine-tuning and the multiverse"),
        ("Evolutionary debunking of theistic belief", 2748, ["SCI", "EPIST"], ["Street2006", "Plantinga2011", "Barrett2004"], "Evolutionary debunking"),
        ("The cognitive science of religion", 2797, ["SCI"], ["Barrett2004", "Plantinga2011"], "The cognitive science of religion"),
        ("Probability, evidence and a priori premises", 2840, ["SCI", "EPIST"], ["Swinburne2004", "Sobel2004", "Oppy2006"], "Probability and a priori premises"),
        ("Summary", 2897, ["INTRO"], ["Plantinga2011"], "Summary"),
    ]),
    (8, "Uniqueness and Simplicity", 2915, 3203, [
        ("Introduction", 2918, ["INTRO"], ["Leftow2012", "Mann1982"], "Introduction"),
        ("The uniqueness of the maximally great being", 2924, ["IDENT", "ATTR"], ["Swinburne1993", "Hoffman2002", "Spinoza"], "Uniqueness"),
        ("Indiscernible godlike beings", 2967, ["IDENT", "FILTER"], ["Godel1995", "Anderson1990", "Fitting2002", "Leibniz"], "Indiscernible godlike beings"),
        ("Identity of indiscernibles in modal contexts", 3011, ["IDENT", "MODAL"], ["Kripke1980", "Williamson2013", "Fine1994"], "Identity of indiscernibles"),
        ("Divine simplicity: the doctrine", 3058, ["IDENT"], ["Aquinas", "Mann1982", "Plantinga1980", "Stump1981"], "Divine simplicity"),
        ("Simplicity and the attributes", 3102, ["IDENT", "ATTR"], ["Mann1982", "Plantinga1980", "Bergmann2001", "Kretzmann1966"], "Simplicity and the attributes"),
        ("The objection from modal collapse to simplicity", 3141, ["IDENT", "MODAL"], ["Plantinga1980", "Leftow2012", "Pruss2006"], "Modal collapse and simplicity"),
        ("Summary", 3189, ["INTRO"], ["Mann1982"], "Summary"),
    ]),
    (9, "Divine Agency", 3204, 3537, [
        ("Introduction", 3207, ["INTRO"], ["Swinburne2004", "Kenny1979"], "Introduction"),
        ("What the main result says about action", 3214, ["AGENCY", "MG"], ["Plantinga1974b", "Kenny1979"], "The main result and action"),
        ("Models agreeing on maximal greatness", 3251, ["AGENCY", "MODAL"], ["HughesCresswell1996", "Blackburn2001"], "Models agreeing on maximal greatness"),
        ("Creation and conservation", 3298, ["AGENCY", "DEP"], ["Aquinas", "Craig1979", "Leftow2012"], "Creation and conservation"),
        ("The freedom of the maximally great being", 3346, ["AGENCY"], ["Rowe2004", "Adams1972", "Kenny1979"], "Divine freedom"),
        ("Must a maximally great being create the best?", 3393, ["AGENCY"], ["Adams1972", "Rowe2004", "Leibniz", "Kraay2010"], "Creating the best"),
        ("Omniscience and foreknowledge", 3440, ["AGENCY", "ATTR"], ["Pike1965", "Hasker1989", "Zagzebski1991", "Stump1981"], "Omniscience and foreknowledge"),
        ("Particular providence and the limits of the result", 3488, ["AGENCY"], ["Swinburne2004", "Alston1989"], "Particular providence"),
        ("Summary", 3521, ["INTRO"], ["Kenny1979"], "Summary"),
    ]),
    (10, "Formal Appendices", 3538, 3939, [
        ("The modal language and its semantics", 3541, ["MODAL"], ["Kripke1963a", "Kripke1963b", "HughesCresswell1996", "Blackburn2001", "Chellas1980"], "The modal language", (1, 386)),
        ("Formal material for Volume I", 3582, ["MODAL", "MG"], ["Plantinga1974b", "Williamson2013"], "Formal material for Volume I", (387, 790)),
        ("Higher-order modal logic and property abstraction", 3628, ["HOL", "FILTER"], ["Gallin1975", "Henkin1950", "Fitting2002"], "Higher-order modal logic", (791, 1302)),
        ("Formal material for Volume II", 3683, ["DEP"], ["Rowe1975", "Pruss2006", "Koons1997"], "Formal material for Volume II", (1303, 1801)),
        ("Formal material for Volume III", 3729, ["FILTER", "MG"], ["Godel1995", "Anderson1990", "Sobel1987"], "Formal material for Volume III", (1802, 2650)),
        ("Formal material for Volumes IV and V", 3833, ["ATTR", "EXIST"], ["Barcan1946", "Fitting1998", "Grim1991"], "Formal material for Volumes IV and V", (2651, 3044)),
        ("Formal material for Volumes VI to IX", 3875, ["EVIL", "IDENT", "AGENCY"], ["Rowe1979", "Kripke1980"], "Formal material for Volumes VI to IX", (3045, 3297)),
        ("The Lean modules", 3913, ["LEAN", "MODAL"], ["Benzmuller2014", "Oppenheimer2011"], "The Lean modules", (3298, 3361)),
    ]),
    (11, "Bibliography and Indices", 3940, 4180, [
        ("Bibliography", 3943, [], [], "Bibliography", "bib"),
        ("Index of names", 4063, [], [], "Index of names", "names"),
        ("Index of subjects", 4102, [], [], "Index of subjects", "subjects"),
        ("Index of numbered results", 4158, [], [], "Index of numbered results", "results"),
    ]),
]

# Volume I (REL-01-a): chapter ranges and works cited, for the name index
VOL1_CHAPTERS = [(3, 18, ["Anselm", "Descartes", "Kant", "Malcolm1960", "Hartshorne1962", "Plantinga1974b",
                          "Godel1995", "Sobel1987", "Anderson1990", "Oppy1995", "Oppenheimer2011", "Benzmuller2014"]),
                 (19, 40, ["Williamson2013", "Salmon1989", "Plantinga1974b"]),
                 (41, 60, ["Plantinga1974b"]),
                 (61, 87, ["Plantinga1974b"]),
                 (127, 170, ["Williamson2013", "Barcan1946"]),
                 (171, 235, ["Williamson2013", "Salmon1989", "Chandler1976"]),
                 (236, 348, ["Godel1995", "Sobel1987", "Anderson1990", "Hajek2002", "Fitting2002"])]

# Items fixed by the substantive corrigenda (volume, chapter): {number: (kind, page)}
ITEM_OVERRIDES = {
    (3, 5): {6: ("Theorem", 983)},
    (3, 6): {3: ("Proposition", 1029)},
    (4, 3): {2: ("Definition", 1452), 9: ("Theorem", 1478)},
    (4, 4): {1: ("Definition", 1499), 6: ("Theorem", 1517)},
    (4, 6): {4: ("Lemma", 1601)},
    (4, 8): {5: ("Proposition", 1694), 7: ("Theorem", 1703)},
    (5, 3): {4: ("Proposition", 1838)},
    (5, 5): {3: ("Lemma", 1926), 4: ("Lemma", 1930), 5: ("Theorem", 1934)},
    (6, 7): {5: ("Lemma", 2483), 7: ("Theorem", 2490)},
    (8, 3): {6: ("Lemma", 2989), 8: ("Theorem", 2996)},
    (9, 3): {5: ("Theorem", 3279)},
}
DISPLAY_OVERRIDES = {(6, 4): {2: 2318}, (7, 5): {6: 2771}}

# Pages on which the substantive corrigenda fall: no generated entry there.
RESERVED = [967, 983, 1029, 1452, 1478, 1499, 1517, 1589, 1601, 1694, 1703, 1838, 1841,
            1783, 1926, 1934, 2318, 2483, 2490, 2771, 2989, 2996, 3066, 3279, 3280,
            3563, 3803, 3804]

# Pointer rows placed in the generated lists: (vol, ch, page, pos, loc, text)
POINTERS = [
    (3, 5, 967, 4, r"l.~4", r"\textit{see} Corrigendum~S1"),
    (3, 5, 983, 1, r"proof of Theorem~5.6", r"\textit{see} Corrigendum~S1"),
    (3, 6, 1029, 1, r"proof of Proposition~6.3", r"\textit{see} Corrigendum~S3"),
    (4, 3, 1452, 1, r"Definition~3.2", r"\textit{see} Corrigendum~S4"),
    (4, 4, 1499, 1, r"Definition~4.1", r"\textit{see} Corrigendum~S5"),
    (4, 6, 1589, 12, r"l.~12", r"\textit{see} Corrigendum~S7"),
    (4, 8, 1694, 1, r"Proposition~8.5", r"\textit{see} Corrigendum~S6"),
    (5, 2, 1783, 20, r"l.~20", r"\textit{see} Corrigendum~S9"),
    (5, 3, 1838, 1, r"Proposition~3.4", r"\textit{see} Corrigendum~S8"),
    (5, 5, 1926, 1, r"Lemma~5.3", r"\textit{see} Corrigendum~S10"),
    (6, 4, 2318, 10, r"display (4.2)", r"\textit{see} Corrigendum~S11"),
    (6, 7, 2483, 1, r"Lemma~7.5", r"\textit{see} Corrigendum~S12"),
    (7, 5, 2771, 10, r"display (5.6)", r"\textit{see} Corrigendum~S13"),
    (8, 3, 2989, 1, r"Lemma~3.6", r"\textit{see} Corrigendum~S14"),
    (8, 5, 3066, 25, r"l.~25", r"\textit{see} Corrigendum~S15"),
    (9, 3, 3280, 1, r"proof of Theorem~3.5", r"\textit{see} Corrigendum~S16"),
    (10, 1, 3563, 1, r"Lemma~214", r"\textit{see} Corrigendum~S17"),
    (10, 5, 3803, 1, r"Lemma~2417 and following paragraph", r"\textit{see} Corrigendum~S2"),
    (11, 1, 3976, 0, r"Gödel, K. (1995)", r"\textit{see} Corrigendum~S18"),
]

TOPICS = [
    ("the coherence of maximal excellence", 4, 9), ("the compossibility of the attributes", 4, 6),
    ("omnipotence", 4, 3), ("omniscience", 4, 4), ("moral perfection", 4, 5),
    ("necessary existence and aseity", 4, 7), ("godlikeness and maximal greatness", 4, 8),
    ("the question-begging objection", 5, 3), ("existence as a predicate", 5, 2),
    ("the Barcan formula", 5, 5), ("modal collapse", 5, 7), ("the logical problem of evil", 6, 2),
    ("the evidential problem of evil", 6, 4), ("the noseeum inference", 6, 5),
    ("divine hiddenness", 6, 6), ("fine-tuning", 7, 4), ("evolutionary debunking", 7, 5),
    ("indiscernible godlike beings", 8, 3), ("divine simplicity", 8, 5), ("uniqueness", 8, 2),
    ("the causal role of the maximally great being", 9, 3), ("creation and conservation", 9, 4),
    ("whether a maximally great being must create the best", 9, 6), ("foreknowledge", 9, 7),
    ("the formal material for Volume III, including Lemma~2417", 10, 5),
    ("the transfer from coherence to possibility", 3, 5), ("the converse premise", 3, 6),
    ("parodies of the argument", 3, 8), ("the ancestral premise", 3, 9),
    ("conceivability and possibility", 3, 2), ("the choice of S5", 1, 7),
    ("maximal greatness and the Barcan formula", 1, 6), ("the comparison with Gödel's argument", 1, 8),
    ("what the formalization establishes", 1, 4), ("the Lean modules", 10, 8),
]
CHAPTER_COUNTS = {1: 9, 3: 12, 4: 9, 5: 10, 6: 9, 7: 8, 8: 8, 9: 9, 10: 8, 11: 4}

# Volume I numbered items (REL-01-a), as a pseudo-chapter for references
VOL1_ITEMS = [("Assumption", "2.1"), ("Definition", "2.2"), ("Definition", "2.3"),
              ("Definition", "2.4"), ("Assumption", "3.1"), ("Lemma", "3.2"), ("Lemma", "3.3"),
              ("Theorem", "3.4"), ("Corollary", "3.5"), ("Proposition", "4.1")]

# entries per page of each volume, and the mix of error types
DENSITY = {3: 1.75, 4: 1.75, 5: 1.75, 6: 1.68, 7: 1.62, 8: 1.75, 9: 1.7, 10: 2.45}
DENSITY_BACK = {"bib": 1.0, "names": 6.0, "subjects": 5.0, "results": 6.0}

MIX_FORMAL = [("formula", 32), ("typo", 26), ("xref", 14), ("xref_out", 6), ("pageref", 4),
              ("cite", 5), ("swap", 6), ("insert", 5), ("topic", 2)]
MIX_DISC = [("formula", 12), ("typo", 38), ("xref", 10), ("xref_out", 5), ("pageref", 4),
            ("cite", 13), ("swap", 8), ("insert", 7), ("topic", 3)]
MIX_INTRO = [("typo", 50), ("topic", 14), ("xref_out", 6), ("cite", 14), ("pageref", 4),
             ("swap", 6), ("insert", 6)]
FORMAL_GROUPS = {"MODAL", "MG", "FILTER", "EXIST", "HOL", "DEP", "LEAN"}


def build():
    rng = __import__("random").Random(SEED)
    volumes = []
    for vnum, vtitle, vs, ve, chs in VOLS:
        chapters = []
        for k, spec in enumerate(chs, 1):
            title, start, groups, cites, short = spec[:5]
            extra = spec[5] if len(spec) > 5 else None
            end = (chs[k][1] - 1) if k < len(chs) else ve
            special = extra if isinstance(extra, str) else None
            c = Chapter(vnum, k, title, start, end, groups, cites, special)
            c.short = short
            if vnum == 10:
                build_lemma_items(c, *extra)
                build_displays(c, rng, 0.5, {})
            elif not special:
                dens = 0.12 if groups and groups[0] == "INTRO" else 0.33
                build_items(c, rng, dens, ITEM_OVERRIDES.get((vnum, k), {}))
                ddens = 0.6 if FORMAL_GROUPS & set(groups) else 0.25
                build_displays(c, rng, ddens, DISPLAY_OVERRIDES.get((vnum, k), {}))
            chapters.append(c)
        volumes.append(Volume(vnum, vtitle, vs, ve, chapters))
    vol1 = Chapter(1, 0, "Volume I", 1, 388, [], [])
    vol1.items = [Item(k, n, None, 1, int(n.split(".")[0]), i)
                  for i, (k, n) in enumerate(VOL1_ITEMS, 1)]
    vmap = {v.num: v for v in volumes}

    def ch(v, c):
        return vmap[v].chapters[c - 1]

    def ext_refs(vol, chap):
        v = vol.num
        if v == 10:
            m = {2: [vol1], 5: [ch(3, 5), ch(3, 7)], 6: [ch(4, 3), ch(4, 4), ch(4, 6), ch(5, 3), ch(5, 5)],
                 7: [ch(6, 4), ch(6, 7), ch(8, 3), ch(9, 3)]}
            return m.get(chap.num, [vol1])
        out = [vol1]
        xch = {3: 5, 4: 6, 5: 6, 6: 7, 7: 7, 8: 7, 9: 7}.get(v)
        if xch:
            out.append(ch(10, xch))
        if v > 3:
            out.append(ch(3, 5))
        if v > 4:
            out += [ch(4, 2), ch(4, 6)]
        return out

    book = Book(volumes, False, GROUPS, BIB, TOPICS, CHAPTER_COUNTS, PUBLISHER_CONFUSIONS,
                ext_refs, RESERVED, extra_name_ranges=VOL1_CHAPTERS)
    book.protected = {"2417", "2471"}
    return book, vmap


def contents_entry(gen, vol):
    """One misprinted page number in the volume's table of contents."""
    rng = gen.rng
    chs = [c for c in vol.chapters if c.num > 1]
    c = rng.choice(chs)
    wrong = __import__("errata_engine").transpose_digits(c.start, rng, vol.start, vol.end)
    from errata_engine import Entry, forread
    return Entry(vol.start + 1, 5 + c.num, "Contents, Chapter~{}".format(c.num),
                 forread(gen.P(wrong), gen.P(c.start)), "", False, "xref"), c


def main():
    book, vmap = build()
    gen = Generator(book, SEED)
    stats = {}
    total = 0
    for vol in book.volumes:
        parts = []
        nvol = 0
        ce, cch = contents_entry(gen, vol)
        for c in vol.chapters:
            if c.special:
                n = int(round(c.pages * DENSITY_BACK[c.special]))
                es = gen.chapter_entries(vol, c, n, [(c.special if c.special != "bib" else "bib", 1)])
            else:
                g = set(c.groups)
                if c.groups and c.groups[0] == "INTRO":
                    mix = MIX_INTRO
                elif g & FORMAL_GROUPS and vol.num == 10 or len(g & FORMAL_GROUPS) >= 2:
                    mix = MIX_FORMAL
                else:
                    mix = MIX_DISC
                n = int(round(c.pages * DENSITY[vol.num]))
                es = gen.chapter_entries(vol, c, n, mix)
                rh = gen.running_head(vol, c) if gen.rng.random() < 0.15 else None
                if rh:
                    es.append(rh)
            if c.num == 1:
                parts.append(r"\subsection*{{Front matter \hfill \normalfont\small pp.~{}--{}}}".format(
                    vol.start, c.start - 1) + "\n\\begin{errlist}\n" + r"{} & {} & {} \\".format(
                    gen.P(ce.page), ce.loc, ce.body) + "\n\\end{errlist}\n")
                nvol += 1
            ptrs = [(p[2], p[3], p[4], p[5]) for p in POINTERS if p[0] == vol.num and p[1] == c.num]
            for e in es:
                assert c.start <= e.page <= c.end, (vol.num, c.num, e.page)
            tex, cnt = latex_chapter(c, es, gen.P, ptrs)
            parts.append(tex)
            nvol += cnt - len(ptrs)
        stats[vol.num] = nvol
        total += nvol
        with open(os.path.join(HERE, "vol{:02d}.tex".format(vol.num)), "w", encoding="utf-8") as f:
            f.write("% generated by generate.py -- do not edit\n")
            f.write("\n".join(parts))
    # skeleton table
    lines = [r"% generated by generate.py -- do not edit"]
    for vol in book.volumes:
        lines.append(r"\noindent\textbf{{Volume {}: {}}} \hfill pp.~{}--{}\par\nopagebreak".format(
            vol.roman, vol.title, vol.start, vol.end))
        lines.append(r"\begin{skeltab}")
        for c in vol.chapters:
            extra = ""
            if c.lemma_range:
                extra = r" \textit{{(Lemmas {}--{})}}".format(*c.lemma_range)
            num = "" if c.special else str(c.num)
            lines.append(r"{} & {}{} & {}--{} \\".format(num, c.title, extra, c.start, c.end))
        lines.append(r"\end{skeltab}")
        lines.append("")
    with open(os.path.join(HERE, "skeleton.tex"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
    # statistics
    labels = [("typo", "Typographical errors (spelling, running heads)"),
              ("wording", "Wrong word or phrase"),
              ("omission", "Omitted or repeated words"),
              ("formula", "Misprinted formulas and symbols"),
              ("xref", "Cross-references and page references"),
              ("citation", "Citations in the text"),
              ("bibliography", "Bibliography (Volume XI)"),
              ("index", "Indices (Volume XI)")]
    srows = [r"% generated by generate.py -- do not edit", r"\begin{tabular}{@{}lr@{}}", r"\toprule"]
    for k, lab in labels:
        srows.append(r"{} & {} \\".format(lab, gen.counts.get(k, 0)))
    srows.append(r"\midrule")
    srows.append(r"Total & {} \\".format(sum(gen.counts.values())))
    srows += [r"\bottomrule", r"\end{tabular}"]
    vrows = [r"\begin{tabular}{@{}lr@{}}", r"\toprule"]
    for v in sorted(stats):
        vrows.append(r"Volume {} & {} \\".format(ROMAN[v], stats[v]))
    vrows += [r"\bottomrule", r"\end{tabular}"]
    with open(os.path.join(HERE, "stats.tex"), "w", encoding="utf-8") as f:
        f.write("\n".join(srows) + "\n\\hspace{2em}\n" + "\n".join(vrows) + "\n")
    print("entries:", total, gen.counts, stats)
    # report the key computed pages
    x5 = vmap[10].chapters[4]
    print("Lemma 2417 page:", [it.page for it in x5.items if it.num == "2417"])
    print("Lemma 214 page:", [it.page for it in vmap[10].chapters[0].items if it.num == "214"])
    print("Godel bib page:", book.bib_page("Godel1995", vmap[11].chapters[0]))


if __name__ == "__main__":
    main()
