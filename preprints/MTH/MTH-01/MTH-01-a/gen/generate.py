#!/usr/bin/env python3
"""Generator for the computed part of MTH-01-a, "On the Existence of Numbers".

Standard library only; deterministic. Writes tab_a.tex, tab_b.tex, tab_c.tex, tab_d.tex and
summary.tex in this directory; ../main.tex includes them. Every claim the manuscript makes about
the tables is checked by an assert in summary(); the script halts if one fails.

Part 1. Structure register and dependency graph for the MTH-01-a inventory.

Each structure: code -> (display, name, carrier cardinality, direct presuppositions, gloss).
Cardinalities: 'fin' < 'a0' (aleph_0) < 'c' (2^aleph_0) < '2c' (2^(2^aleph_0)).
The 'carrier' is the domain a law quantifies over when it quantifies over the structure
(for structure kinds, the domain of one standard instance, e.g. R^n, L^2(R^n)).

Part 2. Hand-curated table of laws for the MTH-01-a inventory.

Each entry: L(key, theory, name, equation, variables, structures, ref, **options)
  equation   LaTeX (math mode) in standard form
  variables  regimented quantifier prefix: the sorts of the variables the law binds
  structures direct mathematical structures quantified over (codes of structures.py)
  ref        textbook or source code (see REFS)
  nom        override of the nominalization status computed by the rule
  var        True if the law quantifies over varied (non-actual) histories
  red        True if C enters only as R^2 with a complex structure (classical use)
  par        keys of laws from which the law is standardly derived
  note       remark printed with the entry
"""
import os

# ====================================================================== part 1: structures

CARD_ORDER = {"none": -1, "fin": 0, "a0": 1, "c": 2, "2c": 3}
CARD_TEX = {"none": "--", "fin": "fin", "a0": r"$\aleph_0$", "c": r"$\mathfrak c$",
            "2c": r"$2^{\mathfrak c}$"}

NUMBERS = ["N", "Z", "Q", "R", "C", "H"]

S = {}


def st(code, disp, name, card, deps, gloss):
    assert code not in S, code
    S[code] = dict(code=code, disp=disp, name=name, card=card, deps=deps, gloss=gloss)


# number systems
st("N", r"$\mathbb N$", "natural numbers", "a0", [], "the progression 0, 1, 2, ... (Peano structure)")
st("Z", r"$\mathbb Z$", "integers", "a0", ["N"], "pairs of naturals modulo difference")
st("Q", r"$\mathbb Q$", "rational numbers", "a0", ["Z"], "pairs of integers modulo proportion")
st("Seq", r"\textsf{Seq}", "sequences", "c", ["N"], "functions on $\\mathbb N$ (Cauchy sequences, series)")
st("R", r"$\mathbb R$", "real numbers", "c", ["Q", "Seq"], "complete ordered field (Cauchy completion of $\\mathbb Q$)")
st("C", r"$\mathbb C$", "complex numbers", "c", ["R"], "$\\mathbb R^2$ with complex multiplication")
st("H", r"$\mathbb H$", "quaternions", "c", ["R"], "$\\mathbb R^4$ with Hamilton's product")
# finite and discrete
st("Fin", r"\textsf{Fin}", "finite sets and graphs", "fin", ["N"], "finite index sets, finite graphs and their counts")
st("Sn", r"\textsf{Sn}", "symmetric groups", "fin", ["Fin"], "permutations of a finite set (particle exchange)")
# linear and geometric
st("Rn", r"\textsf{Rn}", "coordinate spaces", "c", ["R", "N"], "$\\mathbb R^n$ as a set of $n$-tuples")
st("Vr", r"\textsf{Vr}", "real vector spaces", "c", ["R"], "finite-dimensional real vector spaces, inner products")
st("Vc", r"\textsf{Vc}", "complex vector spaces", "c", ["C"], "finite-dimensional complex vector spaces")
st("Lin", r"\textsf{Lin}", "linear maps", "c", ["Vr"], "matrices, determinants, eigenvalues of finite-dimensional maps")
st("E3", r"\textsf{E3}", "Euclidean space", "c", ["Rn", "Vr"], "affine Euclidean 3-space with its metric")
st("Gal", r"\textsf{Gal}", "Galilean spacetime", "c", ["E3"], "absolute time with Euclidean simultaneity slices")
st("Mink", r"\textsf{Mink}", "Minkowski spacetime", "c", ["Rn", "Vr"], "$\\mathbb R^4$ with the Minkowski metric")
st("Top", r"\textsf{Top}", "topology", "c", ["R"], "open sets, limits, continuity on $\\mathbb R^n$")
st("Ck", r"\textsf{Ck}", "differentiable functions", "c", ["Rn", "Top"], "$C^k$ maps between coordinate spaces; derivatives, Riemann integrals")
st("CA", r"\textsf{CA}", "complex analysis", "c", ["C", "Ck"], "holomorphic functions, contour integrals, residues")
st("Man", r"\textsf{Man}", "smooth manifolds", "c", ["Rn", "Top", "Ck"], "second-countable smooth manifolds")
st("TM", r"\textsf{TM}", "tangent bundles", "c", ["Man", "Vr"], "tangent and cotangent bundles")
st("Tens", r"\textsf{Tens}", "tensor fields", "c", ["TM", "Lin"], "tensor fields, differential forms, exterior derivative")
st("Lor", r"\textsf{Lor}", "Lorentzian manifolds", "c", ["Man", "Tens"], "metric, Levi-Civita connection, curvature")
st("StS", r"\textsf{StS}", "state spaces", "c", ["Man", "TM"], "spaces of possible states (configuration-velocity, thermodynamic, $\\mu$-space)")
st("Symp", r"\textsf{Symp}", "symplectic manifolds", "c", ["StS", "Tens"], "phase space with its symplectic form")
st("Lie", r"\textsf{Lie}", "Lie groups", "c", ["Man"], "finite-dimensional Lie groups")
st("LieA", r"\textsf{LieA}", "Lie algebras", "c", ["Vr", "Lin"], "Lie algebras and brackets (incl. Poisson algebras)")
st("SO3", r"\textsf{SO3}", "rotation groups", "c", ["Lie", "Lin"], "$SO(3)$, $O(3)$")
st("SUn", r"\textsf{SUn}", "unitary groups", "c", ["Lie", "Vc"], "$U(n)$, $SU(n)$")
st("Poin", r"\textsf{Poin}", "Lorentz and Poincar\\'e groups", "c", ["Lie", "Mink"], "$O(1,3)$ and $\\mathbb R^{1,3}\\rtimes O(1,3)$")
st("Bund", r"\textsf{Bund}", "principal bundles", "c", ["Man", "Lie", "LieA", "Tens"], "bundles with connection (gauge fields)")
st("Cliff", r"\textsf{Cliff}", "Clifford algebras", "c", ["Vc", "Lin", "Mink"], "Dirac matrices, spinor representations")
st("Grass", r"\textsf{Grass}", "Grassmann algebras", "c", ["Vc"], "anticommuting generators, Berezin integral")
# measure and probability
st("Bor", r"\textsf{Bor}", "Borel sets", "c", ["Top"], "Borel $\\sigma$-algebra of $\\mathbb R^n$")
st("PR", r"\textsf{PR}", "power set of the reals", "2c", ["R"], "arbitrary sets of reals")
st("Leb", r"\textsf{Leb}", "Lebesgue-measurable sets", "2c", ["Bor", "PR"], "Lebesgue $\\sigma$-algebra (all subsets of null sets)")
st("Meas", r"\textsf{Meas}", "measures", "c", ["Bor", "R"], "Borel measures and Lebesgue integration of Borel functions")
st("Prob", r"\textsf{Prob}", "probability measures", "c", ["Meas"], "probability distributions, expectations")
st("Stoch", r"\textsf{Stoch}", "stochastic processes", "c", ["Prob", "Ck", "Dist"], "Wiener process, white noise, ensemble averages")
st("Lmeas", r"\textsf{Lmeas}", "measurable functions", "2c", ["Leb", "R"], "Lebesgue-measurable functions (before quotient)")
# Hilbert space and operator theory
st("Hil", r"\textsf{Hil}", "Hilbert spaces", "c", ["Vc", "Seq", "Top"], "separable complex Hilbert spaces, tensor products")
st("L2", r"\textsf{L2}", "$L^2$ spaces", "c", ["Lmeas", "Hil", "C"], "square-integrable functions modulo null sets")
st("Op", r"\textsf{Op}", "operators", "c", ["Hil", "Bor", "Meas"], "self-adjoint and unitary operators, spectral measures")
st("Tr", r"\textsf{Tr}", "trace-class operators", "c", ["Op"], "density operators, partial trace")
st("Fock", r"\textsf{Fock}", "Fock spaces", "c", ["Hil", "Sn", "N"], "(anti)symmetrized tensor powers, ladder operators")
st("Dist", r"\textsf{Dist}", "distributions", "c", ["Ck", "Top", "Lin"], "tempered distributions, Dirac delta (complex-valued ones add $\\mathbb C$)")
st("OVD", r"\textsf{OVD}", "operator-valued distributions", "c", ["Dist", "Op"], "quantum fields smeared with test functions")
st("Four", r"\textsf{Four}", "Fourier analysis", "c", ["L2", "Dist"], "Fourier--Plancherel transform")

ORDER = list(S.keys())


def closure(codes):
    """Reflexive-transitive closure of a set of structure codes under 'presupposes'."""
    seen, stack = set(), list(codes)
    while stack:
        x = stack.pop()
        if x in seen:
            continue
        seen.add(x)
        stack.extend(S[x]["deps"])
    return seen


def check_acyclic():
    state = {}

    def visit(x, path):
        if state.get(x) == 1:
            raise AssertionError("cycle through " + " ".join(path + [x]))
        if state.get(x) == 2:
            return
        state[x] = 1
        for y in S[x]["deps"]:
            assert y in S, (x, y)
            visit(y, path + [x])
        state[x] = 2

    for x in S:
        visit(x, [])


def maxcard(codes):
    best = "none"
    for x in codes:
        if CARD_ORDER[S[x]["card"]] > CARD_ORDER[best]:
            best = S[x]["card"]
    return best


def sort_codes(codes):
    return sorted(codes, key=ORDER.index)

# ====================================================================== part 2: laws

THEORIES = [
    ("NM", "Newtonian mechanics", "GPS"),
    ("LM", "Lagrangian mechanics", "GPS"),
    ("HM", "Hamiltonian mechanics", "ARN"),
    ("CM", "Continuum mechanics of solids", "GUR"),
    ("FD", "Fluid dynamics and acoustics", "LLF"),
    ("TD", "Thermodynamics", "CAL"),
    ("SM", "Statistical mechanics", "HUA"),
    ("EM", "Electromagnetism", "JAC"),
    ("MH", "Plasma physics and magnetohydrodynamics", "CHEN"),
    ("OP", "Optics", "BW"),
    ("SR", "Special relativity", "JAC"),
    ("GR", "General relativity and cosmology", "WAL"),
    ("QM", "Non-relativistic quantum mechanics", "SAK"),
    ("AN", "Atomic and nuclear physics", "KRANE"),
    ("SS", "Condensed matter physics", "AM"),
    ("QF", "Quantum field theory and the Standard Model", "PS"),
]

REFS = {
    "GPS": "GoldsteinPooleSafko2002", "ARN": "Arnold1989", "GUR": "Gurtin1981",
    "LLF": "LandauLifshitz1987", "CAL": "Callen1985", "HUA": "Huang1987", "REI": "Reif1965",
    "JAC": "Jackson1999", "BW": "BornWolf1999", "WAL": "Wald1984", "MTW": "MisnerThorneWheeler1973",
    "SAK": "SakuraiNapolitano2011", "VN": "vonNeumann1932", "RS": "ReedSimon1980",
    "PS": "PeskinSchroeder1995", "WEI": "Weinberg1995", "SW": "StreaterWightman1964",
    "F80": "Field1980", "GLE": "Gleason1957", "KS": "KochenSpecker1967", "WZ": "WoottersZurek1982",
    "CHSH": "CHSH1969", "KRANE": "Krane1988", "AM": "AshcroftMermin1976", "CHEN": "Chen1984", "TSI": "Cirelson1980", "ROBB": "Robb1914",
}

LAWS = []
KEYS = {}


def L(key, th, name, eq, var_s, structs, ref, nom=None, var=False, red=False, par=(), note=""):
    assert key not in KEYS, key
    e = dict(key=key, th=th, name=name, eq=eq, vars=var_s, S=structs.split(), ref=ref,
             nom=nom, var=var, red=red, par=list(par), note=note)
    KEYS[key] = e
    LAWS.append(e)


# common variable sorts
t = r"t\in\mathbb R"
xp = r"\mathbf x:\mathbb R\to E^3\ (C^2)"
m = r"m\in\mathbb R_{>0}"
F3 = r"\mathbf F:\mathbb R\to\mathbb R^3"
sf = r"\phi:E^3\to\mathbb R"
vf = r"\mathbf v:E^3\times\mathbb R\to\mathbb R^3"
rho = r"\rho:E^3\times\mathbb R\to\mathbb R_{\ge 0}"
q = r"q:\mathbb R\to Q\ (Q\text{ a manifold})"
Lg = r"L:TQ\times\mathbb R\to\mathbb R"
H = r"H:T^*Q\times\mathbb R\to\mathbb R"
psi = r"\psi\in\mathcal H"
Aop = r"\hat A\text{ self-adjoint on }\mathcal H"
Hop = r"\hat H\text{ self-adjoint on }\mathcal H"
EB = r"\mathbf E,\mathbf B:E^3\times\mathbb R\to\mathbb R^3"
g = r"g\text{ Lorentzian metric on }M"
M4 = r"x\in M\ (\text{4-manifold})"
phiQ = r"\phi:\mathcal S(\mathbb R^4)\to\text{operators on }\mathcal F"

# ---------------------------------------------------------------- Newtonian mechanics
L("nm1", "NM", "First law (inertia)", r"\mathbf F_{\mathrm{net}}(t)=\mathbf 0\ \Rightarrow\ \ddot{\mathbf x}(t)=\mathbf 0",
  [t, xp, F3], "R E3 Gal Ck", "GPS", nom="S",
  note="Force-free worldlines are the straight lines of Galilean spacetime; Field's synthetic spacetime states this without numbers.")
L("nm2", "NM", "Second law", r"m\,\ddot{\mathbf x}(t)=\mathbf F(t)", [t, xp, m, F3], "R E3 Gal Vr Ck", "GPS")
L("nm3", "NM", "Third law", r"\mathbf F_{12}(t)=-\mathbf F_{21}(t)", [t, r"\mathbf F_{ij}:\mathbb R\to\mathbb R^3"], "R Vr", "GPS")
L("nm4", "NM", "Universal gravitation", r"\mathbf F_{12}=-G\,m_1m_2\,\frac{\mathbf x_1-\mathbf x_2}{|\mathbf x_1-\mathbf x_2|^3}",
  [r"m_1,m_2\in\mathbb R_{>0}", r"\mathbf x_1\neq\mathbf x_2\in E^3", r"G\in\mathbb R_{>0}"], "R E3 Vr", "GPS", nom="F",
  note="Equivalent, for point masses, to the field form NM.05 and NM.06 that Field nominalizes.")
L("nm5", "NM", "Poisson equation for gravitation", r"\nabla^2\phi=4\pi G\rho", [sf + r"\ (C^2)", r"\rho:E^3\to\mathbb R_{\ge0}"],
  "R E3 Ck", "F80", nom="F")
L("nm6", "NM", "Gravitational equation of motion", r"\ddot{\mathbf x}(t)=-\nabla\phi(\mathbf x(t))", [t, xp, sf],
  "R E3 Ck", "F80", nom="F", par=["nm2", "nm5"])
L("nm7", "NM", "Hooke's law (spring)", r"\mathbf F=-k(\mathbf x-\mathbf x_0)", [r"k\in\mathbb R_{>0}", r"\mathbf x,\mathbf x_0\in E^3"], "R E3 Vr", "GPS")
L("nm8", "NM", "Conservation of linear momentum", r"\frac{d}{dt}\sum_{i=1}^n m_i\dot{\mathbf x}_i(t)=\mathbf 0\quad(\text{isolated system})",
  [r"n\in\mathbb N", r"i\in\{1,\dots,n\}", r"m_i\in\mathbb R_{>0}", r"\mathbf x_i:\mathbb R\to E^3"], "R E3 Vr Ck Fin", "GPS", par=["nm2", "nm3"])
L("nm9", "NM", "Angular momentum theorem", r"\frac{d\mathbf L}{dt}=\boldsymbol\tau,\quad \mathbf L=\mathbf x\times m\dot{\mathbf x},\ \boldsymbol\tau=\mathbf x\times\mathbf F",
  [t, xp, m, F3], "R E3 Vr Ck", "GPS", par=["nm2"])
L("nm10", "NM", "Work--energy theorem", r"\int_{t_0}^{t_1}\mathbf F\cdot\dot{\mathbf x}\,dt=\tfrac12 m|\dot{\mathbf x}(t_1)|^2-\tfrac12 m|\dot{\mathbf x}(t_0)|^2",
  [r"t_0,t_1\in\mathbb R", xp, m, F3], "R E3 Vr Ck", "GPS", par=["nm2"])
L("nm11", "NM", "Conservation of mechanical energy", r"\tfrac12 m|\dot{\mathbf x}|^2+V(\mathbf x)=E,\quad \mathbf F=-\nabla V",
  [xp, r"V:E^3\to\mathbb R\ (C^1)", r"E\in\mathbb R"], "R E3 Ck", "GPS", par=["nm10"])
L("nm12", "NM", "Kepler's third law", r"T^2=\frac{4\pi^2a^3}{G(M+m)}", [r"T,a,M,m\in\mathbb R_{>0}"], "R", "GPS", par=["nm2", "nm4"])
L("nm13", "NM", "Kepler's second law (central forces)", r"\frac{dA}{dt}=\tfrac12|\mathbf r\times\dot{\mathbf r}|=\text{const}",
  [r"\mathbf r:\mathbb R\to\mathbb R^3", r"A:\mathbb R\to\mathbb R"], "R Vr Ck", "GPS", par=["nm9"])
L("nm14", "NM", "Kepler's first law (bound orbits)", r"r(\theta)=\frac{a(1-e^2)}{1+e\cos\theta},\quad 0\le e<1",
  [r"\theta\in[0,2\pi)", r"a\in\mathbb R_{>0}", r"e\in[0,1)"], "R Ck", "GPS", par=["nm2", "nm4"])
L("nm15", "NM", "Euler's equations for a rigid body", r"I_1\dot\omega_1+(I_3-I_2)\,\omega_2\omega_3=\tau_1\ \ (\text{and cyclically})",
  [r"I_k\in\mathbb R_{>0}", r"\boldsymbol\omega,\boldsymbol\tau:\mathbb R\to\mathbb R^3"], "R Vr Lin SO3 Ck", "GPS")
L("nm16", "NM", "Inertia tensor", r"I_{jk}=\int\rho(\mathbf x)\big(|\mathbf x|^2\delta_{jk}-x_jx_k\big)\,d^3x",
  [r"\rho:E^3\to\mathbb R_{\ge0}", r"j,k\in\{1,2,3\}"], "R E3 Lin Ck", "GPS")
L("nm17", "NM", "Galilean boost", r"\mathbf x'=\mathbf x-\mathbf v t,\quad t'=t", [t, r"\mathbf x\in E^3", r"\mathbf v\in\mathbb R^3"], "R E3 Gal Lie", "GPS",
  note="The transformations form a Lie group; invariance under it quantifies over its elements.")
L("nm18", "NM", "Motion of the centre of mass", r"M\ddot{\mathbf X}=\mathbf F_{\mathrm{ext}},\quad \mathbf X=\frac1M\sum_i m_i\mathbf x_i",
  [r"i\in\{1,\dots,n\}", r"m_i\in\mathbb R_{>0}", r"\mathbf x_i:\mathbb R\to E^3"], "R E3 Vr Ck Fin", "GPS", par=["nm2", "nm3"])
L("nm19", "NM", "Simple harmonic oscillator", r"m\ddot x+kx=0,\quad x(t)=A\cos(\omega t+\varphi),\ \omega=\sqrt{k/m}",
  [t, r"x:\mathbb R\to\mathbb R", r"k,m\in\mathbb R_{>0}", r"A,\varphi\in\mathbb R"], "R Ck", "GPS", par=["nm2", "nm7"])
L("nm20", "NM", "Damped driven oscillator", r"m\ddot x+b\dot x+kx=F_0\cos\Omega t", [t, r"x:\mathbb R\to\mathbb R", r"m,b,k,F_0,\Omega\in\mathbb R"], "R Ck", "GPS")
L("nm21", "NM", "Uniformly rotating frame", r"m\ddot{\mathbf x}'=\mathbf F-2m\boldsymbol\Omega\times\dot{\mathbf x}'-m\boldsymbol\Omega\times(\boldsymbol\Omega\times\mathbf x')",
  [t, r"\mathbf x':\mathbb R\to\mathbb R^3", r"\boldsymbol\Omega\in\mathbb R^3"], "R Vr Ck SO3", "GPS")
L("nm22", "NM", "Virial theorem", r"2\langle T\rangle=-\sum_k\langle\mathbf F_k\cdot\mathbf x_k\rangle\quad(\text{time averages, bounded motion})",
  [r"\langle f\rangle=\lim_{\tau\to\infty}\frac1\tau\int_0^\tau f\,dt", r"k\in\{1,\dots,n\}"], "R Vr Ck Seq Fin", "GPS")
L("nm23", "NM", "Newtonian $n$-body problem", r"m_i\ddot{\mathbf x}_i=\sum_{j\neq i}G\,m_im_j\frac{\mathbf x_j-\mathbf x_i}{|\mathbf x_j-\mathbf x_i|^3}",
  [r"i,j\in\{1,\dots,n\}", r"\mathbf x_i:\mathbb R\to E^3", r"m_i\in\mathbb R_{>0}"], "R E3 Vr Ck Fin", "GPS", nom="F", par=["nm2", "nm4"])
L("nm24", "NM", "Escape velocity", r"v_{\mathrm e}=\sqrt{2GM/r}", [r"M,r\in\mathbb R_{>0}"], "R", "GPS", par=["nm11", "nm4"])
L("nm25", "NM", "Impulse--momentum", r"\Delta\mathbf p=\int_{t_0}^{t_1}\mathbf F(t)\,dt", [r"t_0,t_1\in\mathbb R", F3], "R Vr Ck", "GPS", par=["nm2"])
L("nm26", "NM", "Elastic collision in one dimension", r"v_1'=\frac{(m_1-m_2)v_1+2m_2v_2}{m_1+m_2}", [r"m_1,m_2\in\mathbb R_{>0}", r"v_1,v_2\in\mathbb R"], "R", "GPS", par=["nm8", "nm11"])
L("nm27", "NM", "Range of a projectile (level ground, no drag)", r"R=\frac{v_0^2\sin 2\theta}{g}", [r"v_0,g\in\mathbb R_{>0}", r"\theta\in(0,\pi/2)"], "R Ck", "GPS", par=["nm2"])
L("nm28", "NM", "Period of the simple pendulum (small amplitude)", r"T=2\pi\sqrt{\ell/g}", [r"\ell,g\in\mathbb R_{>0}"], "R", "GPS", par=["nm19"])
L("nm29", "NM", "Coulomb friction", r"|F_{\mathrm s}|\le\mu_{\mathrm s}N,\quad |F_{\mathrm k}|=\mu_{\mathrm k}N", [r"\mu_{\mathrm s},\mu_{\mathrm k},N\in\mathbb R_{\ge0}"], "R", "GPS")
L("nm30", "NM", "Rocket equation", r"\Delta v=v_{\mathrm e}\ln\frac{m_0}{m_1}", [r"v_{\mathrm e},m_0,m_1\in\mathbb R_{>0}"], "R Ck", "GPS", par=["nm8"])
L("nm31", "NM", "Parallel-axis theorem", r"I=I_{\mathrm{cm}}+Md^2", [r"I_{\mathrm{cm}},M,d\in\mathbb R_{\ge0}"], "R", "GPS", par=["nm16"])
L("nm32", "NM", "Reduction of the two-body problem", r"\mu\ddot{\mathbf r}=\mathbf F(\mathbf r),\quad \mu=\frac{m_1m_2}{m_1+m_2}",
  [r"\mathbf r:\mathbb R\to\mathbb R^3", r"m_1,m_2\in\mathbb R_{>0}"], "R Vr Ck", "GPS", par=["nm2", "nm3"])

# ---------------------------------------------------------------- Lagrangian mechanics
L("lm1", "LM", "Euler--Lagrange equations", r"\frac{d}{dt}\frac{\partial L}{\partial\dot q^i}-\frac{\partial L}{\partial q^i}=0", [t, q, Lg], "R Man TM StS Ck", "GPS")
L("lm2", "LM", "Hamilton's principle", r"\delta\int_{t_0}^{t_1}L(q,\dot q,t)\,dt=0\quad(\delta q(t_0)=\delta q(t_1)=0)",
  [q, Lg, r"\delta q:[t_0,t_1]\to TQ\ (\text{all variations})"], "R Man TM StS Ck", "GPS", var=True)
L("lm3", "LM", "Natural Lagrangian", r"L=\tfrac12\sum_i m_i|\dot{\mathbf x}_i|^2-V(\mathbf x_1,\dots,\mathbf x_n)", [Lg, r"V:(E^3)^n\to\mathbb R"], "R E3 StS Ck Fin", "GPS")
L("lm4", "LM", "Noether's theorem (mechanics)", r"\delta q^i=\epsilon K^i(q),\ \delta L=0\ \Rightarrow\ \frac{d}{dt}\Big(\sum_i\frac{\partial L}{\partial\dot q^i}K^i\Big)=0",
  [q, Lg, r"K:Q\to TQ"], "R Man TM StS Ck Lie", "GPS")
L("lm5", "LM", "Lagrange multipliers (holonomic constraints)", r"\frac{d}{dt}\frac{\partial L}{\partial\dot q^i}-\frac{\partial L}{\partial q^i}=\sum_a\lambda_a\frac{\partial f_a}{\partial q^i},\quad f_a(q,t)=0",
  [q, Lg, r"\lambda_a:\mathbb R\to\mathbb R", r"f_a:Q\times\mathbb R\to\mathbb R"], "R Man StS Ck Fin", "GPS")
L("lm6", "LM", "Conjugate momenta and cyclic coordinates", r"p_i=\frac{\partial L}{\partial\dot q^i};\quad \frac{\partial L}{\partial q^k}=0\Rightarrow \dot p_k=0", [q, Lg], "R Man TM StS Ck", "GPS", par=["lm1"])
L("lm7", "LM", "Rayleigh dissipation", r"\frac{d}{dt}\frac{\partial L}{\partial\dot q^i}-\frac{\partial L}{\partial q^i}+\frac{\partial\mathcal F}{\partial\dot q^i}=0,\quad \mathcal F=\tfrac12\sum_i c_i(\dot q^i)^2",
  [q, Lg, r"c_i\in\mathbb R_{\ge0}"], "R Man StS Ck", "GPS")
L("lm8", "LM", "Normal modes of small oscillations", r"\det(V-\omega^2T)=0,\quad V_{ij}=\frac{\partial^2V}{\partial q^i\partial q^j}\Big|_{q_0}",
  [r"V,T\in\mathbb R^{n\times n}\text{ symmetric}", r"\omega\in\mathbb R"], "R Lin Vr Ck", "GPS")
L("lm9", "LM", "Energy function", r"h=\sum_i\dot q^i\frac{\partial L}{\partial\dot q^i}-L,\quad \frac{dh}{dt}=-\frac{\partial L}{\partial t}", [q, Lg], "R Man TM StS Ck", "GPS", par=["lm1"])
L("lm10", "LM", "Lagrangian of a charged particle", r"L=\tfrac12m|\dot{\mathbf x}|^2-q\phi(\mathbf x,t)+q\,\dot{\mathbf x}\cdot\mathbf A(\mathbf x,t)",
  [xp, r"\phi:E^3\times\mathbb R\to\mathbb R", r"\mathbf A:E^3\times\mathbb R\to\mathbb R^3"], "R E3 StS Ck", "GPS")
L("lm11", "LM", "Maupertuis' principle", r"\delta\int\mathbf p\cdot d\mathbf q=0\quad(\text{fixed energy})", [q, r"\text{varied paths in }Q"], "R Man StS Ck", "GPS", var=True)
L("lm12", "LM", "D'Alembert's principle", r"\sum_i(\mathbf F_i-m_i\ddot{\mathbf x}_i)\cdot\delta\mathbf x_i=0\quad(\text{all virtual displacements})",
  [r"\mathbf x_i:\mathbb R\to E^3", r"\delta\mathbf x_i\in\mathbb R^3"], "R E3 Vr Ck Fin", "GPS", var=True)
L("lm13", "LM", "Euler--Lagrange equations for fields", r"\partial_\mu\frac{\partial\mathcal L}{\partial(\partial_\mu\phi)}-\frac{\partial\mathcal L}{\partial\phi}=0",
  [r"\phi:M\to\mathbb R", r"\mathcal L:J^1\to\mathbb R\ (\text{jet space})"], "R Man Tens StS Ck", "GPS")

# ---------------------------------------------------------------- Hamiltonian mechanics
L("hm1", "HM", "Hamilton's equations", r"\dot q^i=\frac{\partial H}{\partial p_i},\quad \dot p_i=-\frac{\partial H}{\partial q^i}", [t, H, r"(q,p):\mathbb R\to T^*Q"], "R StS Symp Ck", "ARN")
L("hm2", "HM", "Legendre transformation", r"H(q,p,t)=\sum_ip_i\dot q^i-L(q,\dot q,t),\quad p_i=\frac{\partial L}{\partial\dot q^i}", [H, Lg], "R StS Symp Ck", "GPS", par=["lm6"])
L("hm3", "HM", "Evolution by Poisson bracket", r"\frac{df}{dt}=\{f,H\}+\frac{\partial f}{\partial t},\quad \{f,g\}=\sum_i\Big(\frac{\partial f}{\partial q^i}\frac{\partial g}{\partial p_i}-\frac{\partial f}{\partial p_i}\frac{\partial g}{\partial q^i}\Big)",
  [r"f,g:T^*Q\times\mathbb R\to\mathbb R", H], "R StS Symp Ck LieA", "GPS", par=["hm1"])
L("hm4", "HM", "Canonical brackets", r"\{q^i,p_j\}=\delta^i_j,\quad \{q^i,q^j\}=\{p_i,p_j\}=0", [r"i,j\in\{1,\dots,n\}"], "R StS Symp LieA Fin", "GPS")
L("hm5", "HM", "Liouville equation", r"\frac{\partial\rho}{\partial t}+\{\rho,H\}=0", [r"\rho:T^*Q\times\mathbb R\to\mathbb R_{\ge0}", H], "R StS Symp Meas Ck", "ARN", par=["hm1"])
L("hm6", "HM", "Liouville's theorem (phase volume)", r"\phi_t^{*}(\omega^n)=\omega^n", [r"\phi_t:T^*Q\to T^*Q\ (\text{flow of }X_H)", t], "R StS Symp Meas", "ARN", par=["hm1"])
L("hm7", "HM", "Symplectic form of Hamiltonian vector fields", r"\iota_{X_H}\omega=dH,\quad \omega=\sum_i dq^i\wedge dp_i", [r"X_H\text{ vector field on }T^*Q", H], "R StS Symp Tens", "ARN")
L("hm8", "HM", "Hamilton--Jacobi equation", r"\frac{\partial S}{\partial t}+H\Big(q,\frac{\partial S}{\partial q},t\Big)=0", [r"S:Q\times\mathbb R\to\mathbb R", H], "R StS Symp Ck", "GPS")
L("hm9", "HM", "Canonical transformations", r"\Phi^{*}\omega=\omega", [r"\Phi:T^*Q\to T^*Q"], "R StS Symp Tens", "ARN")
L("hm10", "HM", "Action--angle variables", r"J=\frac{1}{2\pi}\oint p\,dq,\quad \dot\theta=\frac{\partial H}{\partial J}", [r"(J,\theta)\in\mathbb R\times S^1", H], "R StS Symp Ck", "GPS")
L("hm11", "HM", "Poincar\\'e recurrence", r"\mu(D)<\infty,\ \phi_t(D)=D\ \Rightarrow\ \text{a.e. }x\in U\subseteq D\text{ returns to }U\text{ infinitely often}",
  [r"\mu\text{ invariant measure on }T^*Q", r"U\text{ measurable}"], "R N StS Meas", "ARN")
L("hm12", "HM", "Conserved quantities", r"\{G,H\}=0\ \Rightarrow\ \frac{dG}{dt}=0", [r"G,H:T^*Q\to\mathbb R"], "R StS Symp LieA", "ARN", par=["hm3"])
L("hm13", "HM", "Hamiltonian of a charged particle", r"H=\frac{1}{2m}|\mathbf p-q\mathbf A|^2+q\phi", [r"(\mathbf x,\mathbf p)\in T^*E^3", r"\phi,\mathbf A\text{ potentials}"], "R E3 StS Symp", "GPS", par=["lm10", "hm2"])
L("hm14", "HM", "Liouville--Arnold theorem", r"\{F_i,F_j\}=0\ (i,j\le n),\ dF_1\wedge\cdots\wedge dF_n\neq0\ \Rightarrow\ \text{compact level sets are tori }T^n",
  [r"F_1,\dots,F_n:T^*Q\to\mathbb R"], "R StS Symp Lie Tens", "ARN")

# ---------------------------------------------------------------- Continuum mechanics of solids
L("cm1", "CM", "Conservation of mass (referential form)", r"\rho(\mathbf x,t)\det\mathbf F(\mathbf X,t)=\rho_0(\mathbf X)", [r"\mathbf X\in B\subseteq E^3", r"\mathbf F=\nabla\chi,\ \chi:B\times\mathbb R\to E^3"], "R E3 Lin Ck", "GUR")
L("cm2", "CM", "Cauchy's equation of motion", r"\rho\dot{\mathbf v}=\operatorname{div}\boldsymbol\sigma+\rho\mathbf b", [rho, vf, r"\boldsymbol\sigma:E^3\times\mathbb R\to\mathrm{Sym}(3)"], "R E3 Lin Ck", "GUR")
L("cm3", "CM", "Symmetry of the Cauchy stress", r"\boldsymbol\sigma=\boldsymbol\sigma^{\mathsf T}", [r"\boldsymbol\sigma:E^3\to\mathbb R^{3\times3}"], "R E3 Lin", "GUR")
L("cm4", "CM", "Cauchy's stress theorem", r"\mathbf t(\mathbf x,\mathbf n)=\boldsymbol\sigma(\mathbf x)\mathbf n", [r"\mathbf n\in S^2", r"\mathbf x\in E^3"], "R E3 Lin", "GUR")
L("cm5", "CM", "Isotropic linear elasticity", r"\boldsymbol\sigma=\lambda(\operatorname{tr}\boldsymbol\varepsilon)\mathbf I+2\mu\boldsymbol\varepsilon", [r"\lambda,\mu\in\mathbb R", r"\boldsymbol\varepsilon\in\mathrm{Sym}(3)"], "R Lin", "GUR")
L("cm6", "CM", "Infinitesimal strain", r"\boldsymbol\varepsilon=\tfrac12(\nabla\mathbf u+\nabla\mathbf u^{\mathsf T})", [r"\mathbf u:E^3\to\mathbb R^3\ (C^1)"], "R E3 Lin Ck", "GUR")
L("cm7", "CM", "Navier--Cauchy equations", r"(\lambda+\mu)\nabla(\nabla\cdot\mathbf u)+\mu\nabla^2\mathbf u+\rho\mathbf b=\rho\,\ddot{\mathbf u}", [r"\mathbf u:E^3\times\mathbb R\to\mathbb R^3"], "R E3 Ck", "GUR", par=["cm2", "cm5", "cm6"])
L("cm8", "CM", "Elastic wave speeds", r"c_P=\sqrt{(\lambda+2\mu)/\rho},\quad c_S=\sqrt{\mu/\rho}", [r"\lambda,\mu,\rho\in\mathbb R_{>0}"], "R", "GUR", par=["cm7"])
L("cm9", "CM", "Euler--Bernoulli beam", r"EI\,\frac{d^4w}{dx^4}=q(x)", [r"w,q:[0,\ell]\to\mathbb R"], "R Ck", "GUR")
L("cm10", "CM", "Vibrating string", r"\frac{\partial^2y}{\partial t^2}=\frac{T}{\mu}\frac{\partial^2y}{\partial x^2}", [r"y:[0,\ell]\times\mathbb R\to\mathbb R", r"T,\mu\in\mathbb R_{>0}"], "R Ck", "GUR")
L("cm11", "CM", "Polar decomposition of the deformation gradient", r"\mathbf F=\mathbf R\mathbf U,\quad \mathbf R\in SO(3),\ \mathbf U=\mathbf U^{\mathsf T}>0", [r"\mathbf F\in GL^+(3)"], "R Lin SO3", "GUR")
L("cm12", "CM", "Balance of energy", r"\rho\dot\varepsilon=\boldsymbol\sigma:\mathbf D-\operatorname{div}\mathbf q+\rho r", [rho, r"\mathbf q:E^3\times\mathbb R\to\mathbb R^3", r"\mathbf D=\mathrm{sym}\nabla\mathbf v"], "R E3 Lin Ck", "GUR")
L("cm13", "CM", "Clausius--Duhem inequality", r"\rho\dot\eta\ge-\operatorname{div}\frac{\mathbf q}{\theta}+\frac{\rho r}{\theta}", [r"\eta,\theta:E^3\times\mathbb R\to\mathbb R", r"\mathbf q:E^3\times\mathbb R\to\mathbb R^3"], "R E3 Ck", "GUR")
L("cm14", "CM", "Material frame-indifference", r"\boldsymbol\sigma^{*}=\mathbf Q\boldsymbol\sigma\mathbf Q^{\mathsf T}\ \text{ under }\ \mathbf x^{*}=\mathbf Q(t)\mathbf x+\mathbf c(t)",
  [r"\mathbf Q:\mathbb R\to O(3)", r"\mathbf c:\mathbb R\to\mathbb R^3"], "R E3 Lin SO3 Lie", "GUR")
L("cm15", "CM", "Young's modulus and Poisson's ratio", r"E=\frac{\mu(3\lambda+2\mu)}{\lambda+\mu},\quad \nu=\frac{\lambda}{2(\lambda+\mu)}", [r"\lambda,\mu\in\mathbb R_{>0}"], "R", "GUR", par=["cm5"])
L("cm16", "CM", "Reynolds transport theorem", r"\frac{d}{dt}\int_{\Omega_t}f\,dV=\int_{\Omega_t}\big(\partial_tf+\nabla\cdot(f\mathbf v)\big)\,dV", [r"\Omega_t\subseteq E^3\text{ material region}", r"f:E^3\times\mathbb R\to\mathbb R"], "R E3 Ck", "GUR")
L("cm17", "CM", "Saint-Venant compatibility", r"\nabla\times(\nabla\times\boldsymbol\varepsilon)^{\mathsf T}=\mathbf 0\quad(\text{simply connected body})", [r"\boldsymbol\varepsilon:E^3\to\mathrm{Sym}(3)\ (C^2)"], "R E3 Lin Ck", "GUR")

# ---------------------------------------------------------------- Fluid dynamics and acoustics
L("fd1", "FD", "Continuity equation", r"\partial_t\rho+\nabla\cdot(\rho\mathbf v)=0", [rho, vf], "R E3 Ck", "LLF")
L("fd2", "FD", "Euler equations", r"\rho\big(\partial_t\mathbf v+(\mathbf v\cdot\nabla)\mathbf v\big)=-\nabla p+\rho\mathbf g", [rho, vf, r"p:E^3\times\mathbb R\to\mathbb R"], "R E3 Ck", "LLF")
L("fd3", "FD", "Incompressible Navier--Stokes equations", r"\rho\big(\partial_t\mathbf v+(\mathbf v\cdot\nabla)\mathbf v\big)=-\nabla p+\mu\nabla^2\mathbf v+\mathbf f,\quad \nabla\cdot\mathbf v=0",
  [vf, r"p:E^3\times\mathbb R\to\mathbb R", r"\rho,\mu\in\mathbb R_{>0}"], "R E3 Ck", "LLF")
L("fd4", "FD", "Bernoulli's equation", r"p+\tfrac12\rho|\mathbf v|^2+\rho gz=\text{const along a streamline}", [r"\text{streamlines }\gamma\subseteq E^3", r"\rho,g\in\mathbb R_{>0}"], "R E3 Ck", "LLF", par=["fd2"])
L("fd5", "FD", "Kelvin's circulation theorem", r"\frac{d\Gamma}{dt}=0,\quad \Gamma(t)=\oint_{C(t)}\mathbf v\cdot d\mathbf l", [r"C(t)\text{ material loop}", vf], "R E3 Ck", "LLF", par=["fd2"])
L("fd6", "FD", "Vorticity equation (incompressible)", r"\frac{D\boldsymbol\omega}{Dt}=(\boldsymbol\omega\cdot\nabla)\mathbf v+\nu\nabla^2\boldsymbol\omega,\quad \boldsymbol\omega=\nabla\times\mathbf v", [vf, r"\nu\in\mathbb R_{>0}"], "R E3 Ck", "LLF", par=["fd3"])
L("fd7", "FD", "Hagen--Poiseuille law", r"Q=\frac{\pi R^4\Delta p}{8\mu L}", [r"R,L,\mu,\Delta p\in\mathbb R_{>0}"], "R", "LLF", par=["fd3"])
L("fd8", "FD", "Stokes drag", r"F=6\pi\mu Rv", [r"\mu,R,v\in\mathbb R_{>0}"], "R", "LLF", par=["fd3"])
L("fd9", "FD", "Reynolds number (dynamic similarity)", r"\mathrm{Re}=\frac{\rho vL}{\mu}", [r"\rho,v,L,\mu\in\mathbb R_{>0}"], "R", "LLF")
L("fd10", "FD", "Archimedes' principle", r"\mathbf F_B=-\rho_f V\mathbf g", [r"\rho_f,V\in\mathbb R_{>0}", r"\mathbf g\in\mathbb R^3"], "R Vr", "LLF", par=["fd11"])
L("fd11", "FD", "Hydrostatic equilibrium", r"\nabla p=\rho\mathbf g", [r"p:E^3\to\mathbb R", r"\rho:E^3\to\mathbb R_{>0}"], "R E3 Ck", "LLF")
L("fd12", "FD", "Darcy's law", r"\mathbf q=-\frac{k}{\mu}\nabla p", [r"p:E^3\to\mathbb R", r"k,\mu\in\mathbb R_{>0}"], "R E3 Ck", "LLF")
L("fd13", "FD", "Potential flow", r"\mathbf v=\nabla\varphi,\quad \nabla^2\varphi=0", [r"\varphi:E^3\to\mathbb R\ (C^2)"], "R E3 Ck", "LLF")
L("fd14", "FD", "Complex potential (plane flow)", r"w(z)=\varphi+i\psi\ \text{holomorphic},\quad w'(z)=v_x-iv_y", [r"z\in U\subseteq\mathbb C", r"w:U\to\mathbb C"], "R C CA", "LLF", red=True)
L("fd15", "FD", "Kutta--Joukowski theorem", r"L'=\rho V\Gamma\quad(\text{lift per unit span})", [r"\rho,V\in\mathbb R_{>0}", r"\Gamma\in\mathbb R"], "R C CA", "LLF", red=True, par=["fd16"],
  note="The statement is real-valued; the standard proof evaluates the contour integral of FD.16 (Blasius).")
L("fd16", "FD", "Blasius theorem", r"F_x-iF_y=\frac{i\rho}{2}\oint_C\Big(\frac{dw}{dz}\Big)^2dz", [r"C\subseteq\mathbb C\text{ closed contour}", r"w:U\to\mathbb C"], "R C CA", "LLF", red=True, par=["fd14"])
L("fd17", "FD", "Speed of sound", r"c^2=\Big(\frac{\partial p}{\partial\rho}\Big)_s", [r"p(\rho,s)\text{ equation of state}"], "R Ck", "LLF")
L("fd18", "FD", "Linear acoustic wave equation", r"\frac{\partial^2p'}{\partial t^2}=c^2\nabla^2p'", [r"p':E^3\times\mathbb R\to\mathbb R"], "R E3 Ck", "LLF", par=["fd1", "fd2"])
L("fd19", "FD", "Rankine--Hugoniot conditions (normal shock)", r"\rho_1u_1=\rho_2u_2,\quad p_1+\rho_1u_1^2=p_2+\rho_2u_2^2", [r"\rho_k,u_k,p_k\in\mathbb R"], "R", "LLF", par=["fd1", "fd2"])
L("fd20", "FD", "Acoustic Doppler effect", r"f'=f\,\frac{c+v_{\mathrm o}}{c-v_{\mathrm s}}\quad(\text{approach along the line of sight})", [r"f,c\in\mathbb R_{>0}", r"v_{\mathrm o},v_{\mathrm s}\in[0,c)"], "R", "LLF")
L("fd21", "FD", "Compressible Navier--Stokes momentum equation", r"\rho\frac{D\mathbf v}{Dt}=-\nabla p+\nabla\cdot\boldsymbol\tau+\rho\mathbf g,\quad \boldsymbol\tau=\mu(\nabla\mathbf v+\nabla\mathbf v^{\mathsf T})+\lambda(\nabla\cdot\mathbf v)\mathbf I",
  [rho, vf, r"\mu,\lambda\in\mathbb R"], "R E3 Lin Ck", "LLF")
L("fd22", "FD", "Torricelli's law", r"v=\sqrt{2gh}", [r"g,h\in\mathbb R_{>0}"], "R", "LLF", par=["fd4"])
L("fd23", "FD", "Kolmogorov spectrum (inertial range)", r"E(k)=C\,\varepsilon^{2/3}k^{-5/3}", [r"k\in\mathbb R_{>0}", r"\varepsilon\in\mathbb R_{>0}", r"E\text{ ensemble-averaged spectrum}"], "R Prob Stoch", "LLF",
  note="A statistical law: $E(k)$ is defined by ensemble averages over turbulent velocity fields.")
L("fd24", "FD", "Young--Laplace equation", r"\Delta p=\gamma\Big(\frac1{R_1}+\frac1{R_2}\Big)", [r"\gamma\in\mathbb R_{>0}", r"R_1,R_2\in\mathbb R\setminus\{0\}"], "R E3 Ck", "LLF")
L("fd25", "FD", "Stokes equations (creeping flow)", r"\mu\nabla^2\mathbf v=\nabla p,\quad \nabla\cdot\mathbf v=0", [vf, r"p:E^3\to\mathbb R"], "R E3 Ck", "LLF", par=["fd3"])

# ---------------------------------------------------------------- Thermodynamics
L("td1", "TD", "Zeroth law", r"A\sim B\ \wedge\ B\sim C\ \Rightarrow\ A\sim C\quad(\sim\text{: thermal equilibrium})", [r"A,B,C\text{ systems (concrete)}"], "", "CAL",
  note="No mathematical structure is quantified over: the law is stated in the vocabulary of systems and one relation.")
L("td2", "TD", "First law", r"dU=\delta Q-\delta W,\quad \delta W=p\,dV\ (\text{quasi-static})", [r"U:\Sigma\to\mathbb R\ (\Sigma\text{ equilibrium state space})", r"\delta Q,\delta W\text{ 1-forms on }\Sigma"], "R StS Tens", "CAL")
L("td3", "TD", "Clausius inequality", r"\oint\frac{\delta Q}{T}\le0", [r"\text{cycles }\gamma\text{ in }\Sigma", r"T:\Sigma\to\mathbb R_{>0}"], "R StS Tens", "CAL")
L("td4", "TD", "Definition of entropy", r"dS=\frac{\delta Q_{\mathrm{rev}}}{T}", [r"S:\Sigma\to\mathbb R"], "R StS Tens", "CAL", par=["td3"])
L("td5", "TD", "Fundamental thermodynamic relation", r"dU=T\,dS-p\,dV+\mu\,dN", [r"U(S,V,N)\text{ on }\Sigma"], "R StS Tens", "CAL", par=["td2", "td4"])
L("td6", "TD", "Carnot efficiency", r"\eta=1-\frac{T_{\mathrm c}}{T_{\mathrm h}}", [r"T_{\mathrm c},T_{\mathrm h}\in\mathbb R_{>0}"], "R", "CAL", par=["td3"])
L("td7", "TD", "Third law (Nernst)", r"\lim_{T\to0}\Delta S_T=0\quad(\text{isothermal processes})", [r"S:\Sigma\to\mathbb R", r"T\in\mathbb R_{>0}"], "R StS Top", "CAL")
L("td8", "TD", "Ideal gas law", r"pV=Nk_BT", [r"p,V,T\in\mathbb R_{>0}", r"N\in\mathbb N"], "R N", "CAL")
L("td9", "TD", "Maxwell relation", r"\Big(\frac{\partial T}{\partial V}\Big)_S=-\Big(\frac{\partial p}{\partial S}\Big)_V", [r"U(S,V)\in C^2(\Sigma)"], "R StS Ck", "CAL", par=["td5"])
L("td10", "TD", "Gibbs--Duhem relation", r"S\,dT-V\,dp+N\,d\mu=0", [r"\text{states in }\Sigma"], "R StS Tens", "CAL", par=["td5"])
L("td11", "TD", "Gibbs free energy criterion", r"G=U+pV-TS;\quad \Delta G\le0\ \text{ at fixed }T,p", [r"G:\Sigma\to\mathbb R"], "R StS", "CAL", par=["td5"])
L("td12", "TD", "Clausius--Clapeyron equation", r"\frac{dp}{dT}=\frac{L}{T\,\Delta v}", [r"p(T)\text{ coexistence curve in }\Sigma"], "R StS Ck", "CAL", par=["td11"])
L("td13", "TD", "Gibbs phase rule", r"F=C-P+2", [r"C,P,F\in\mathbb N"], "N", "CAL",
  note="Relates three counts: components, phases, degrees of freedom. Each instance is expressible with numerically definite quantifiers.")
L("td14", "TD", "Van der Waals equation", r"\Big(p+\frac{an^2}{V^2}\Big)(V-nb)=nRT", [r"p,V,T,n\in\mathbb R_{>0}", r"a,b\in\mathbb R_{\ge0}"], "R", "CAL")
L("td15", "TD", "Fourier's law of conduction", r"\mathbf q=-k\nabla T", [r"T:E^3\to\mathbb R_{>0}", r"k\in\mathbb R_{>0}"], "R E3 Ck", "CAL")
L("td16", "TD", "Heat equation", r"\partial_tT=\alpha\nabla^2T", [r"T:E^3\times\mathbb R\to\mathbb R"], "R E3 Ck", "CAL", par=["td15"])
L("td17", "TD", "Stefan--Boltzmann law", r"j=\sigma T^4", [r"T\in\mathbb R_{>0}"], "R", "CAL", par=["sm14"])
L("td18", "TD", "Newton's law of cooling", r"\frac{dT}{dt}=-h\,(T-T_{\mathrm{env}})", [r"T:\mathbb R\to\mathbb R", r"h\in\mathbb R_{>0}"], "R Ck", "CAL")
L("td19", "TD", "Onsager reciprocity", r"J_i=\sum_jL_{ij}X_j,\quad L_{ij}=L_{ji}", [r"i,j\in\{1,\dots,n\}", r"L\in\mathbb R^{n\times n}"], "R Lin Fin", "CAL")
L("td20", "TD", "Wien's displacement law", r"\lambda_{\max}T=b", [r"T\in\mathbb R_{>0}"], "R", "CAL", par=["sm14"])
L("td21", "TD", "Euler relation", r"U=TS-pV+\mu N", [r"U,T,S,p,V,\mu,N\in\mathbb R"], "R", "CAL", par=["td5"])
L("td22", "TD", "Concavity of entropy (stability)", r"S(\lambda X_1+(1-\lambda)X_2)\ge\lambda S(X_1)+(1-\lambda)S(X_2)", [r"X_1,X_2\in\Sigma", r"\lambda\in[0,1]"], "R StS", "CAL")
L("td23", "TD", "Joule--Thomson coefficient", r"\mu_{\mathrm{JT}}=\Big(\frac{\partial T}{\partial p}\Big)_H=\frac{V}{C_p}(T\alpha-1)", [r"\text{states in }\Sigma"], "R StS Ck", "CAL", par=["td5"])
L("td24", "TD", "Mayer's relation (ideal gas)", r"C_p-C_V=nR", [r"n\in\mathbb R_{>0}"], "R", "CAL", par=["td8"])
L("td25", "TD", "Reversible adiabat (ideal gas)", r"pV^{\gamma}=\text{const},\quad \gamma=C_p/C_V", [r"p,V\in\mathbb R_{>0}"], "R", "CAL", par=["td2", "td8"])
L("td26", "TD", "Kelvin--Planck statement", r"\neg\exists\text{ cycle with }W>0,\ Q_{\mathrm{in}}=W\text{ from one reservoir only}", [r"W,Q\in\mathbb R"], "R", "CAL")

# ---------------------------------------------------------------- Statistical mechanics
L("sm1", "SM", "Boltzmann entropy", r"S=k_B\ln W", [r"W\in\mathbb N_{>0}\ (\text{microstates compatible with the macrostate})"], "R N StS", "HUA")
L("sm2", "SM", "Gibbs entropy", r"S=-k_B\sum_ip_i\ln p_i", [r"(p_i)\text{ distribution on microstates}"], "R StS Prob", "HUA")
L("sm3", "SM", "Canonical distribution", r"p_i=\frac{e^{-E_i/k_BT}}{Z},\quad Z=\sum_ie^{-E_i/k_BT}", [r"i\text{ microstates}", r"T\in\mathbb R_{>0}"], "R StS Prob Seq", "HUA")
L("sm4", "SM", "Free energy from the partition function", r"F=-k_BT\ln Z", [r"Z\in\mathbb R_{>0}"], "R StS Prob", "HUA", par=["sm3"])
L("sm5", "SM", "Microcanonical ensemble", r"\mu_E(A)=\frac{\int_{A\cap\{H=E\}}d\sigma/|\nabla H|}{\int_{\{H=E\}}d\sigma/|\nabla H|}", [r"A\subseteq\Gamma\text{ Borel}", r"H:\Gamma\to\mathbb R"], "R StS Symp Meas Prob", "HUA")
L("sm6", "SM", "Grand canonical distribution", r"p_{i,N}=\frac{e^{-(E_i-\mu N)/k_BT}}{\mathcal Z}", [r"N\in\mathbb N", r"\mu\in\mathbb R"], "R N StS Prob Seq", "HUA")
L("sm7", "SM", "Maxwell--Boltzmann speed distribution", r"f(v)=4\pi\Big(\frac{m}{2\pi k_BT}\Big)^{3/2}v^2e^{-mv^2/2k_BT}", [r"v\in\mathbb R_{\ge0}"], "R Prob Ck", "HUA", par=["sm3"])
L("sm8", "SM", "Equipartition theorem", r"\Big\langle\tfrac12 a\,x^2\Big\rangle=\tfrac12k_BT\quad(\text{each quadratic degree of freedom})", [r"x\text{ canonical coordinate}", r"a\in\mathbb R_{>0}"], "R StS Prob", "HUA", par=["sm3"])
L("sm9", "SM", "Boltzmann transport equation", r"\partial_tf+\mathbf v\cdot\nabla_{\mathbf x}f+\frac{\mathbf F}{m}\cdot\nabla_{\mathbf v}f=C[f]", [r"f:\mathbb R^3\times\mathbb R^3\times\mathbb R\to\mathbb R_{\ge0}\ (\mu\text{-space})"], "R StS Meas Ck", "HUA")
L("sm10", "SM", "Boltzmann's H-theorem", r"\frac{d\mathcal H}{dt}\le0,\quad \mathcal H=\int f\ln f\,d^3x\,d^3v", [r"f\text{ solution of SM.09}"], "R StS Meas Ck", "HUA", par=["sm9"])
L("sm11", "SM", "Energy fluctuations", r"\langle(\Delta E)^2\rangle=k_BT^2C_V", [r"\text{canonical ensemble}"], "R StS Prob", "HUA", par=["sm3"])
L("sm12", "SM", "Bose--Einstein distribution", r"\bar n(\varepsilon)=\frac{1}{e^{(\varepsilon-\mu)/k_BT}-1}", [r"\varepsilon\in\mathbb R", r"\mu<\varepsilon"], "R StS Prob", "HUA")
L("sm13", "SM", "Fermi--Dirac distribution", r"\bar n(\varepsilon)=\frac{1}{e^{(\varepsilon-\mu)/k_BT}+1}", [r"\varepsilon,\mu\in\mathbb R"], "R StS Prob", "HUA")
L("sm14", "SM", "Planck's law", r"B_\nu(T)=\frac{2h\nu^3}{c^2}\,\frac{1}{e^{h\nu/k_BT}-1}", [r"\nu,T\in\mathbb R_{>0}"], "R", "HUA", par=["sm12"])
L("sm15", "SM", "Ising model", r"H(s)=-J\sum_{\langle ij\rangle}s_is_j-h\sum_is_i,\quad s_i\in\{-1,+1\}", [r"s\in\{-1,1\}^\Lambda,\ \Lambda\text{ finite lattice}", r"J,h\in\mathbb R"], "R Z Fin Prob", "HUA")
L("sm16", "SM", "Einstein relation", r"D=\mu_mk_BT", [r"D,\mu_m,T\in\mathbb R_{>0}"], "R", "REI")
L("sm17", "SM", "Langevin equation", r"m\dot v=-\gamma v+\xi(t),\quad \langle\xi(t)\xi(t')\rangle=2\gamma k_BT\,\delta(t-t')", [r"\xi\text{ Gaussian white noise}", r"v\text{ stochastic process}"], "R Stoch Dist", "REI")
L("sm18", "SM", "Diffusion equation", r"\partial_t\rho=D\nabla^2\rho", [r"\rho:E^3\times\mathbb R\to\mathbb R_{\ge0}"], "R E3 Ck", "REI", par=["sm19"])
L("sm19", "SM", "Fick's first law", r"\mathbf J=-D\nabla c", [r"c:E^3\to\mathbb R_{\ge0}"], "R E3 Ck", "REI")
L("sm20", "SM", "Mean squared displacement", r"\langle|\mathbf x(t)-\mathbf x(0)|^2\rangle=2dDt", [r"d\in\{1,2,3\}", r"\mathbf x\text{ Brownian path}"], "R Stoch Prob", "REI", par=["sm17"])
L("sm21", "SM", "Birkhoff ergodic theorem", r"\lim_{\tau\to\infty}\frac1\tau\int_0^\tau f(\phi_tx)\,dt=\int_\Gamma f\,d\mu\quad(\mu\text{-a.e. }x,\ \text{ergodic flow})", [r"f\in L^1(\mu)", r"x\in\Gamma"], "R StS Meas Prob", "HUA")
L("sm22", "SM", "Debye $T^3$ law", r"C_V=\frac{12\pi^4}{5}Nk_B\Big(\frac{T}{\Theta_D}\Big)^3\quad(T\ll\Theta_D)", [r"T,\Theta_D\in\mathbb R_{>0}", r"N\in\mathbb N"], "R N", "REI")
L("sm23", "SM", "Sackur--Tetrode equation", r"S=Nk_B\Big[\ln\Big(\frac{V}{N\lambda^3}\Big)+\frac52\Big],\quad \lambda=\frac{h}{\sqrt{2\pi mk_BT}}", [r"N\in\mathbb N", r"V,T\in\mathbb R_{>0}"], "R N", "HUA")
L("sm24", "SM", "Bose--Einstein condensation threshold", r"n\lambda_c^3=\zeta(3/2)", [r"n\in\mathbb R_{>0}", r"\zeta(s)=\textstyle\sum_{k\ge1}k^{-s}"], "R Seq", "HUA", par=["sm12"])
L("sm25", "SM", "Jarzynski equality", r"\big\langle e^{-W/k_BT}\big\rangle=e^{-\Delta F/k_BT}", [r"W\text{ work, random over realizations}"], "R Prob StS", "HUA",
  note="Stated over the ensemble of realizations of a driven process from canonical initial conditions.")
L("sm26", "SM", "Detailed balance", r"\pi_iP_{ij}=\pi_jP_{ji}", [r"i,j\in\text{states}", r"P\text{ stochastic matrix}", r"\pi\text{ stationary distribution}"], "R Prob Lin", "HUA")
L("sm27", "SM", "Fermi energy (free spin-$\\frac12$ gas)", r"E_F=\frac{\hbar^2}{2m}(3\pi^2n)^{2/3}", [r"n\in\mathbb R_{>0}"], "R", "HUA", par=["sm13"])

# ---------------------------------------------------------------- Electromagnetism
L("em1", "EM", "Coulomb's law", r"\mathbf F_{12}=\frac{q_1q_2}{4\pi\varepsilon_0}\frac{\mathbf x_1-\mathbf x_2}{|\mathbf x_1-\mathbf x_2|^3}", [r"q_1,q_2\in\mathbb R", r"\mathbf x_1\ne\mathbf x_2\in E^3"], "R E3 Vr", "JAC")
L("em2", "EM", "Gauss's law", r"\nabla\cdot\mathbf E=\rho/\varepsilon_0", [EB, r"\rho:E^3\times\mathbb R\to\mathbb R"], "R E3 Ck", "JAC")
L("em3", "EM", "Absence of magnetic monopoles", r"\nabla\cdot\mathbf B=0", [EB], "R E3 Ck", "JAC")
L("em4", "EM", "Faraday's law", r"\nabla\times\mathbf E=-\partial_t\mathbf B", [EB], "R E3 Ck", "JAC")
L("em5", "EM", "Amp\\`ere--Maxwell law", r"\nabla\times\mathbf B=\mu_0\mathbf J+\mu_0\varepsilon_0\partial_t\mathbf E", [EB, r"\mathbf J:E^3\times\mathbb R\to\mathbb R^3"], "R E3 Ck", "JAC")
L("em6", "EM", "Lorentz force", r"\mathbf F=q(\mathbf E+\mathbf v\times\mathbf B)", [r"q\in\mathbb R", r"\mathbf v\in\mathbb R^3", EB], "R E3 Vr", "JAC")
L("em7", "EM", "Conservation of charge", r"\partial_t\rho+\nabla\cdot\mathbf J=0", [r"\rho,\mathbf J\text{ source fields}"], "R E3 Ck", "JAC", par=["em2", "em5"])
L("em8", "EM", "Potentials", r"\mathbf E=-\nabla\phi-\partial_t\mathbf A,\quad \mathbf B=\nabla\times\mathbf A", [r"\phi:E^3\times\mathbb R\to\mathbb R", r"\mathbf A:E^3\times\mathbb R\to\mathbb R^3"], "R E3 Ck", "JAC", par=["em3", "em4"])
L("em9", "EM", "Gauge transformations", r"\mathbf A\mapsto\mathbf A+\nabla\chi,\quad \phi\mapsto\phi-\partial_t\chi", [r"\chi:E^3\times\mathbb R\to\mathbb R\ (\text{all smooth }\chi)"], "R E3 Ck", "JAC", par=["em8"],
  note="Invariance of $\\mathbf E$ and $\\mathbf B$ is asserted for every smooth $\\chi$, so the law quantifies over a function space.")
L("em10", "EM", "Electromagnetic wave equation", r"\nabla^2\mathbf E=\mu_0\varepsilon_0\,\partial_t^2\mathbf E,\quad c=1/\sqrt{\mu_0\varepsilon_0}", [EB], "R E3 Ck", "JAC", par=["em4", "em5"])
L("em11", "EM", "Poynting's theorem", r"\partial_tu+\nabla\cdot\mathbf S=-\mathbf J\cdot\mathbf E,\quad \mathbf S=\frac{\mathbf E\times\mathbf B}{\mu_0}", [EB, r"u=\tfrac12(\varepsilon_0|\mathbf E|^2+|\mathbf B|^2/\mu_0)"], "R E3 Ck", "JAC", par=["em4", "em5"])
L("em12", "EM", "Biot--Savart law", r"\mathbf B(\mathbf x)=\frac{\mu_0}{4\pi}\int\frac{\mathbf J(\mathbf x')\times(\mathbf x-\mathbf x')}{|\mathbf x-\mathbf x'|^3}\,d^3x'", [r"\mathbf J:E^3\to\mathbb R^3\ (\text{steady})"], "R E3 Vr Ck", "JAC")
L("em13", "EM", "Ohm's law", r"\mathbf J=\sigma\mathbf E", [r"\sigma\in\mathbb R_{>0}", EB], "R E3", "JAC")
L("em14", "EM", "Faraday's law of induction (integral)", r"\mathcal E=-\frac{d\Phi_B}{dt},\quad \Phi_B=\int_\Sigma\mathbf B\cdot d\mathbf a", [r"\Sigma\text{ surface with boundary loop}"], "R E3 Ck", "JAC", par=["em4"])
L("em15", "EM", "Linear constitutive relations", r"\mathbf D=\varepsilon\mathbf E,\quad \mathbf B=\mu\mathbf H", [r"\varepsilon,\mu\in\mathbb R_{>0}"], "R E3", "JAC")
L("em16", "EM", "Macroscopic Maxwell equations", r"\nabla\cdot\mathbf D=\rho_f,\quad \nabla\times\mathbf H=\mathbf J_f+\partial_t\mathbf D", [r"\mathbf D,\mathbf H:E^3\times\mathbb R\to\mathbb R^3"], "R E3 Ck", "JAC")
L("em17", "EM", "Kirchhoff's circuit laws", r"\sum_{k\in\text{node}}I_k=0,\quad \sum_{k\in\text{loop}}V_k=0", [r"\text{finite circuit graph}", r"I_k,V_k\in\mathbb R"], "R Fin", "JAC")
L("em18", "EM", "Larmor formula", r"P=\frac{q^2a^2}{6\pi\varepsilon_0c^3}", [r"q\in\mathbb R", r"a\in\mathbb R_{\ge0}"], "R", "JAC", par=["em19"])
L("em19", "EM", "Li\\'enard--Wiechert potential", r"\phi(\mathbf x,t)=\frac{q}{4\pi\varepsilon_0}\Big[\frac{1}{(1-\mathbf n\cdot\boldsymbol\beta)R}\Big]_{\mathrm{ret}}", [r"\text{source worldline }\mathbf r:\mathbb R\to E^3", r"t_{\mathrm{ret}}\text{ retarded time}"], "R E3 Vr Ck", "JAC", par=["em20"])
L("em20", "EM", "Retarded potential", r"\phi(\mathbf x,t)=\frac{1}{4\pi\varepsilon_0}\int\frac{\rho(\mathbf x',t-|\mathbf x-\mathbf x'|/c)}{|\mathbf x-\mathbf x'|}\,d^3x'", [r"\rho:E^3\times\mathbb R\to\mathbb R"], "R E3 Ck", "JAC", par=["em8"])
L("em21", "EM", "Covariant Maxwell equations", r"\partial_\mu F^{\mu\nu}=\mu_0J^\nu,\quad \partial_{[\lambda}F_{\mu\nu]}=0", [r"F\text{ antisymmetric tensor field on }\mathbb R^{1,3}"], "R Mink Tens Ck", "JAC")
L("em22", "EM", "Maxwell equations in forms", r"dF=0,\quad d{\star}F\propto{\star}J", [r"F\in\Omega^2(M)", r"J\in\Omega^1(M)"], "R Man Tens", "MTW")
L("em23", "EM", "Electromagnetic Lagrangian density", r"\mathcal L=-\frac{1}{4\mu_0}F_{\mu\nu}F^{\mu\nu}-J^\mu A_\mu", [r"A\text{ (all field configurations varied)}"], "R Mink Tens Ck", "JAC", var=True)
L("em24", "EM", "Complex impedance", r"Z=R+i\omega L+\frac{1}{i\omega C}", [r"R,L,C,\omega\in\mathbb R_{>0}"], "R C", "JAC", red=True)
L("em25", "EM", "Magnetic dipole in a field", r"\boldsymbol\tau=\mathbf m\times\mathbf B,\quad U=-\mathbf m\cdot\mathbf B", [r"\mathbf m,\mathbf B\in\mathbb R^3"], "R Vr", "JAC")
L("em26", "EM", "Capacitance", r"Q=CV,\quad U=\tfrac12CV^2", [r"C\in\mathbb R_{>0}", r"V\in\mathbb R"], "R", "JAC")
L("em27", "EM", "Electrostatic Poisson equation", r"\nabla^2\phi=-\rho/\varepsilon_0", [r"\phi:E^3\to\mathbb R\ (C^2)"], "R E3 Ck", "JAC", par=["em2", "em8"],
  note="Same form as NM.05; Field's construction for that equation is not, in the literature, carried over explicitly.")
L("em28", "EM", "Uniqueness theorem (Dirichlet problem)", r"\nabla^2\phi_1=\nabla^2\phi_2\text{ in }V,\ \phi_1=\phi_2\text{ on }\partial V\ \Rightarrow\ \phi_1=\phi_2", [r"V\subseteq E^3\text{ bounded}", r"\phi_k\in C^2(V)\cap C(\bar V)"], "R E3 Ck Top", "JAC")
L("em29", "EM", "Self-inductance", r"\mathcal E=-L\frac{dI}{dt}", [r"I:\mathbb R\to\mathbb R", r"L\in\mathbb R_{>0}"], "R Ck", "JAC")
L("em30", "EM", "Maxwell stress tensor", r"T_{ij}=\varepsilon_0\big(E_iE_j-\tfrac12\delta_{ij}E^2\big)+\frac1{\mu_0}\big(B_iB_j-\tfrac12\delta_{ij}B^2\big)", [EB], "R E3 Lin", "JAC")
L("em31", "EM", "Plasma frequency", r"\omega_p^2=\frac{ne^2}{\varepsilon_0m_e}", [r"n\in\mathbb R_{>0}"], "R", "JAC")
L("em32", "EM", "Cyclotron frequency", r"\omega_c=\frac{|q|B}{m}", [r"q\in\mathbb R", r"B,m\in\mathbb R_{>0}"], "R", "JAC", par=["em6"])
L("em33", "EM", "Skin depth", r"\delta=\sqrt{\frac{2}{\mu\sigma\omega}}", [r"\mu,\sigma,\omega\in\mathbb R_{>0}"], "R", "JAC")

# ---------------------------------------------------------------- Plasma physics and MHD
B3 = r"\mathbf B:E^3\times\mathbb R\to\mathbb R^3"
L("mh1", "MH", "Ideal Ohm's law", r"\mathbf E+\mathbf v\times\mathbf B=\mathbf 0", [vf, EB], "R E3 Vr", "CHEN")
L("mh2", "MH", "Induction equation", r"\partial_t\mathbf B=\nabla\times(\mathbf v\times\mathbf B)+\eta\nabla^2\mathbf B", [vf, B3, r"\eta\in\mathbb R_{\ge0}"], "R E3 Ck", "CHEN", par=["em4", "em13"])
L("mh3", "MH", "MHD momentum equation", r"\rho\frac{D\mathbf v}{Dt}=-\nabla p+\mathbf J\times\mathbf B", [rho, vf, B3], "R E3 Ck", "CHEN", par=["fd2", "em6"])
L("mh4", "MH", "Alfv\\'en speed", r"v_A=\frac{B}{\sqrt{\mu_0\rho}}", [r"B,\rho\in\mathbb R_{>0}"], "R", "CHEN", par=["mh2", "mh3"])
L("mh5", "MH", "Magnetic pressure and plasma beta", r"p_B=\frac{B^2}{2\mu_0},\quad \beta=\frac{2\mu_0p}{B^2}", [r"p,B\in\mathbb R_{>0}"], "R", "CHEN")
L("mh6", "MH", "Debye length", r"\lambda_D=\sqrt{\frac{\varepsilon_0k_BT_e}{ne^2}}", [r"T_e,n\in\mathbb R_{>0}"], "R", "CHEN")
L("mh7", "MH", "Vlasov equation", r"\partial_tf+\mathbf v\cdot\nabla_{\mathbf x}f+\frac qm(\mathbf E+\mathbf v\times\mathbf B)\cdot\nabla_{\mathbf v}f=0", [r"f:\mathbb R^3\times\mathbb R^3\times\mathbb R\to\mathbb R_{\ge0}\ (\mu\text{-space})", EB], "R StS Meas Ck", "CHEN")
L("mh8", "MH", "Frozen-in flux (ideal MHD)", r"\frac{d}{dt}\int_{\Sigma(t)}\mathbf B\cdot d\mathbf a=0", [r"\Sigma(t)\text{ material surface}", B3], "R E3 Ck", "CHEN", par=["mh2"])
L("mh9", "MH", "Magnetic Reynolds number", r"R_m=\mu_0\sigma vL", [r"\sigma,v,L\in\mathbb R_{>0}"], "R", "CHEN")
L("mh10", "MH", "Larmor radius", r"r_L=\frac{mv_\perp}{|q|B}", [r"v_\perp,m,B\in\mathbb R_{>0}", r"q\in\mathbb R"], "R", "CHEN", par=["em6"])
L("mh11", "MH", "Magnetic moment (adiabatic invariant)", r"\mu=\frac{mv_\perp^2}{2B}=\text{const}", [r"v_\perp,m,B\in\mathbb R_{>0}"], "R", "CHEN")
L("mh12", "MH", "$\\mathbf E\\times\\mathbf B$ drift", r"\mathbf v_E=\frac{\mathbf E\times\mathbf B}{B^2}", [EB], "R Vr", "CHEN", par=["em6"])
L("mh13", "MH", "Bohm--Gross dispersion relation", r"\omega^2=\omega_p^2+3k^2\frac{k_BT_e}{m_e}", [r"k\in\mathbb R", r"T_e\in\mathbb R_{>0}"], "R", "CHEN", par=["em31"])
L("mh14", "MH", "Force-free magnetic field", r"\nabla\times\mathbf B=\alpha\mathbf B", [B3, r"\alpha:E^3\to\mathbb R"], "R E3 Ck", "CHEN")

# ---------------------------------------------------------------- Optics
L("op1", "OP", "Snell's law", r"n_1\sin\theta_1=n_2\sin\theta_2", [r"n_k\in\mathbb R_{\ge1}", r"\theta_k\in[0,\pi/2]"], "R Ck", "BW")
L("op2", "OP", "Law of reflection", r"\theta_r=\theta_i", [r"\text{rays and surface normals in }E^3"], "E3", "BW", nom="S",
  note="Congruence of the angles of incidence and reflection is a statement of synthetic geometry.")
L("op3", "OP", "Fermat's principle", r"\delta\int_\gamma n\,ds=0", [r"\gamma\text{ ranges over varied paths}", r"n:E^3\to\mathbb R_{\ge1}"], "R E3 Ck", "BW", var=True)
L("op4", "OP", "Thin lens equation", r"\frac1f=\frac1{d_o}+\frac1{d_i}", [r"f,d_o,d_i\in\mathbb R\setminus\{0\}"], "R", "BW")
L("op5", "OP", "Lensmaker's equation (thin lens in air)", r"\frac1f=(n-1)\Big(\frac1{R_1}-\frac1{R_2}\Big)", [r"n\in\mathbb R_{>1}", r"R_1,R_2\in\mathbb R\setminus\{0\}"], "R", "BW", par=["op1"])
L("op6", "OP", "Malus's law", r"I=I_0\cos^2\theta", [r"I_0\in\mathbb R_{\ge0}", r"\theta\in\mathbb R"], "R Ck", "BW")
L("op7", "OP", "Brewster's angle", r"\tan\theta_B=n_2/n_1", [r"n_1,n_2\in\mathbb R_{\ge1}"], "R Ck", "BW", par=["op15"])
L("op8", "OP", "Two-slit interference maxima", r"d\sin\theta=m\lambda,\quad m\in\mathbb Z", [r"m\in\mathbb Z", r"d,\lambda\in\mathbb R_{>0}"], "R Z Ck", "BW")
L("op9", "OP", "Single-slit diffraction minima", r"a\sin\theta=m\lambda,\quad m\in\mathbb Z\setminus\{0\}", [r"m\in\mathbb Z\setminus\{0\}", r"a,\lambda\in\mathbb R_{>0}"], "R Z Ck", "BW")
L("op10", "OP", "Rayleigh criterion (circular aperture)", r"\sin\theta=\frac{j_{1,1}}{\pi}\frac{\lambda}{D}", [r"j_{1,1}\text{ first positive zero of }J_1", r"\lambda,D\in\mathbb R_{>0}"], "R Ck Seq", "BW")
L("op11", "OP", "Fraunhofer diffraction", r"U(\mathbf k)\propto\int_{\mathcal A}U_0(\mathbf x)\,e^{-i\mathbf k\cdot\mathbf x}\,d^2x", [r"U_0:\mathcal A\to\mathbb C", r"\mathbf k\in\mathbb R^2"], "R C Ck", "BW", red=True)
L("op12", "OP", "Helmholtz equation", r"\nabla^2U+k^2U=0", [r"U:E^3\to\mathbb C", r"k\in\mathbb R_{>0}"], "R C E3 Ck", "BW", red=True, par=["em10"])
L("op13", "OP", "Eikonal equation", r"|\nabla S|^2=n^2", [r"S:E^3\to\mathbb R", r"n:E^3\to\mathbb R_{\ge1}"], "R E3 Ck", "BW")
L("op14", "OP", "Beer--Lambert law", r"I(\ell)=I_0e^{-\alpha\ell}", [r"\ell,\alpha\in\mathbb R_{\ge0}"], "R Ck", "BW")
L("op15", "OP", "Fresnel equations (s-polarization)", r"r_s=\frac{n_1\cos\theta_i-n_2\cos\theta_t}{n_1\cos\theta_i+n_2\cos\theta_t},\quad t_s=\frac{2n_1\cos\theta_i}{n_1\cos\theta_i+n_2\cos\theta_t}", [r"n_k\in\mathbb R_{\ge1}", r"\theta_i,\theta_t\in[0,\pi/2]"], "R Ck", "BW", par=["em16"])
L("op16", "OP", "Kramers--Kronig relations", r"\chi'(\omega)=\frac1\pi\,\mathrm{P}\!\!\int_{-\infty}^{\infty}\frac{\chi''(\omega')}{\omega'-\omega}\,d\omega'", [r"\chi=\chi'+i\chi''\text{ causal response}", r"\omega\in\mathbb R"], "R C CA", "JAC", red=True,
  note="The relation can be stated as a real Hilbert-transform pair; its standard justification is analyticity in the upper half-plane.")
L("op17", "OP", "Jones calculus", r"\mathbf E_{\mathrm{out}}=J\,\mathbf E_{\mathrm{in}},\quad \mathbf E\in\mathbb C^2,\ J\in M_2(\mathbb C)", [r"\mathbf E\in\mathbb C^2", r"J\in M_2(\mathbb C)"], "C Vc Lin", "BW", red=True)
L("op18", "OP", "Vacuum dispersion relation", r"\omega=c|\mathbf k|", [r"\mathbf k\in\mathbb R^3"], "R Vr", "JAC", par=["em10"])
L("op19", "OP", "Paraxial ray-transfer matrices", r"\binom{y_2}{\theta_2}=\begin{pmatrix}A&B\\C&D\end{pmatrix}\binom{y_1}{\theta_1},\quad AD-BC=\frac{n_1}{n_2}", [r"y_k,\theta_k\in\mathbb R", r"A,B,C,D\in\mathbb R"], "R Lin", "BW")
L("op20", "OP", "Rayleigh scattering", r"I\propto\lambda^{-4}", [r"\lambda\in\mathbb R_{>0}"], "R", "JAC")
L("op21", "OP", "Abbe diffraction limit", r"d=\frac{\lambda}{2n\sin\alpha}", [r"\lambda,n\in\mathbb R_{>0}", r"\alpha\in(0,\pi/2]"], "R Ck", "BW")
L("op22", "OP", "Bragg's law", r"2d\sin\theta=n\lambda,\quad n\in\mathbb N_{>0}", [r"n\in\mathbb N_{>0}", r"d,\lambda\in\mathbb R_{>0}"], "R N Ck", "BW")
L("op23", "OP", "Wiener--Khinchin theorem", r"S(\omega)=\int_{-\infty}^{\infty}\Gamma(\tau)\,e^{i\omega\tau}\,d\tau,\quad \Gamma(\tau)=\langle E^*(t)E(t+\tau)\rangle", [r"E\text{ stationary random process}", r"\tau,\omega\in\mathbb R"], "R C Prob Stoch Ck", "BW", red=True)
L("op24", "OP", "Paraxial wave equation", r"\nabla_\perp^2A+2ik\,\partial_zA=0", [r"A:\mathbb R^3\to\mathbb C", r"k\in\mathbb R_{>0}"], "R C E3 Ck", "BW", red=True, par=["op12"])
L("op25", "OP", "Gaussian beam width", r"w(z)=w_0\sqrt{1+(z/z_R)^2},\quad z_R=\frac{\pi w_0^2}{\lambda}", [r"z\in\mathbb R", r"w_0,\lambda\in\mathbb R_{>0}"], "R", "BW", par=["op24"])

# ---------------------------------------------------------------- Special relativity
L("sr1", "SR", "Lorentz transformation", r"t'=\gamma\Big(t-\frac{vx}{c^2}\Big),\quad x'=\gamma(x-vt),\quad \gamma=\big(1-v^2/c^2\big)^{-1/2}", [r"(t,x,y,z)\in\mathbb R^4", r"v\in(-c,c)"], "R Mink Poin", "JAC")
L("sr2", "SR", "Invariance of the interval", r"c^2\Delta t^2-|\Delta\mathbf x|^2=c^2\Delta t'^2-|\Delta\mathbf x'|^2", [r"\text{event pairs}", r"\text{inertial coordinates}"], "R Mink", "ROBB", nom="S",
  note="Robb's axiomatization in terms of the relation \\enquote{after} recovers Minkowski geometry up to a choice of unit.")
L("sr3", "SR", "Minkowski spacetime", r"(\mathbb R^4,\eta),\quad \eta=\mathrm{diag}(1,-1,-1,-1)", [r"\text{events}\in M"], "Mink", "ROBB", nom="S")
L("sr4", "SR", "Energy--momentum relation", r"E^2=(pc)^2+(mc^2)^2", [r"E,p\in\mathbb R_{\ge0}", r"m\in\mathbb R_{\ge0}"], "R", "JAC")
L("sr5", "SR", "Rest energy", r"E_0=mc^2", [r"m\in\mathbb R_{\ge0}"], "R", "JAC", par=["sr4"])
L("sr6", "SR", "Time dilation", r"\Delta t=\gamma\,\Delta\tau", [r"v\in(-c,c)"], "R", "JAC", par=["sr1"])
L("sr7", "SR", "Length contraction", r"L=L_0/\gamma", [r"L_0\in\mathbb R_{>0}"], "R", "JAC", par=["sr1"])
L("sr8", "SR", "Velocity addition", r"u=\frac{u'+v}{1+u'v/c^2}", [r"u',v\in(-c,c)"], "R", "JAC", par=["sr1"])
L("sr9", "SR", "Relativistic Doppler effect (receding source)", r"f_{\mathrm{obs}}=f_{\mathrm{src}}\sqrt{\frac{1-\beta}{1+\beta}}", [r"\beta\in[0,1)"], "R", "JAC", par=["sr1"])
L("sr10", "SR", "Conservation of four-momentum", r"\sum_{\mathrm{in}}p^\mu=\sum_{\mathrm{out}}p^\mu", [r"p^\mu\in\mathbb R^{1,3}", r"\text{finite sets of particles}"], "R Mink Fin", "JAC")
L("sr11", "SR", "Covariant equation of motion", r"\frac{dp^\mu}{d\tau}=qF^{\mu\nu}u_\nu", [r"x:\mathbb R\to\mathbb R^{1,3}", r"F\text{ field tensor}"], "R Mink Tens Ck", "JAC")
L("sr12", "SR", "Proper time", r"\tau=\int\sqrt{1-|\dot{\mathbf x}(t)|^2/c^2}\,dt", [r"\mathbf x:\mathbb R\to E^3\ (|\dot{\mathbf x}|<c)"], "R Ck", "JAC")
L("sr13", "SR", "Poincar\\'e invariance", r"\text{laws invariant under }x\mapsto\Lambda x+a,\ \Lambda\in O(1,3),\ a\in\mathbb R^{1,3}", [r"(\Lambda,a)\in\mathbb R^{1,3}\rtimes O(1,3)"], "R Mink Poin Lie", "WEI")
L("sr14", "SR", "Compton scattering", r"\lambda'-\lambda=\frac{h}{m_ec}(1-\cos\theta)", [r"\theta\in[0,\pi]"], "R Ck", "JAC", par=["sr10"])
L("sr15", "SR", "Relativistic momentum", r"\mathbf p=\gamma m\mathbf v", [r"\mathbf v\in\mathbb R^3,\ |\mathbf v|<c"], "R Vr", "JAC")
L("sr16", "SR", "Free-particle action", r"S=-mc^2\int d\tau", [r"\text{varied timelike worldlines}"], "R Mink Ck", "JAC", var=True)
L("sr17", "SR", "Reverse triangle inequality", r"\tau(u+v)\ge\tau(u)+\tau(v)\quad(u,v\text{ future timelike})", [r"u,v\in\mathbb R^{1,3}"], "R Mink", "MTW")
L("sr18", "SR", "Additivity of rapidity", r"\phi_{1\oplus2}=\phi_1+\phi_2,\quad \tanh\phi=v/c", [r"\phi_k\in\mathbb R"], "R Ck", "JAC", par=["sr8"])

# ---------------------------------------------------------------- General relativity
L("gr1", "GR", "Einstein field equations", r"G_{\mu\nu}+\Lambda g_{\mu\nu}=\frac{8\pi G}{c^4}T_{\mu\nu}", [M4, g, r"T\text{ symmetric tensor field}"], "R Man Lor Tens", "WAL")
L("gr2", "GR", "Geodesic equation", r"\frac{d^2x^\mu}{d\tau^2}+\Gamma^\mu_{\alpha\beta}\frac{dx^\alpha}{d\tau}\frac{dx^\beta}{d\tau}=0", [r"x:\mathbb R\to M", g], "R Man Lor Ck", "WAL")
L("gr3", "GR", "Levi-Civita connection", r"\Gamma^\lambda_{\mu\nu}=\tfrac12g^{\lambda\sigma}(\partial_\mu g_{\sigma\nu}+\partial_\nu g_{\sigma\mu}-\partial_\sigma g_{\mu\nu})", [g], "R Man Lor Tens", "WAL")
L("gr4", "GR", "Contracted Bianchi identity", r"\nabla_\mu G^{\mu\nu}=0", [g], "R Man Lor Tens", "WAL")
L("gr5", "GR", "Local conservation of energy--momentum", r"\nabla_\mu T^{\mu\nu}=0", [g, r"T\text{ tensor field}"], "R Man Lor Tens", "WAL", par=["gr1", "gr4"])
L("gr6", "GR", "Schwarzschild solution", r"ds^2=-\Big(1-\frac{r_s}{r}\Big)c^2dt^2+\Big(1-\frac{r_s}{r}\Big)^{-1}dr^2+r^2d\Omega^2,\quad r_s=\frac{2GM}{c^2}", [r"r>r_s", r"M\in\mathbb R_{>0}"], "R Man Lor", "WAL", par=["gr1"])
L("gr7", "GR", "FLRW metric", r"ds^2=-c^2dt^2+a(t)^2\Big[\frac{dr^2}{1-kr^2}+r^2d\Omega^2\Big]", [r"a:\mathbb R\to\mathbb R_{>0}", r"k\in\{-1,0,1\}"], "R Z Man Lor Ck", "WAL")
L("gr8", "GR", "Friedmann equation", r"\Big(\frac{\dot a}{a}\Big)^2=\frac{8\pi G}{3}\rho-\frac{kc^2}{a^2}+\frac{\Lambda c^2}{3}", [r"a,\rho:\mathbb R\to\mathbb R", r"k\in\{-1,0,1\}"], "R Z Ck", "WAL", par=["gr1", "gr7"])
L("gr9", "GR", "Gravitational redshift (static observers)", r"\nu_\infty=\nu_e\sqrt{1-r_s/r}", [r"r>r_s"], "R", "WAL", par=["gr6"])
L("gr10", "GR", "Perihelion advance per orbit", r"\Delta\varpi=\frac{6\pi GM}{c^2a(1-e^2)}", [r"a\in\mathbb R_{>0}", r"e\in[0,1)"], "R", "MTW", par=["gr6"])
L("gr11", "GR", "Deflection of light (weak field)", r"\delta=\frac{4GM}{c^2b}", [r"b\in\mathbb R_{>0}\ (\text{impact parameter})"], "R", "WAL", par=["gr6"])
L("gr12", "GR", "Linearized field equations (Lorenz gauge)", r"\Box\bar h_{\mu\nu}=-\frac{16\pi G}{c^4}T_{\mu\nu}", [r"\bar h\text{ symmetric tensor field on }\mathbb R^{1,3}"], "R Mink Tens Ck", "WAL", par=["gr1"])
L("gr13", "GR", "Einstein--Hilbert action", r"S=\frac{c^4}{16\pi G}\int R\sqrt{-g}\,d^4x", [r"g\text{ ranges over varied metrics}"], "R Man Lor Tens", "WAL", var=True)
L("gr14", "GR", "Quadrupole formula", r"P=\frac{G}{5c^5}\Big\langle\dddot Q_{ij}\dddot Q_{ij}\Big\rangle", [r"Q_{ij}\text{ traceless mass quadrupole}"], "R Lin Ck", "MTW", par=["gr12"])
L("gr15", "GR", "Raychaudhuri equation (timelike geodesics)", r"\frac{d\theta}{d\tau}=-\frac{\theta^2}{3}-\sigma_{ab}\sigma^{ab}+\omega_{ab}\omega^{ab}-R_{ab}u^au^b", [r"u\text{ geodesic congruence}"], "R Man Lor Tens", "WAL")
L("gr16", "GR", "Local flatness (normal coordinates)", r"g_{\mu\nu}(p)=\eta_{\mu\nu},\quad \partial_\lambda g_{\mu\nu}(p)=0", [r"p\in M"], "R Man Lor Mink", "WAL")
L("gr17", "GR", "Area theorem", r"\frac{dA}{dv}\ge0\quad(\text{null energy condition})", [r"A\text{ horizon cross-section area}"], "R Man Lor Ck", "WAL")
L("gr18", "GR", "Acceleration equation", r"\frac{\ddot a}{a}=-\frac{4\pi G}{3}\Big(\rho+\frac{3p}{c^2}\Big)+\frac{\Lambda c^2}{3}", [r"a,\rho,p:\mathbb R\to\mathbb R"], "R Ck", "WAL", par=["gr1", "gr7"])
L("gr19", "GR", "Riemann tensor", r"[\nabla_\mu,\nabla_\nu]V^\rho=R^\rho{}_{\sigma\mu\nu}V^\sigma", [r"V\text{ vector field}"], "R Man Lor Tens", "WAL")
L("gr20", "GR", "Geodesic deviation", r"\frac{D^2\xi^\alpha}{d\tau^2}+R^\alpha{}_{\beta\gamma\delta}u^\beta\xi^\gamma u^\delta=0", [r"\xi\text{ deviation vector}"], "R Man Lor Tens", "MTW")
L("gr21", "GR", "Hubble law (low redshift)", r"v=H_0d,\quad H=\dot a/a", [r"d\in\mathbb R_{>0}"], "R Ck", "WAL", par=["gr7"])

# ---------------------------------------------------------------- Non-relativistic quantum mechanics
L("qm1", "QM", "Schr\\\"odinger equation", r"i\hbar\frac{d}{dt}\psi(t)=\hat H\psi(t)", [t, r"\psi:\mathbb R\to\mathcal H", Hop], "R C Hil Op Ck", "SAK")
L("qm2", "QM", "Time-independent Schr\\\"odinger equation", r"\hat H\psi=E\psi", [psi, r"E\in\sigma(\hat H)\subseteq\mathbb R"], "R C Hil Op", "SAK", par=["qm1"])
L("qm3", "QM", "Born rule", r"\Pr(a\in\Delta)=\|\hat P_{\hat A}(\Delta)\psi\|^2", [psi + r",\ \|\psi\|=1", r"\Delta\subseteq\mathbb R\text{ Borel}", Aop], "R C Hil Op Prob", "SAK")
L("qm4", "QM", "Canonical commutation relation", r"[\hat x,\hat p]=i\hbar", [r"\hat x,\hat p\text{ self-adjoint on }L^2(\mathbb R)"], "C Hil Op L2", "SAK")
L("qm5", "QM", "Heisenberg uncertainty relation", r"\sigma_x\sigma_p\ge\hbar/2", [psi], "R C Hil Op", "SAK", par=["qm6"])
L("qm6", "QM", "Robertson inequality", r"\sigma_A\sigma_B\ge\tfrac12\big|\langle[\hat A,\hat B]\rangle\big|", [psi, r"\hat A,\hat B\text{ self-adjoint}"], "R C Hil Op", "SAK")
L("qm7", "QM", "Heisenberg equation of motion", r"\frac{d\hat A_H}{dt}=\frac{i}{\hbar}[\hat H,\hat A_H]+\Big(\frac{\partial\hat A}{\partial t}\Big)_H", [t, Aop], "R C Hil Op Ck", "SAK")
L("qm8", "QM", "Expectation values", r"\langle\hat A\rangle=\operatorname{Tr}(\rho\hat A)", [r"\rho\text{ density operator}", Aop], "R C Hil Op Tr", "VN")
L("qm9", "QM", "Von Neumann equation", r"i\hbar\frac{d\rho}{dt}=[\hat H,\rho]", [r"\rho:\mathbb R\to\mathcal T_1(\mathcal H)"], "R C Hil Op Tr Ck", "VN")
L("qm10", "QM", "Stone's theorem", r"U(t)=e^{-i\hat Ht/\hbar}\ \leftrightarrow\ \hat H\text{ self-adjoint}", [r"U:\mathbb R\to\mathcal U(\mathcal H)\text{ strongly continuous}"], "R C Hil Op Top", "RS")
L("qm11", "QM", "Hydrogen energy levels", r"E_n=-\frac{m_ee^4}{8\varepsilon_0^2h^2n^2},\quad n\in\mathbb N_{>0}", [r"n\in\mathbb N_{>0}"], "R N Hil Op L2", "SAK", par=["qm2"])
L("qm12", "QM", "Harmonic oscillator spectrum", r"E_n=\hbar\omega\big(n+\tfrac12\big),\quad n\in\mathbb N", [r"n\in\mathbb N"], "R N Hil Op L2", "SAK", par=["qm2"])
L("qm13", "QM", "Angular momentum spectrum", r"\hat L^2:\ \hbar^2\ell(\ell+1),\quad \hat L_z:\ \hbar m,\ m\in\{-\ell,\dots,\ell\}", [r"\ell\in\mathbb N", r"m\in\mathbb Z"], "R Z N Hil Op LieA", "SAK")
L("qm14", "QM", "Spin algebra", r"[\hat S_i,\hat S_j]=i\hbar\varepsilon_{ijk}\hat S_k;\quad \hat{\mathbf S}=\tfrac\hbar2\boldsymbol\sigma\ (\text{spin }\tfrac12)", [r"\hat S_i\text{ on }\mathbb C^{2s+1}"], "C Vc Lin LieA SUn Hil", "SAK")
L("qm15", "QM", "Symmetrization postulate", r"\psi(\dots,x_i,\dots,x_j,\dots)=\pm\psi(\dots,x_j,\dots,x_i,\dots)", [r"\psi\in\mathcal H^{\otimes n}", r"\pi\in S_n"], "C Hil Sn", "SAK")
L("qm16", "QM", "Composite systems", r"\mathcal H_{AB}=\mathcal H_A\otimes\mathcal H_B", [r"\mathcal H_A,\mathcal H_B\text{ Hilbert spaces}"], "C Hil", "SAK")
L("qm17", "QM", "L\\\"uders rule", r"\rho\mapsto\frac{\hat P\rho\hat P}{\operatorname{Tr}(\hat P\rho)}", [r"\hat P\text{ projection}", r"\rho\text{ density operator}"], "R C Hil Op Tr", "VN")
L("qm18", "QM", "Ehrenfest theorem", r"\frac{d}{dt}\langle\hat x\rangle=\frac{\langle\hat p\rangle}{m},\quad \frac{d}{dt}\langle\hat p\rangle=-\langle V'(\hat x)\rangle", [r"\psi:\mathbb R\to L^2(\mathbb R)"], "R C Hil Op L2 Ck", "SAK", par=["qm7"])
L("qm19", "QM", "Probability current", r"\partial_t|\psi|^2+\nabla\cdot\mathbf j=0,\quad \mathbf j=\frac{\hbar}{2mi}(\psi^*\nabla\psi-\psi\nabla\psi^*)", [r"\psi:\mathbb R^3\times\mathbb R\to\mathbb C"], "R C L2 Ck", "SAK", par=["qm36"])
L("qm20", "QM", "Momentum representation", r"\tilde\psi(p)=(2\pi\hbar)^{-1/2}\int e^{-ipx/\hbar}\psi(x)\,dx", [r"\psi\in L^2(\mathbb R)"], "R C L2 Four", "SAK")
L("qm21", "QM", "Spectral theorem", r"\hat A=\int_{\mathbb R}\lambda\,dE_{\hat A}(\lambda)", [Aop, r"E_{\hat A}\text{ projection-valued measure}"], "R C Hil Op Bor", "RS")
L("qm22", "QM", "Rayleigh--Schr\\\"odinger perturbation theory", r"E_n^{(1)}=\langle n|\hat V|n\rangle,\quad E_n^{(2)}=\sum_{m\ne n}\frac{|\langle m|\hat V|n\rangle|^2}{E_n-E_m}", [r"\{|n\rangle\}\text{ eigenbasis of }\hat H_0"], "R C Hil Op Seq", "SAK")
L("qm23", "QM", "Fermi's golden rule", r"\Gamma_{i\to f}=\frac{2\pi}{\hbar}|\langle f|\hat V|i\rangle|^2\rho(E_f)", [r"|i\rangle,|f\rangle\in\mathcal H"], "R C Hil Op", "SAK")
L("qm24", "QM", "WKB tunnelling", r"T\approx\exp\Big(-\frac2\hbar\int_{x_1}^{x_2}\sqrt{2m(V(x)-E)}\,dx\Big)", [r"V:\mathbb R\to\mathbb R", r"E\in\mathbb R"], "R Hil L2 Ck", "SAK")
L("qm25", "QM", "Bohr--Sommerfeld quantization (WKB)", r"\oint p\,dx=2\pi\hbar\big(n+\tfrac12\big)", [r"n\in\mathbb N"], "R N Hil Ck", "SAK")
L("qm26", "QM", "CHSH inequality and Tsirelson bound", r"|S|\le2\ (\text{local}),\quad |S|\le2\sqrt2\ (\text{quantum}),\ S=E(a,b)-E(a,b')+E(a',b)+E(a',b')",
  [r"a,a',b,b'\text{ settings}", r"E\text{ correlations}"], "R C Hil Op Prob", "CHSH")
L("qm27", "QM", "Aharonov--Bohm phase", r"\Delta\varphi=\frac{q}{\hbar}\oint\mathbf A\cdot d\mathbf l", [r"\mathbf A:E^3\to\mathbb R^3", r"\text{closed paths}"], "R C E3 Hil Ck", "SAK")
L("qm28", "QM", "Density operators", r"\rho\ge0,\quad \operatorname{Tr}\rho=1", [r"\rho\in\mathcal T_1(\mathcal H)"], "R C Hil Tr", "VN")
L("qm29", "QM", "Particle in a box", r"E_n=\frac{n^2\pi^2\hbar^2}{2mL^2},\quad n\in\mathbb N_{>0}", [r"n\in\mathbb N_{>0}"], "R N Hil Op L2", "SAK", par=["qm2"])
L("qm30", "QM", "Landau levels", r"E_n=\hbar\omega_c\big(n+\tfrac12\big),\quad \omega_c=|q|B/m", [r"n\in\mathbb N"], "R N Hil Op L2", "SAK", par=["qm2"])
L("qm31", "QM", "Anomalous Zeeman effect (weak field)", r"\Delta E=g_J\mu_Bm_JB", [r"m_J\in\{-J,\dots,J\}\subseteq\tfrac12\mathbb Z"], "R Q Hil Op", "SAK")
L("qm32", "QM", "Gleason's theorem", r"\dim\mathcal H\ge3:\ \mu(\hat P)=\operatorname{Tr}(\rho\hat P)\ \text{for every probability measure on projections}", [r"\mu:\mathcal P(\mathcal H)\to[0,1]"], "R C Hil Op Tr Prob", "GLE")
L("qm33", "QM", "Kochen--Specker theorem", r"\dim\mathcal H\ge3:\ \neg\exists v:\mathcal P\to\{0,1\}\ \text{noncontextual}", [r"\mathcal P\text{ finite set of projections}"], "C Hil Op Fin", "KS")
L("qm34", "QM", "No-cloning theorem", r"\neg\exists U\ \forall\psi:\ U(\psi\otimes e)=\psi\otimes\psi", [r"U\text{ unitary on }\mathcal H\otimes\mathcal H", psi], "C Hil Op", "WZ")
L("qm35", "QM", "Rydberg formula", r"\frac1\lambda=R_\infty\Big(\frac1{n_1^2}-\frac1{n_2^2}\Big),\quad n_2>n_1\ge1", [r"n_1,n_2\in\mathbb N_{>0}"], "R N Hil Op", "SAK", par=["qm11"])
L("qm36", "QM", "Position-space Schr\\\"odinger equation", r"i\hbar\,\partial_t\psi=-\frac{\hbar^2}{2m}\nabla^2\psi+V\psi", [r"\psi:\mathbb R\to L^2(\mathbb R^3)", r"V:\mathbb R^3\to\mathbb R"], "R C L2 Op Ck", "SAK", par=["qm1"])
L("qm37", "QM", "Pauli exclusion principle", r"\psi\in\Lambda^n\mathcal H\ \Rightarrow\ \text{no single-particle state is doubly occupied}", [r"\psi\in\mathcal H^{\otimes n}"], "C Hil Sn", "SAK", par=["qm15"])
L("qm38", "QM", "Reduced states", r"\rho_A=\operatorname{Tr}_B\rho_{AB}", [r"\rho_{AB}\in\mathcal T_1(\mathcal H_A\otimes\mathcal H_B)"], "R C Hil Tr", "VN")
L("qm39", "QM", "Variational principle", r"E_0\le\langle\psi|\hat H|\psi\rangle\quad(\|\psi\|=1)", [r"\psi\in\mathrm{Dom}(\hat H)"], "R C Hil Op", "SAK")
L("qm40", "QM", "Hellmann--Feynman theorem", r"\frac{dE_\lambda}{d\lambda}=\Big\langle\psi_\lambda\Big|\frac{\partial\hat H_\lambda}{\partial\lambda}\Big|\psi_\lambda\Big\rangle", [r"\lambda\in\mathbb R", r"\hat H_\lambda\text{ family}"], "R C Hil Op Ck", "SAK")
L("qm41", "QM", "Bloch's theorem", r"\psi_{\mathbf k}(\mathbf x+\mathbf R)=e^{i\mathbf k\cdot\mathbf R}\psi_{\mathbf k}(\mathbf x)", [r"\mathbf R\in\mathbb Z^3\text{-lattice}", r"\mathbf k\in\text{Brillouin zone}"], "R Z C L2 Op", "SAK")

# ---------------------------------------------------------------- Atomic and nuclear physics
L("an1", "AN", "Radioactive decay law", r"N(t)=N_0e^{-\lambda t},\quad t_{1/2}=\frac{\ln2}{\lambda}", [t, r"\lambda\in\mathbb R_{>0}", r"N(t)\text{ expected number of undecayed nuclei}"], "R Prob Ck", "KRANE",
  note="Each nucleus has a constant probability of decay per unit time; $N(t)$ is an expectation.")
L("an2", "AN", "Activity", r"\mathcal A=-\frac{dN}{dt}=\lambda N", [t, r"\lambda\in\mathbb R_{>0}"], "R Ck", "KRANE", par=["an1"])
L("an3", "AN", "Semi-empirical mass formula", r"B=a_VA-a_SA^{2/3}-a_C\frac{Z(Z-1)}{A^{1/3}}-a_A\frac{(A-2Z)^2}{A}+\delta(A,Z)", [r"A,Z\in\mathbb N", r"a_V,a_S,a_C,a_A\in\mathbb R_{>0}"], "R N Z", "KRANE")
L("an4", "AN", "Nuclear radius", r"R=r_0A^{1/3}", [r"A\in\mathbb N_{>0}", r"r_0\in\mathbb R_{>0}"], "R N", "KRANE")
L("an5", "AN", "Moseley's law ($K_\\alpha$ lines)", r"\nu=\tfrac34R_\infty c\,(Z-1)^2", [r"Z\in\mathbb N_{>1}"], "R N", "KRANE")
L("an6", "AN", "Rutherford cross section", r"\frac{d\sigma}{d\Omega}=\Big(\frac{Z_1Z_2e^2}{16\pi\varepsilon_0E}\Big)^2\frac{1}{\sin^4(\theta/2)}", [r"Z_1,Z_2\in\mathbb Z", r"E\in\mathbb R_{>0}", r"\theta\in(0,\pi]"], "R Z Ck", "GPS", par=["em1", "nm2"])
L("an7", "AN", "Breit--Wigner resonance", r"\sigma(E)\propto\frac{\Gamma^2/4}{(E-E_0)^2+\Gamma^2/4}", [r"E,E_0\in\mathbb R", r"\Gamma\in\mathbb R_{>0}"], "R", "KRANE", nom="Q")
L("an8", "AN", "Electric dipole selection rules", r"\Delta\ell=\pm1,\quad \Delta m\in\{0,\pm1\}", [r"\ell\in\mathbb N", r"m\in\mathbb Z"], "Z Hil Op", "SAK")
L("an9", "AN", "Fine structure of hydrogen", r"E_{nj}=E_n\Big[1+\frac{\alpha^2}{n^2}\Big(\frac{n}{j+\frac12}-\frac34\Big)\Big]", [r"n\in\mathbb N_{>0}", r"j\in\{\tfrac12,\dots,n-\tfrac12\}"], "R Q N Hil Op", "SAK", par=["qm11"])
L("an10", "AN", "Einstein coefficients", r"\frac{A_{21}}{B_{21}}=\frac{8\pi h\nu^3}{c^3},\quad g_1B_{12}=g_2B_{21}", [r"g_1,g_2\in\mathbb N_{>0}", r"\nu\in\mathbb R_{>0}"], "R N", "SAK", par=["sm14"])
L("an11", "AN", "Photoelectric equation", r"E_{k,\max}=h\nu-W", [r"\nu,W\in\mathbb R_{>0}"], "R", "SAK", nom="Q")
L("an12", "AN", "Planck--Einstein relation", r"E=h\nu", [r"\nu\in\mathbb R_{>0}"], "R", "SAK", nom="Q")
L("an13", "AN", "De Broglie relation", r"\lambda=\frac hp", [r"p\in\mathbb R_{>0}"], "R", "SAK", nom="Q")
L("an14", "AN", "Rabi formula", r"P_{1\to2}(t)=\frac{\Omega^2}{\Omega_R^2}\sin^2\Big(\frac{\Omega_Rt}{2}\Big),\quad \Omega_R=\sqrt{\Omega^2+\Delta^2}", [t, r"\Omega,\Delta\in\mathbb R"], "R C Hil Op Ck", "SAK", par=["qm1"])
L("an15", "AN", "Larmor precession", r"\omega_L=\gamma B", [r"\gamma\in\mathbb R", r"B\in\mathbb R_{\ge0}"], "R", "SAK")
L("an16", "AN", "Mean free path", r"\ell=\frac{1}{n\sigma}", [r"n,\sigma\in\mathbb R_{>0}"], "R", "KRANE")
L("an17", "AN", "Geiger--Nuttall law", r"\log_{10}t_{1/2}=a\frac{Z}{\sqrt{E_\alpha}}+b", [r"Z\in\mathbb N", r"E_\alpha\in\mathbb R_{>0}", r"a,b\in\mathbb R"], "R N", "KRANE")
L("an18", "AN", "$Q$-value of a reaction", r"Q=\Big(\sum_{\mathrm{initial}}m-\sum_{\mathrm{final}}m\Big)c^2", [r"\text{finite sets of nuclei}", r"m\in\mathbb R_{>0}"], "R Fin", "KRANE", par=["sr5"])
L("an19", "AN", "Nuclear binding energy", r"B=\big(Zm_p+(A-Z)m_n-M_{\mathrm{nuc}}\big)c^2", [r"A,Z\in\mathbb N", r"M_{\mathrm{nuc}}\in\mathbb R_{>0}"], "R N Z", "KRANE", par=["sr5"])
L("an20", "AN", "Isospin algebra", r"[\hat T_i,\hat T_j]=i\varepsilon_{ijk}\hat T_k,\quad \text{nucleon}=\text{isodoublet}", [r"\hat T_i\text{ on }\mathbb C^2\otimes\mathcal H"], "C Hil LieA SUn", "KRANE")

# ---------------------------------------------------------------- Condensed matter physics
L("ss1", "SS", "Drude conductivity", r"\sigma=\frac{ne^2\tau}{m}", [r"n,\tau,m\in\mathbb R_{>0}"], "R", "AM", par=["nm2", "em6"])
L("ss2", "SS", "Wiedemann--Franz law", r"\frac{\kappa}{\sigma T}=\frac{\pi^2}{3}\Big(\frac{k_B}{e}\Big)^2", [r"T\in\mathbb R_{>0}"], "R", "AM", par=["sm13"])
L("ss3", "SS", "Hall coefficient", r"R_H=\frac1{nq}", [r"n\in\mathbb R_{>0}", r"q\in\mathbb R\setminus\{0\}"], "R", "AM", par=["em6"])
L("ss4", "SS", "Bravais and reciprocal lattices", r"\Lambda=\Big\{\sum_in_i\mathbf a_i:n_i\in\mathbb Z\Big\},\quad \mathbf a_i\cdot\mathbf b_j=2\pi\delta_{ij}", [r"n_i\in\mathbb Z", r"\mathbf a_i,\mathbf b_j\in\mathbb R^3"], "R Z Vr Lin", "AM")
L("ss5", "SS", "Monatomic chain dispersion", r"\omega(k)=2\sqrt{K/m}\,\big|\sin(ka/2)\big|", [r"k\in(-\pi/a,\pi/a]", r"K,m,a\in\mathbb R_{>0}"], "R Ck", "AM", par=["nm2", "nm7"])
L("ss6", "SS", "Free-electron density of states", r"g(E)=\frac{V}{2\pi^2}\Big(\frac{2m}{\hbar^2}\Big)^{3/2}\sqrt E", [r"E\in\mathbb R_{\ge0}", r"V\in\mathbb R_{>0}"], "R", "AM", nom="Q")
L("ss7", "SS", "Josephson relations", r"I=I_c\sin\Delta\varphi,\quad \frac{d\Delta\varphi}{dt}=\frac{2eV}{\hbar}", [t, r"\Delta\varphi:\mathbb R\to\mathbb R"], "R Ck", "AM", nom="Q")
L("ss8", "SS", "Flux quantization", r"\Phi=n\frac{h}{2e},\quad n\in\mathbb Z", [r"n\in\mathbb Z"], "R Z", "AM", nom="Q")
L("ss9", "SS", "London equation", r"\nabla^2\mathbf B=\frac{\mathbf B}{\lambda_L^2},\quad \lambda_L^2=\frac{m}{\mu_0n_se^2}", [B3, r"n_s\in\mathbb R_{>0}"], "R E3 Ck", "AM")
L("ss10", "SS", "Curie law", r"\chi=\frac CT", [r"T\in\mathbb R_{>0}"], "R", "AM")
L("ss11", "SS", "Curie--Weiss law", r"\chi=\frac{C}{T-T_c}\quad(T>T_c)", [r"T,T_c\in\mathbb R_{>0}"], "R", "AM")
L("ss12", "SS", "Integer quantum Hall effect", r"\sigma_{xy}=\nu\frac{e^2}{h},\quad \nu\in\mathbb Z", [r"\nu\in\mathbb Z"], "R Z", "AM", nom="Q")
L("ss13", "SS", "Landau free energy", r"F(M,T)=F_0+a(T-T_c)M^2+bM^4\quad(a,b>0)", [r"M\in\mathbb R", r"T\in\mathbb R_{>0}"], "R", "HUA")
L("ss14", "SS", "Rushbrooke scaling relation", r"\alpha+2\beta+\gamma=2", [r"\alpha,\beta,\gamma\text{ critical exponents}"], "R Prob StS", "HUA")
L("ss15", "SS", "Critical point of the square-lattice Ising model", r"\sinh\frac{2J}{k_BT_c}=1", [r"J,T_c\in\mathbb R_{>0}"], "R Prob Fin", "HUA", par=["sm15"])
L("ss16", "SS", "Mermin--Wagner theorem", r"d\le2,\ T>0,\ \text{short range, continuous symmetry}\ \Rightarrow\ \text{no spontaneous order}", [r"d\in\mathbb N", r"\text{Gibbs states}"], "R N Prob Lie", "HUA")
L("ss17", "SS", "Dulong--Petit law", r"C_V=3Nk_B\quad(T\gg\Theta_D)", [r"N\in\mathbb N"], "R N", "AM", par=["sm8"])
L("ss18", "SS", "Effective mass tensor", r"\Big(\frac{1}{m^*}\Big)_{ij}=\frac1{\hbar^2}\frac{\partial^2E}{\partial k_i\partial k_j}", [r"E:\text{Brillouin zone}\to\mathbb R"], "R Lin Ck", "AM", nom="Q")
L("ss19", "SS", "Semiclassical electron dynamics", r"\hbar\dot{\mathbf k}=-e(\mathbf E+\mathbf v\times\mathbf B),\quad \mathbf v=\frac1\hbar\nabla_{\mathbf k}E", [r"\mathbf k:\mathbb R\to\text{Brillouin zone}", EB], "R E3 Ck", "AM", nom="Q")
L("ss20", "SS", "Kramers degeneracy", r"\Theta\hat H\Theta^{-1}=\hat H,\ \Theta^2=-1\ \Rightarrow\ \text{every eigenvalue is at least doubly degenerate}", [r"\Theta\text{ antiunitary}", Hop], "C Hil Op", "SAK")

# ---------------------------------------------------------------- QFT and the Standard Model
L("qf1", "QF", "Klein--Gordon equation", r"(\Box+m^2)\phi=0", [phiQ], "R Mink OVD Fock", "PS")
L("qf2", "QF", "Dirac equation", r"(i\gamma^\mu\partial_\mu-m)\psi=0", [r"\psi\text{ spinor field}"], "C Mink Cliff OVD", "PS")
L("qf3", "QF", "Clifford relation", r"\{\gamma^\mu,\gamma^\nu\}=2\eta^{\mu\nu}", [r"\gamma^\mu\in M_4(\mathbb C)"], "C Cliff Mink", "PS", nom="Q")
L("qf4", "QF", "Equal-time (anti)commutation relations", r"[\phi(t,\mathbf x),\pi(t,\mathbf y)]=i\delta^3(\mathbf x-\mathbf y),\quad \{\psi_a(t,\mathbf x),\psi_b^\dagger(t,\mathbf y)\}=\delta_{ab}\delta^3(\mathbf x-\mathbf y)", [phiQ], "C OVD Dist", "PS")
L("qf5", "QF", "Ladder operators", r"[a(\mathbf k),a^\dagger(\mathbf k')]\propto\delta^3(\mathbf k-\mathbf k')", [r"\mathbf k\in\mathbb R^3"], "C Fock Dist", "PS")
L("qf6", "QF", "Fock space", r"\mathcal F_\pm(\mathcal H)=\bigoplus_{n\ge0}\mathcal H^{\otimes n}_{\pm}", [r"n\in\mathbb N"], "N Hil Fock", "RS")
L("qf7", "QF", "QED Lagrangian", r"\mathcal L=\bar\psi(i\gamma^\mu D_\mu-m)\psi-\tfrac14F_{\mu\nu}F^{\mu\nu},\quad D_\mu=\partial_\mu+ieA_\mu", [r"\psi,A\text{ quantum fields}"], "R C Cliff OVD Bund", "PS")
L("qf8", "QF", "Yang--Mills field strength", r"F^a_{\mu\nu}=\partial_\mu A^a_\nu-\partial_\nu A^a_\mu+gf^{abc}A^b_\mu A^c_\nu", [r"A\text{ connection on a principal bundle}"], "R Bund LieA", "PS")
L("qf9", "QF", "Yang--Mills Lagrangian", r"\mathcal L=-\tfrac14F^a_{\mu\nu}F^{a\mu\nu}", [r"A\text{ ranges over varied connections}"], "R Bund LieA", "PS", var=True)
L("qf10", "QF", "Gauge group of the Standard Model", r"G_{\mathrm{SM}}=SU(3)_C\times SU(2)_L\times U(1)_Y", [r"g\in G_{\mathrm{SM}}"], "SUn Lie Bund", "WEI", nom="Q")
L("qf11", "QF", "Higgs potential", r"V(\Phi)=-\mu^2\Phi^\dagger\Phi+\lambda(\Phi^\dagger\Phi)^2,\quad v=\sqrt{\mu^2/\lambda}", [r"\Phi\in\mathbb C^2", r"\mu^2,\lambda\in\mathbb R_{>0}"], "R C Vc", "PS", nom="Q")
L("qf12", "QF", "Spin--statistics theorem", r"s\in\mathbb N\Rightarrow[\,\cdot,\cdot\,]\text{ at spacelike separation};\quad s\in\mathbb N+\tfrac12\Rightarrow\{\,\cdot,\cdot\,\}", [r"s\in\tfrac12\mathbb N"], "Q OVD Poin", "SW")
L("qf13", "QF", "CPT theorem", r"\Theta\phi(x)\Theta^{-1}=\eta\,\phi^\dagger(-x),\quad \Theta\text{ antiunitary}", [r"\text{Wightman fields}"], "C OVD Poin", "SW")
L("qf14", "QF", "Dyson series", r"S=T\exp\Big(-i\int d^4x\,\mathcal H_I(x)\Big)", [r"\mathcal H_I\text{ interaction density}"], "R C OVD Seq", "PS")
L("qf15", "QF", "LSZ reduction", r"\langle f|S|i\rangle=\text{residue of the poles at }p_k^2=m^2\text{ of }\widetilde{\langle\Omega|T\phi(x_1)\cdots\phi(x_n)|\Omega\rangle},\ \text{times }Z^{-n/2}", [r"x_k\in\mathbb R^{1,3}"], "C OVD Four", "PS")
L("qf16", "QF", "Unitarity and the optical theorem", r"S^\dagger S=\mathbf 1;\quad \operatorname{Im}f(0)=\frac{k}{4\pi}\sigma_{\mathrm{tot}}", [r"S\text{ on Fock space}"], "R C Fock Op", "WEI")
L("qf17", "QF", "Callan--Symanzik equation", r"\Big[\mu\frac{\partial}{\partial\mu}+\beta(g)\frac{\partial}{\partial g}+n\gamma(g)\Big]G^{(n)}=0", [r"\mu\in\mathbb R_{>0}", r"G^{(n)}\text{ Green functions}"], "R OVD Ck", "PS")
L("qf18", "QF", "One-loop QED beta function", r"\beta(e)=\frac{e^3}{12\pi^2}", [r"e\in\mathbb R_{>0}"], "R OVD", "PS", par=["qf17"])
L("qf19", "QF", "One-loop QCD beta function", r"\beta(g)=-\frac{g^3}{16\pi^2}\Big(11-\frac23n_f\Big)", [r"n_f\in\mathbb N"], "R N OVD", "PS", par=["qf17"])
L("qf20", "QF", "Wightman axioms", r"\phi:\mathcal S(\mathbb R^4)\to\text{operators},\ \text{Poincar\'e covariance, locality, spectrum condition, unique vacuum}", [phiQ], "C OVD Poin Hil", "SW")
L("qf21", "QF", "Feynman propagator", r"\tilde D_F(p)=\frac{i}{p^2-m^2+i\epsilon}", [r"p\in\mathbb R^{1,3}"], "C Dist Mink", "PS", nom="Q")
L("qf22", "QF", "Grassmann variables", r"\theta_i\theta_j=-\theta_j\theta_i,\quad \int d\theta\,\theta=1,\ \int d\theta=0", [r"\theta_i\text{ generators}"], "C Grass", "PS", nom="Q")
L("qf23", "QF", "Anomaly cancellation (one generation)", r"\sum_{\text{left-handed Weyl}}Y^3=0,\quad \sum_{\text{left-handed Weyl}}Y=0", [r"Y\in\mathbb Q\text{ hypercharges}", r"\text{finite multiplet list}"], "Q Fin", "WEI", nom="Q",
  note="As an arithmetical condition the law is a finite sum over $\\mathbb Q$; it is required for the consistency of the quantized gauge theory.")
L("qf24", "QF", "Gell-Mann--Nishijima relation", r"Q=T_3+\frac Y2", [r"Q,T_3,Y\in\mathbb Q"], "Q LieA", "WEI", nom="Q")
L("qf25", "QF", "Unitarity of the CKM matrix", r"V^\dagger V=\mathbf 1_3", [r"V\in U(3)"], "C Lin SUn", "PS", nom="Q")
L("qf26", "QF", "Two-flavour neutrino oscillation", r"P_{\alpha\to\beta}=\sin^22\theta\,\sin^2\Big(\frac{\Delta m^2L}{4E}\Big)\quad(\alpha\neq\beta)", [r"L,E\in\mathbb R_{>0}", r"\theta\in[0,\pi/2]"], "R C Hil Ck", "WEI")
L("qf27", "QF", "Tree-level gauge boson masses", r"m_W=m_Z\cos\theta_W", [r"\theta_W\in(0,\pi/2)"], "R Ck", "PS", nom="Q")
L("qf28", "QF", "Goldstone's theorem", r"G\to H\ \text{spontaneously}\ \Rightarrow\ \dim G-\dim H\ \text{massless scalars}", [r"G,H\text{ Lie groups}"], "N Lie OVD", "WEI")
L("qf29", "QF", "Wigner classification", r"\text{one-particle states}\leftrightarrow\text{unitary irreps of }\widetilde{\mathcal P},\ (m,s),\ m>0,\ s\in\tfrac12\mathbb N", [r"m\in\mathbb R_{\ge0}", r"s\in\tfrac12\mathbb N"], "R Q Poin Hil Op", "WEI")
L("qf30", "QF", "Baryon number conservation (perturbative)", r"\sum_{\mathrm{in}}B=\sum_{\mathrm{out}}B,\quad B(\text{quark})=\tfrac13", [r"B\in\tfrac13\mathbb Z"], "Q Fin", "WEI", nom="Q")
L("qf31", "QF", "Charge quantization", r"Q_u=+\tfrac23e,\ Q_d=-\tfrac13e;\quad Q_{\text{hadron}}\in e\mathbb Z", [r"Q/e\in\tfrac13\mathbb Z"], "Q Z", "WEI", nom="Q")
L("qf32", "QF", "Hawking temperature", r"T_H=\frac{\hbar c^3}{8\pi GMk_B}", [r"M\in\mathbb R_{>0}"], "R", "WAL", nom="Q",
  note="Derived in quantum field theory on curved spacetime; as stated it relates two real magnitudes.")
L("qf33", "QF", "Unruh temperature", r"T=\frac{\hbar a}{2\pi ck_B}", [r"a\in\mathbb R_{>0}"], "R", "WAL", nom="Q",
  note="Derived in quantum field theory; as stated it relates two real magnitudes.")
L("qf34", "QF", "Casimir pressure (parallel plates)", r"\frac FA=-\frac{\pi^2\hbar c}{240\,d^4}", [r"d\in\mathbb R_{>0}"], "R Seq", "PS", nom="Q")
L("qf35", "QF", "Schwinger term of the electron anomaly", r"a_e=\frac{\alpha}{2\pi}+O(\alpha^2)", [r"\alpha\in\mathbb R_{>0}"], "R OVD Seq", "PS")
L("qf36", "QF", "Two-body cross section (CM frame, equal masses)", r"\Big(\frac{d\sigma}{d\Omega}\Big)_{\mathrm{CM}}=\frac{|\mathcal M|^2}{64\pi^2E_{\mathrm{cm}}^2}", [r"\mathcal M\in\mathbb C"], "R C Fock Op", "PS")
L("qf37", "QF", "Electroweak couplings", r"e=g\sin\theta_W=g'\cos\theta_W", [r"g,g'\in\mathbb R_{>0}"], "R Ck", "PS", nom="Q")

# ====================================================================== computation
HERE = os.path.dirname(os.path.abspath(__file__))

QTRIG = {"Hil", "Op", "Tr", "L2", "Fock", "OVD", "Cliff", "Grass"}
PTRIG = {"StS", "Symp", "Prob", "Stoch"}
KSET = {"N", "Z", "Fin", "Sn"}
NOMINALIZED = {"O", "S", "F", "K"}
RESISTANT = {"V", "P", "Q"}
STATUS_ORDER = ["O", "S", "F", "K", "A", "V", "P", "Q"]
STATUS_GLOSS = {
    "O": "no mathematical structure quantified over",
    "S": "synthetic geometry suffices",
    "F": "nominalized in Field (1980)",
    "K": "counts only: numerically definite quantifiers",
    "A": "local field law: covered in principle, not carried out",
    "V": "variational: quantifies over varied histories",
    "P": "state space or probability: quantifies over possible states",
    "Q": "quantum: Hilbert-space formalism",
}
STATUS_SRC = {"O": "--", "S": "F80; Robb", "F": "F80", "K": "F80", "A": "F80, AD12", "V": "M82", "P": "M82",
              "Q": "B96; Bu03"}
RED = {"C": ["Rn", "Vr"], "CA": ["Ck"], "Vc": ["Vr"]}


def status(e):
    if e["nom"]:
        return e["nom"]
    Sx = set(e["S"])
    if not Sx:
        return "O"
    if Sx & QTRIG:
        return "Q"
    if e["var"]:
        return "V"
    if Sx & PTRIG:
        return "P"
    if Sx <= KSET:
        return "K"
    return "A"


def numbers_of(codes):
    cl = closure(codes)
    return [n for n in NUMBERS if n in cl]


def reduced(codes):
    out = []
    for x in codes:
        out.extend(RED.get(x, [x]))
    return sorted(set(out), key=ORDER.index)


def compute():
    check_acyclic()
    counters = {}
    for e in LAWS:
        for x in e["S"]:
            assert x in S, (e["key"], x)
        counters[e["th"]] = counters.get(e["th"], 0) + 1
        e["id"] = f"{e['th']}.{counters[e['th']]:02d}"
        e["status"] = status(e)
        e["clos"] = sort_codes(closure(e["S"]))
        e["dom"] = maxcard(e["S"])
        e["ccard"] = maxcard(e["clos"])
        e["nums"] = numbers_of(e["S"])
        e["minS"] = reduced(e["S"]) if e["red"] else list(e["S"])
        e["minnums"] = numbers_of(e["minS"])
        assert e["key"][:2].upper() == e["th"], e["key"]
        assert int(e["key"][2:]) == counters[e["th"]], ("key order", e["key"])
        if e["red"]:
            assert "C" in closure(e["S"]) and "C" not in closure(e["minS"]), e["key"]
    for e in LAWS:
        for p in e["par"]:
            assert p in KEYS, (e["key"], p)
    th_codes = [t[0] for t in THEORIES]
    assert set(th_codes) == {e["th"] for e in LAWS}
    return th_codes


# ====================================================================== formatting
NUMTEX = {"N": r"\mathbb N", "Z": r"\mathbb Z", "Q": r"\mathbb Q", "R": r"\mathbb R", "C": r"\mathbb C", "H": r"\mathbb H"}


def nums_tex(ns):
    return "$" + r"\,".join(NUMTEX[n] for n in ns) + "$" if ns else "none"


def codes_tex(cs):
    return ", ".join(S[c]["disp"] for c in cs) if cs else "none"


def lid(key):
    return KEYS[key]["id"]


def entry_tex(e):
    extra = sort_codes(set(e["clos"]) - set(e["S"]))
    lines = []
    lines.append(r"\begin{lawentry}{%s}{%s}{%s}" % (e["id"], e["name"], REFS[e["ref"]]))
    lines.append(r"\lawEq{%s}" % e["eq"])
    lines.append(r"\lawRow{Variables}{%s}" % ("; ".join("$" + v + "$" for v in e["vars"])))
    lines.append(r"\lawRow{Structures}{%s\quad\textit{closure adds:} %s}" % (codes_tex(e["S"]), codes_tex(extra)))
    st_ = e["status"]
    lines.append(r"\lawRow{Domain}{%s\quad\textit{closure:} %s\quad\textit{numbers:} %s\quad\textit{status:} \textbf{%s} (%s; %s)}"
                 % (CARD_TEX[e["dom"]], CARD_TEX[e["ccard"]], nums_tex(e["nums"]), st_, STATUS_GLOSS[st_], STATUS_SRC[st_]))
    tail = []
    if e["red"]:
        tail.append(r"\textit{reduction:} $\mathbb C\to\mathbb R^2$ with a complex structure; minimal numbers %s" % nums_tex(e["minnums"]))
    if e["par"]:
        tail.append(r"\textit{derived from:} " + ", ".join(lid(p) for p in e["par"]))
    if e["note"]:
        tail.append(e["note"])
    if tail:
        lines.append(r"\lawRow{Remarks}{%s}" % ".\\enspace ".join(tail).replace("..", "."))
    lines.append(r"\end{lawentry}")
    return "\n".join(lines)


def write(name, text):
    with open(os.path.join(HERE, name), "w", encoding="utf-8") as f:
        f.write(text if text.endswith("\n") else text + "\n")


def tab_a(th_codes):
    out = []
    for code, title, ref in THEORIES:
        es = [e for e in LAWS if e["th"] == code]
        cnt = {s: sum(1 for e in es if e["status"] == s) for s in STATUS_ORDER}
        nums = [n for n in NUMBERS if any(n in e["nums"] for e in es)]
        out.append(r"\subsection*{%s: %s}" % (code, title))
        out.append(r"\addcontentsline{toc}{subsection}{%s: %s}" % (code, title))
        out.append(r"{\footnotesize %d laws (%s--%s). Status counts: %s. Number systems committed to: %s. Principal reference: \citet{%s}.}\par\medskip"
                   % (len(es), es[0]["id"], es[-1]["id"],
                      ", ".join(f"{s} {cnt[s]}" for s in STATUS_ORDER if cnt[s]), nums_tex(nums), REFS[ref]))
        for e in es:
            out.append(entry_tex(e))
    write("tab_a.tex", "\n".join(out))


def ids_compact(es):
    return ", ".join(e["id"] for e in es) if es else "--"


def tab_b():
    out = []
    for c in ORDER:
        s = S[c]
        cl = sort_codes(closure([c]))
        direct = [e for e in LAWS if c in e["S"]]
        via = [e for e in LAWS if c in e["clos"] and c not in e["S"]]
        out.append(r"\begin{structentry}{%s}{%s}" % (s["disp"], s["name"]))
        out.append(r"\lawRow{Gloss}{%s}" % s["gloss"])
        out.append(r"\lawRow{Carrier}{%s\quad\textit{presupposes:} %s}" % (CARD_TEX[s["card"]], codes_tex(s["deps"])))
        out.append(r"\lawRow{Closure}{%s\quad (%d structures; cardinality %s; numbers %s)}"
                   % (codes_tex(sort_codes(set(cl) - {c})), len(cl), CARD_TEX[maxcard(cl)], nums_tex(numbers_of([c]))))
        out.append(r"\lawRow{Direct use}{%d laws: %s}" % (len(direct), ids_compact(direct)))
        out.append(r"\lawRow{Via closure}{%d further laws}" % len(via))
        out.append(r"\end{structentry}")
    write("tab_b.tex", "\n".join(out))


def tabular(colspec, header, rows, size=r"\footnotesize", long=False):
    env = "longtable" if long else "tabular"
    o = [r"{%s\setlength{\tabcolsep}{3pt}" % size]
    if not long:
        o.append(r"\begin{center}")
    o.append(r"\begin{%s}{%s}" % (env, colspec))
    o.append(r"\toprule")
    o.append(" & ".join(header) + r" \\")
    o.append(r"\midrule")
    if long:
        o.append(r"\endhead")
        o.append(r"\bottomrule\endfoot")
    for r in rows:
        o.append(" & ".join(str(x) for x in r) + r" \\")
    if not long:
        o.append(r"\bottomrule")
    o.append(r"\end{%s}" % env)
    if not long:
        o.append(r"\end{center}")
    o.append("}")
    return "\n".join(o)


def tab_c(th_codes):
    out = []
    # C1: theory x status
    rows = []
    for code in th_codes:
        es = [e for e in LAWS if e["th"] == code]
        r = [code, len(es)] + [sum(1 for e in es if e["status"] == s) or "." for s in STATUS_ORDER]
        r.append(sum(1 for e in es if e["status"] in RESISTANT))
        rows.append(r)
    tot = ["all", len(LAWS)] + [sum(1 for e in LAWS if e["status"] == s) for s in STATUS_ORDER] + [sum(1 for e in LAWS if e["status"] in RESISTANT)]
    rows.append([r"\textbf{%s}" % x for x in tot])
    out.append(r"\paragraph{Table C1. Nominalization status by theory.}")
    out.append(tabular("l r " + "r " * len(STATUS_ORDER) + "r", ["Th.", "Laws"] + STATUS_ORDER + ["V+P+Q"], rows))
    # C2: theory x number systems (standard / minimal)
    rows = []
    for code in th_codes:
        es = [e for e in LAWS if e["th"] == code]
        r = [code, len(es)]
        for n in NUMBERS:
            a = sum(1 for e in es if n in e["nums"])
            b = sum(1 for e in es if n in e["minnums"])
            r.append(f"{a}/{b}" if a != b else str(a))
        rows.append(r)
    r = ["all", len(LAWS)]
    for n in NUMBERS:
        a = sum(1 for e in LAWS if n in e["nums"])
        b = sum(1 for e in LAWS if n in e["minnums"])
        r.append(f"{a}/{b}" if a != b else str(a))
    rows.append([r"\textbf{%s}" % x for x in r])
    out.append(r"\paragraph{Table C2. Laws committing to each number system, by theory} (standard formulation / after the reduction $\mathbb C\to\mathbb R^2$ where admissible; one figure where the two agree).")
    out.append(tabular("l r " + "r " * len(NUMBERS), ["Th.", "Laws"] + ["$" + NUMTEX[n] + "$" for n in NUMBERS], rows))
    # C3: theory x cardinalities
    cards = ["none", "fin", "a0", "c", "2c"]
    rows = []
    for code in th_codes:
        es = [e for e in LAWS if e["th"] == code]
        rows.append([code] + [sum(1 for e in es if e["dom"] == k) or "." for k in cards] + [sum(1 for e in es if e["ccard"] == k) or "." for k in cards])
    rows.append([r"\textbf{all}"] + [r"\textbf{%d}" % sum(1 for e in LAWS if e["dom"] == k) for k in cards] + [r"\textbf{%d}" % sum(1 for e in LAWS if e["ccard"] == k) for k in cards])
    out.append(r"\paragraph{Table C3. Cardinality of the domain quantified over, by theory} (left: largest carrier among the structures the law quantifies over directly; right: largest carrier in the dependency closure).")
    out.append(tabular("l " + "r " * 10, ["Th."] + [CARD_TEX[k] for k in cards] + [CARD_TEX[k] for k in cards], rows))
    # C7: theories as wholes
    rows = []
    for code, title, _ in THEORIES:
        es = [e for e in LAWS if e["th"] == code]
        sts = {e["status"] for e in es}
        if sts <= NOMINALIZED:
            verdict = "nominalized"
        elif sts <= NOMINALIZED | {"A"}:
            verdict = "in principle"
        else:
            verdict = "resistant"
        un = [n for n in NUMBERS if any(n in e["nums"] for e in es)]
        um = [n for n in NUMBERS if any(n in e["minnums"] for e in es)]
        ur = [n for n in NUMBERS if any(n in e["minnums"] for e in es if e["status"] in RESISTANT)]
        rows.append([code, title, nums_tex(un), nums_tex(um), nums_tex(ur), verdict])
    out.append(r"\paragraph{Table C4. Theories as wholes.} Numbers committed to by some law of the theory (standard; minimal; minimal and carried by a law of status V, P or Q), and the verdict on the theory as a whole: \emph{nominalized} if every law has status O, S, F or K; \emph{in principle} if every law has one of these or A; \emph{resistant} otherwise.")
    out.append(tabular("l p{5.2cm} l l l l", ["Th.", "Theory", "Standard", "Minimal", "Resistant", "Verdict"], rows))
    # C5: structure x theory incidence
    rows = []
    for c in ORDER:
        r = [S[c]["disp"]]
        for code in th_codes:
            n = sum(1 for e in LAWS if e["th"] == code and c in e["S"])
            r.append(n or ".")
        r.append(sum(1 for e in LAWS if c in e["S"]))
        r.append(sum(1 for e in LAWS if c in e["clos"]))
        rows.append(r)
    out.append(r"\paragraph{Table C5. Direct use of each structure by theory} (last two columns: laws using the structure directly; laws whose closure contains it).")
    out.append(tabular("l " + "r " * len(th_codes) + "r r", ["Str."] + th_codes + ["dir.", "clos."], rows, size=r"\scriptsize", long=True))
    # C6: closure matrix
    rows = []
    for c in ORDER:
        cl = closure([c])
        rows.append([S[c]["disp"]] + [r"$\bullet$" if n in cl else "." for n in NUMBERS] + [len(cl), CARD_TEX[S[c]["card"]], CARD_TEX[maxcard(cl)]])
    out.append(r"\paragraph{Table C6. Dependency closure: number systems presupposed by each structure} (with the size of the closure, the carrier's cardinality and the largest cardinality in the closure).")
    out.append(tabular("l " + "c " * len(NUMBERS) + "r c c", ["Str."] + ["$" + NUMTEX[n] + "$" for n in NUMBERS] + ["$|\\mathrm{cl}|$", "carrier", "closure"], rows, size=r"\scriptsize", long=True))
    write("tab_c.tex", "\n".join(out))


def rel(a, b):
    a, b = set(a), set(b)
    if a == b:
        return "$=$"
    if a < b:
        return r"$\subset$"
    if a > b:
        return r"$\supset$"
    return "incomp."


def path_to(codes, target):
    """Shortest presupposition chain from a directly quantified structure to target (BFS)."""
    from collections import deque
    dq = deque([[c] for c in sort_codes(codes)])
    seen = set(codes)
    while dq:
        p = dq.popleft()
        if p[-1] == target:
            return p
        for y in S[p[-1]]["deps"]:
            if y not in seen:
                seen.add(y)
                dq.append(p + [y])
    return None


def path_tex(p):
    if p is None:
        return "--"
    return r"$\to$".join(S[c]["disp"] for c in p)


LONG = {}


def longest(c):
    """Longest presupposition chain from structure c down to a structure with no presuppositions."""
    if c not in LONG:
        best = [c]
        for y in S[c]["deps"]:
            p = [c] + longest(y)
            if len(p) > len(best) or (len(p) == len(best) and p > best):
                best = p
        LONG[c] = best
    return LONG[c]


def tops(codes):
    """Directly quantified structures not presupposed by another directly quantified structure."""
    return [c for c in sort_codes(codes) if not any(c in closure([d]) for d in codes if d != c)]


def tab_e():
    rows = []
    depth = []
    for e in LAWS:
        if e["S"]:
            ch = max((longest(c) for c in e["S"]), key=lambda p: (len(p), p))
            assert ch[-1] == "N"
            depth.append(len(ch) - 1)
            rows.append([e["id"], codes_tex(tops(e["S"])), path_tex(ch), len(ch) - 1, len(e["clos"])])
        else:
            depth.append(None)
            rows.append([e["id"], "none", "--", "--", 0])
    write("tab_e.tex", tabular("l p{4.6cm} p{7.4cm} r r", ["Law", "Top structures", "Longest presupposition chain", "Depth", "$|\\mathrm{cl}|$"], rows, size=r"\scriptsize", long=True))
    return depth


def tab_d(th_codes):
    out = []
    # D1: per number system, laws not committing (exceptions), by theory
    for n in NUMBERS:
        yes = [e for e in LAWS if n in e["nums"]]
        rows = []
        for code in th_codes:
            es = [e for e in LAWS if e["th"] == code]
            y = [e for e in es if n in e["nums"]]
            no = [e for e in es if n not in e["nums"]]
            if len(y) <= len(no):
                rows.append([code, len(y), "committing: " + ids_compact(y)])
            else:
                rows.append([code, len(y), "not committing: " + ids_compact(no)])
        out.append(r"\paragraph{Table D-$%s$.} %d of %d laws commit to $%s$ in their standard formulation; %d after admissible reduction."
                   % (NUMTEX[n], len(yes), len(LAWS), NUMTEX[n], sum(1 for e in LAWS if n in e["minnums"])))
        out.append(tabular("l r p{12.2cm}", ["Th.", "No.", "Laws (the shorter of the two lists)"], rows, size=r"\scriptsize", long=True))
    # D2: routes of C
    rows = []
    for e in LAWS:
        if "C" in e["nums"]:
            route = [x for x in e["S"] if "C" in closure([x])]
            rows.append([e["id"], codes_tex(route), e["status"], "yes" if e["red"] else "no", nums_tex(e["minnums"])])
    out.append(r"\paragraph{Table D-routes.} Every law committing to $\mathbb C$, with the directly quantified structures whose closure contains $\mathbb C$, its status, whether the reduction $\mathbb C\to\mathbb R^2$ is admissible, and the minimal numbers.")
    out.append(tabular("l p{6.8cm} c c l", ["Law", "Route to $\\mathbb C$", "St.", "Red.", "Minimal"], rows, size=r"\scriptsize", long=True))
    # D3: derivations
    rows = []
    for e in LAWS:
        if e["par"]:
            pn = sorted(set(n for p in e["par"] for n in KEYS[p]["nums"]), key=NUMBERS.index)
            ps = "".join(sorted({KEYS[p]["status"] for p in e["par"]}, key=STATUS_ORDER.index))
            rows.append([e["id"], ", ".join(lid(p) for p in e["par"]), nums_tex(e["nums"]), nums_tex(pn), rel(e["nums"], pn), e["status"], ps])
    out.append(r"\paragraph{Table D-derivations.} Laws standardly derived from others in the inventory: the law's numbers, the union of its sources' numbers and their relation, the law's status and its sources' statuses.")
    out.append(tabular("l l l l c c c", ["Law", "Sources", "Numbers", "Sources' numbers", "Rel.", "St.", "Src. st."], rows, size=r"\scriptsize", long=True))
    write("tab_d.tex", "\n".join(out))


def summary(th_codes):
    """Macros with computed figures for the prose; also verifies the claims made there."""
    d = {}
    n = len(LAWS)
    d["nLaws"] = n
    d["nTheories"] = len(THEORIES)
    d["nStructures"] = len(S)
    for s in STATUS_ORDER:
        d["nStat" + s] = sum(1 for e in LAWS if e["status"] == s)
    d["nResistant"] = sum(1 for e in LAWS if e["status"] in RESISTANT)
    d["nNominalized"] = sum(1 for e in LAWS if e["status"] in NOMINALIZED)
    names = {"N": "N", "Z": "Z", "Q": "Q", "R": "R", "C": "C", "H": "H"}
    for k in NUMBERS:
        d["nNum" + names[k]] = sum(1 for e in LAWS if k in e["nums"])
        d["nMin" + names[k]] = sum(1 for e in LAWS if k in e["minnums"])
        d["nRes" + names[k]] = sum(1 for e in LAWS if k in e["minnums"] and e["status"] in RESISTANT)
    d["nRed"] = sum(1 for e in LAWS if e["red"])
    d["nDomC"] = sum(1 for e in LAWS if e["dom"] == "c")
    d["nClosTwoC"] = sum(1 for e in LAWS if e["ccard"] == "2c")
    d["nDerived"] = sum(1 for e in LAWS if e["par"])
    d["nNoStruct"] = sum(1 for e in LAWS if not e["S"])
    # verified claims ------------------------------------------------------------
    nonempty = [e for e in LAWS if e["S"]]
    assert all("N" in e["nums"] for e in nonempty)                       # every law with structure commits to N
    assert {k for e in LAWS for k in e["nums"]} == {"N", "Z", "Q", "R", "C"}  # H unused
    assert {k for e in LAWS for k in e["minnums"]} == {"N", "Z", "Q", "R", "C"}
    for e in LAWS:                                                        # C after reduction only in quantum laws
        if "C" in e["minnums"]:
            assert e["status"] == "Q", e["id"]
    assert max(CARD_ORDER[e["dom"]] for e in LAWS) == CARD_ORDER["c"]     # no law quantifies directly over 2^c
    for e in LAWS:                                                        # 2^c closures arise only through L2
        if e["ccard"] == "2c":
            assert "Lmeas" in e["clos"] and ({"L2", "Four"} & set(e["clos"])), e["id"]
    for k in ["N", "Z", "Q", "R", "C"]:                                   # each number system carried by a resistant law
        assert any(k in e["minnums"] and e["status"] in RESISTANT for e in LAWS), k
    for e in LAWS:                                                        # laws without R
        if "R" not in e["nums"]:
            assert e["dom"] in ("none", "fin", "a0") or e["status"] == "Q" or e["status"] == "S", e["id"]
    assert {k for e in LAWS if e["status"] == "Q" for k in e["minnums"]} == {"N", "Z", "Q", "R", "C"}
    intro = [e["id"] for e in LAWS if e["par"] and set(e["nums"]) - {k for p in e["par"] for k in KEYS[p]["nums"]}]
    assert intro == ["OP.12"] and KEYS["op12"]["red"], intro
    big = sorted(ORDER, key=lambda c: -len(closure([c])))[:2]
    assert big == ["Four", "OVD"] and len(closure(["Four"])) == 20 and len(closure(["OVD"])) == 18
    d["listNoR"] = ", ".join(e["id"] for e in LAWS if "R" not in e["nums"])
    d["listTwoC"] = ", ".join(e["id"] for e in LAWS if e["ccard"] == "2c")
    d["listMinC"] = str(sum(1 for e in LAWS if "C" in e["minnums"]))
    d["listQnoC"] = ", ".join(e["id"] for e in LAWS if e["status"] == "Q" and "C" not in e["nums"])
    d["listRedC"] = ", ".join(e["id"] for e in LAWS if e["red"])
    d["listNominalized"] = ", ".join(e["id"] for e in LAWS if e["status"] in NOMINALIZED)
    d["listResQ"] = ", ".join(e["id"] for e in LAWS if "Q" in e["minnums"] and e["status"] in RESISTANT)
    resist_theories = []
    for code, title, _ in THEORIES:
        es = [e for e in LAWS if e["th"] == code]
        if any(e["status"] in RESISTANT for e in es):
            resist_theories.append(code)
    d["listResTheories"] = ", ".join(resist_theories)
    d["nResTheories"] = len(resist_theories)
    d["listInPrinciple"] = ", ".join(c for c, _, _ in THEORIES if c not in resist_theories)
    out = []
    for k, v in d.items():
        out.append(r"\newcommand{\%s}{%s}" % (k, v))
    write("summary.tex", "\n".join(out))
    return d


def main():
    th_codes = compute()
    tab_a(th_codes)
    tab_b()
    tab_c(th_codes)
    tab_d(th_codes)
    depth = tab_e()
    d = summary(th_codes)
    from collections import Counter
    cnt = Counter(x for x in depth if x is not None)
    d["depthDist"] = ", ".join(f"{n} of depth {l}" for l, n in sorted(cnt.items()))
    d["depthMax"] = max(cnt)
    d["depthMaxLaws"] = ", ".join(e["id"] for e, x in zip(LAWS, depth) if x == max(cnt))
    with open(os.path.join(HERE, "summary.tex"), "a", encoding="utf-8") as f:
        for k in ("depthDist", "depthMax", "depthMaxLaws"):
            f.write(r"\newcommand{\%s}{%s}" % (k, d[k]) + "\n")
    for k, v in d.items():
        print(f"{k:16s} {v}")


if __name__ == "__main__":
    main()
