"""Finite second-order Kripke models for the Goedel--Scott--Anderson family of axioms.

A model is (n, R, m, Pi, c):
  worlds 0..n-1, accessibility R (list of successor bitmasks),
  constant domain 0..m-1,
  points (w,d) encoded as bit w*m+d; a property (intension) is a bitmask over points,
  Pi: the admissible properties, a Boolean algebra given by its atoms (a partition of the points),
  c: the core of positivity; P = {Y in Pi : Y contains c} (rigid).
Everything is computed by brute force.  Python 3 standard library only.
"""
import itertools


class Model:
    def __init__(self, n, succ, m, atoms, c):
        self.n, self.succ, self.m = n, succ, m
        self.atoms = atoms
        self.c = c
        self.full = (1 << (n * m)) - 1
        self.Pi = elements(atoms)
        self.Pset = set(self.Pi)

    # -- basic operations on intensions
    def pt(self, w, d):
        return 1 << (w * self.m + d)

    def has(self, Y, w, d):
        return (Y >> (w * self.m + d)) & 1 == 1

    def line(self, d, worlds):
        """the points (v,d) for v in the bitmask worlds"""
        r = 0
        for v in range(self.n):
            if (worlds >> v) & 1:
                r |= self.pt(v, d)
        return r

    def rows(self, worlds):
        r = 0
        for v in range(self.n):
            if (worlds >> v) & 1:
                for d in range(self.m):
                    r |= self.pt(v, d)
        return r

    def box(self, Y):
        """(box Y)(w,d) iff (v,d) in Y for all v with wRv"""
        r = 0
        for w in range(self.n):
            for d in range(self.m):
                L = self.line(d, self.succ[w])
                if Y & L == L:
                    r |= self.pt(w, d)
        return r

    def proj(self, Y):
        """(exists-projection Y)(w,d) iff (w,e) in Y for some e"""
        r = 0
        for w in range(self.n):
            if Y & self.rows(1 << w):
                r |= self.rows(1 << w)
        return r

    def P(self, Y):
        return Y & self.c == self.c

    # -- world-relative notions
    def nec_x(self, Y, w, d):
        """box Y(d) at w"""
        L = self.line(d, self.succ[w])
        return Y & L == L

    def entails(self, Y, Z, w):
        """box forall y (Y(y) -> Z(y)) at w"""
        S = self.rows(self.succ[w])
        return (Y & S) & ~Z == 0

    def nec_inst(self, Y, w):
        """box exists y Y(y) at w"""
        for v in range(self.n):
            if (self.succ[w] >> v) & 1 and not (Y & self.rows(1 << v)):
                return False
        return True

    def inst(self, Y, w):
        return (Y & self.rows(1 << w)) != 0

    def pos_inst(self, Y, w):
        return any((self.succ[w] >> v) & 1 and self.inst(Y, v) for v in range(self.n))

    # -- Anderson's definitions
    def G_A(self):
        """G(x) iff for all Y in Pi: P(Y) <-> box Y(x)"""
        r = 0
        for w in range(self.n):
            for d in range(self.m):
                if all(self.P(Y) == self.nec_x(Y, w, d) for Y in self.Pi):
                    r |= self.pt(w, d)
        return r

    def ess_A(self, Y, w, d):
        """Y is an A-essence of d at w: for all Z: box Z(d) <-> box forall y (Y y -> Z y)"""
        return all(self.nec_x(Z, w, d) == self.entails(Y, Z, w) for Z in self.Pi)

    def NE_A(self):
        r = 0
        for w in range(self.n):
            for d in range(self.m):
                if all(self.nec_inst(Y, w) for Y in self.Pi if self.ess_A(Y, w, d)):
                    r |= self.pt(w, d)
        return r

    # -- Scott's definitions
    def G_S(self):
        """G(x) iff for all Y: P(Y) -> Y(x)"""
        r = 0
        for w in range(self.n):
            for d in range(self.m):
                if all(self.has(Y, w, d) for Y in self.Pi if self.P(Y)):
                    r |= self.pt(w, d)
        return r

    def ess_S(self, Y, w, d):
        """Y(x) and for all Z: Z(x) -> box forall y (Y y -> Z y)"""
        if not self.has(Y, w, d):
            return False
        return all(self.entails(Y, Z, w) for Z in self.Pi if self.has(Z, w, d))

    def NE_S(self):
        r = 0
        for w in range(self.n):
            for d in range(self.m):
                if all(self.nec_inst(Y, w) for Y in self.Pi if self.ess_S(Y, w, d)):
                    r |= self.pt(w, d)
        return r

    # -- closure conditions on Pi (Henkin conditions)
    def closed(self):
        for Y in self.Pi:
            if self.box(Y) not in self.Pset or self.proj(Y) not in self.Pset:
                return False
        return True

    # -- the filter axioms F2 (closure under necessary entailment) at every world
    def F2(self):
        pos = [Y for Y in self.Pi if self.P(Y)]
        for w in range(self.n):
            for Y in pos:
                for Z in self.Pi:
                    if not self.P(Z) and self.entails(Y, Z, w):
                        return (w, Y, Z)
        return None

    def F2_ok(self):
        return self.F2() is None

    def ultra(self):
        return self.c in self.atoms


def elements(atoms):
    out = []
    k = len(atoms)
    for s in range(1 << k):
        Y = 0
        for i in range(k):
            if (s >> i) & 1:
                Y |= atoms[i]
        out.append(Y)
    return out


def partitions(items):
    """all set partitions of the list items"""
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in partitions(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]


def atoms_of_partition(p):
    return sorted(sum(1 << x for x in block) for block in p)
