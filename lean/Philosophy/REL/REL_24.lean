/-
REL-24 · On the Evidential Irrelevance of the Present Collection
Formalization of Theorem 1.2.

Odds are represented by pairs of natural-number weights: prior odds `a : b`
on G against not-G, and likelihoods `lG` and `lN` of the evidence E under G
and under not-G. Posterior odds are `a * lG : b * lN`.

What this file establishes. If the likelihoods are equal (Proposition 1.1),
the posterior odds are proportional to the prior odds. It does not establish
Proposition 1.1, which is argued in the manuscript.
-/

namespace Philosophy.REL_24

/-- Theorem 1.2. Equal likelihoods leave the odds unchanged: the posterior
odds `a * l : b * l` and the prior odds `a : b` are the same ratio. -/
theorem odds_unchanged (a b lG lN : Nat) (equal : lG = lN) :
    (a * lG) * b = (b * lN) * a := by
  subst equal
  rw [Nat.mul_comm a lG, Nat.mul_comm b lG, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm a b]

end Philosophy.REL_24

#print axioms Philosophy.REL_24.odds_unchanged
