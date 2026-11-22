/-
LOG-17 · Hempel's Ravens and Bayesian Confirmation
Formalization of Lemma 3.1, Proposition 3.2, Theorems 3.3 and 3.4 and
Corollary 3.5.

The model (Section 2 of the manuscript). The hypothesis H says that all
ravens are black; the alternative H_k says that exactly k ravens are not
black. The two hypotheses agree on the number of ravens, k + b, and on the
number of non-black things, k + a (Assumption 2.3). Under H_k there are
b black ravens and a non-black non-ravens. An observation is made by
drawing at random either a raven or a non-black thing.

Probabilities are rational numbers; a ratio p / q is represented by the
pair of natural numbers (p, q), and inequalities between ratios are
stated by cross-multiplication, so that the whole development is
arithmetic on natural numbers.

What this file establishes. Given the model, (i) evidence confirms H
against H_k exactly when it is more likely under H (Lemma 3.1); (ii) a
non-black non-raven drawn from the non-black things confirms H (Theorem
3.3); (iii) a black raven drawn from the ravens confirms H more, by the
likelihood-ratio measure, exactly when non-black non-ravens outnumber black
ravens (Theorem 3.4); (iv) the likelihood ratio for the non-black
non-raven exceeds 1 by at most 1/M when a ≥ M · k (Corollary 3.5).

What it does not establish. It does not establish the Bayesian account of
confirmation (Definition 2.1), the choice of the likelihood ratio as the
measure of degree of confirmation (Definition 2.2), or the sampling
assumption (Assumption 2.3); these are the manuscript's premises, and the
module only computes their consequences. It treats a single alternative
H_k; the extension to a mixture of alternatives is made in prose (Remark
3.6).
-/

namespace Philosophy.LOG_17

/-- Lemma 3.1 (Bayes's theorem for two hypotheses). With priors
proportional to `p` and `q` (both positive) and likelihoods proportional
to `x` (under H) and `y` (under H_k), the posterior of H, which is
`p * x / (p * x + q * y)`, exceeds its prior `p / (p + q)` iff `x > y`.
The inequality between the two ratios is stated by cross-multiplication. -/
theorem confirms_iff_likelier (p q x y : Nat) (hp : 0 < p) (hq : 0 < q) :
    p * (p * x + q * y) < p * x * (p + q) ↔ y < x := by
  have hpq : 0 < p * q := Nat.mul_pos hp hq
  have e1 : p * (p * x + q * y) = p * p * x + p * q * y := by
    rw [Nat.mul_add, Nat.mul_assoc, Nat.mul_assoc]
  have e2 : p * x * (p + q) = p * p * x + p * q * x := by
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [e1, e2]
  constructor
  · intro h
    exact (Nat.mul_lt_mul_left hpq).mp (Nat.lt_of_add_lt_add_left h)
  · intro h
    exact Nat.add_lt_add_left ((Nat.mul_lt_mul_left hpq).mpr h) _

/-- Proposition 3.2 (likelihoods in the sampling model). A raven drawn at
random is black with probability `(k + b) / (k + b)` under H and
`b / (k + b)` under H_k; a non-black thing drawn at random is a non-raven
with probability `(k + a) / (k + a)` under H and `a / (k + a)` under H_k.
We record the numerators over the common denominator. -/
def likelihoodH_raven (k b : Nat) : Nat := k + b
def likelihoodK_raven (_k b : Nat) : Nat := b
def likelihoodH_shoe (k a : Nat) : Nat := k + a
def likelihoodK_shoe (_k a : Nat) : Nat := a

/-- Theorem 3.3. If `k > 0`, a non-black non-raven drawn from the non-black
things is more likely under H than under H_k, and so (Lemma 3.1) confirms
H, whatever the positive priors. -/
theorem shoe_confirms (k a p q : Nat) (hk : 0 < k) (hp : 0 < p) (hq : 0 < q) :
    p * (p * likelihoodH_shoe k a + q * likelihoodK_shoe k a)
      < p * likelihoodH_shoe k a * (p + q) := by
  apply (confirms_iff_likelier p q _ _ hp hq).mpr
  simp only [likelihoodH_shoe, likelihoodK_shoe]
  omega

/-- Theorem 3.4. Let `k > 0`. The likelihood ratio of the black raven,
`(k + b) / b`, exceeds that of the non-black non-raven, `(k + a) / a`, iff
`b < a`. (The positivity of `a` and `b`, needed for the ratios to be
defined, is not needed for the cross-multiplied inequality.) -/
theorem raven_beats_shoe (k a b : Nat) (hk : 0 < k) :
    (k + a) * b < (k + b) * a ↔ b < a := by
  have e1 : (k + a) * b = k * b + a * b := Nat.add_mul k a b
  have e2 : (k + b) * a = k * a + a * b := by
    rw [Nat.add_mul, Nat.mul_comm b a]
  rw [e1, e2]
  constructor
  · intro h
    exact (Nat.mul_lt_mul_left hk).mp (Nat.lt_of_add_lt_add_right h)
  · intro h
    exact Nat.add_lt_add_right ((Nat.mul_lt_mul_left hk).mpr h) _

/-- Corollary 3.5 (negligibility). If the non-black non-ravens number at
least `M` times the non-black ravens posited by H_k, the likelihood ratio
of the non-black non-raven, `(k + a) / a`, is at most `(M + 1) / M`. -/
theorem shoe_negligible (k a M : Nat) (h : M * k ≤ a) :
    (k + a) * M ≤ a * (M + 1) := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_comm k M, Nat.mul_comm a M]
  omega

end Philosophy.LOG_17

#print axioms Philosophy.LOG_17.shoe_confirms
#print axioms Philosophy.LOG_17.raven_beats_shoe
