/-
MTE-16 · Expected Choiceworthiness, Variance-Normalized
Formalization of Proposition 3.2, Theorem 3.3 and Proposition 4.1 (revised
version of 7 October 2026).

In a choice between two options, a theory's variance-normalized
choiceworthiness takes the values +1 and -1 on the option it prefers and
the other, or is undefined if the theory is indifferent (Section 3). The
normalized expected choiceworthiness of the first option over the second is
therefore the credence-weighted sum of the signs of the theories'
preferences. Theories are represented by triples (credence, value of option
1, value of option 2) with integer entries.

What this file establishes. Indifferent theories, which the revision excludes
from variance normalization, make no difference to the verdict; and a theory
with greater credence outvotes a theory with smaller credence when they
disagree. It does not establish that variance normalization is the right
method of intertheoretic comparison.
-/

namespace Philosophy.MTE_16

/-- The sign of an integer. -/
def sgn (z : Int) : Int := if z > 0 then 1 else if z < 0 then -1 else 0

/-- A theory: credence, choiceworthiness of option 1, of option 2. -/
abbrev Theory := Int × Int × Int

/-- Contribution of a theory to the normalized comparison of option 1 with
option 2 (Theorem 3.3). -/
def vote (t : Theory) : Int := t.1 * sgn (t.2.1 - t.2.2)

/-- Normalized expected choiceworthiness of option 1 over option 2. -/
def score : List Theory → Int
  | [] => 0
  | t :: ts => vote t + score ts

/-- Proposition 3.2. Adding an indifferent theory does not change the score. -/
theorem indifferent_irrelevant (ts : List Theory) (c x : Int) :
    score ((c, x, x) :: ts) = score ts := by
  simp [score, vote, sgn]

/-- Proposition 4.1. With two theories that disagree, the one with greater
credence determines the verdict. -/
theorem outvote (c1 c2 x1 y1 x2 y2 : Int)
    (hc : c1 > c2) (h1 : x1 > y1) (h2 : x2 < y2) :
    score [(c1, x1, y1), (c2, x2, y2)] > 0 := by
  have a1 : x1 - y1 > 0 := by omega
  have a2 : ¬ (x2 - y2 > 0) := by omega
  have a3 : x2 - y2 < 0 := by omega
  simp [score, vote, sgn, a1, a2, a3]
  omega

end Philosophy.MTE_16

#print axioms Philosophy.MTE_16.indifferent_irrelevant
#print axioms Philosophy.MTE_16.outvote
