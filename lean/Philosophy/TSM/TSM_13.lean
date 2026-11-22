/-
TSM-13 · Zeno's Achilles and Convergent Series
Formalization of the arithmetic content of equation (1) and of the bound in
Theorem 1.1 (revised version of 7 October 2026).

Writing G n = 1 + 10 + ... + 10^(n-1), the partial sum of the first n
catch-up distances is S n = d * G n / 10^(n-1). The closed form of equation
(1) is equivalent to 9 * G n + 1 = 10^n, and the bound S n < 10d/9 to
9 * G n < 10^n. The index error corrected in the revision concerned the
relation between n and the exponent; here it is fixed by the definition of G.

What this file establishes. The closed form and the bound, for every n. It
does not establish convergence, which requires real analysis.
-/

namespace Philosophy.TSM_13

/-- G n = 1 + 10 + ... + 10^(n-1). -/
def geom : Nat → Nat
  | 0 => 0
  | n + 1 => geom n + 10 ^ n

/-- Equation (1), integer form: 9 * G n + 1 = 10^n. -/
theorem repunit (n : Nat) : 9 * geom n + 1 = 10 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [geom, Nat.pow_succ]
    omega

/-- Theorem 1.1, bound: every partial sum stays below the limit. -/
theorem below_limit (n : Nat) : 9 * geom n < 10 ^ n := by
  have := repunit n
  omega

/-- The partial sums are increasing. -/
theorem increasing (n : Nat) : geom n < geom (n + 1) := by
  simp only [geom]
  have : 0 < 10 ^ n := Nat.pos_pow_of_pos n (by decide)
  omega

end Philosophy.TSM_13

#print axioms Philosophy.TSM_13.repunit
