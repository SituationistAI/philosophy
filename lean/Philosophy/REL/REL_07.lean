/-
REL-07 · Hume's Maxim Quantified
Formalization of Theorem 2.4 (revised version of 7 October 2026).

Prior odds on the miracle are represented by natural numbers `a : b` with
`a ≥ 1`, and the per-witness likelihood ratio r/s by a natural number `L ≥ 2`.
By Proposition 2.3, which relies on conditional independence (Assumption 2.1,
as corrected in the revision), the posterior odds after n testimonies are
`a * L^n : b`.

What this file establishes. For any such prior odds, some finite number of
testimonies makes the posterior odds favourable. It does not establish that
actual testimonies satisfy conditional independence, which is discussed in
Section 4 of the manuscript.
-/

namespace Philosophy.REL_07

/-- n < 2^n. -/
theorem lt_two_pow' (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

/-- Theorem 2.4. Enough conditionally independent witnesses establish the
miracle, whatever the (non-zero) prior odds. -/
theorem enough_witnesses (a b L : Nat) (ha : 1 ≤ a) (hL : 2 ≤ L) :
    ∃ n, a * L ^ n > b := by
  refine ⟨b, ?_⟩
  have h1 : b < 2 ^ b := lt_two_pow' b
  have h2 : 2 ^ b ≤ L ^ b := Nat.pow_le_pow_left hL b
  have h3 : L ^ b ≤ a * L ^ b := Nat.le_mul_of_pos_left _ ha
  omega

end Philosophy.REL_07

#print axioms Philosophy.REL_07.enough_witnesses
