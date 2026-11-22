/-
LOG-01 · The Liar Resolved
Formalization of Propositions 3.4–3.5, Lemma 4.2, Theorems 4.1 and 4.3,
Proposition 4.6 and Propositions 5.1–5.3.

Truth values are those of the (k+1)-valued Łukasiewicz logic L_k,
represented by the natural numbers 0, …, k (0 is falsity, k is truth).
Negation is `k - x`; the conditional is `min k (k - x + y)`; conjunction is
`min`. Subtraction on natural numbers is truncated, which is exactly the
behaviour of the Łukasiewicz connectives on [0, k].

A sentence S that says of itself that it is not φ-true, where φ is an
operator interpreted by a function f on values, has an acceptable value
x exactly when `k - f x = x`.

What this file establishes. The ordinary liar has no classical value, has
the unique value k/2 when k is even, and the liar built from any finite
iteration of Field's determinateness operator D has a value strictly
between falsity and truth in a suitable L_k. An "exactly true" operator
would produce a liar with no value. It does not establish the full theory
with quantifiers and a truth predicate, whose consistency is discussed in
Section 8 of the manuscript.
-/

namespace Philosophy.LOG_01

/-- Definition 3.1. Łukasiewicz negation, conditional and conjunction on L_k. -/
def neg (k x : Nat) : Nat := k - x
def imp (k x y : Nat) : Nat := min k (k - x + y)
def conj (x y : Nat) : Nat := min x y

/-- Definition 3.3. Field's determinateness operator, D A := A ∧ ¬(A → ¬A). -/
def D (k x : Nat) : Nat := conj x (neg k (imp k x (neg k x)))

/-- D computed: on L_k, D x = max(0, 2x - k). -/
theorem D_eq (k x : Nat) (hx : x ≤ k) : D k x = 2 * x - k := by
  simp only [D, conj, neg, imp]
  omega

/-- Proposition 3.4. Classically (k = 1) the liar has no value. -/
theorem classical_liar (x : Nat) (hx : x ≤ 1) : neg 1 x ≠ x := by
  simp only [neg]; omega

/-- Theorem 4.1. In L_k the liar has a value iff 2x = k; for k = 2m the
unique value is m, which is neither 0 nor k when m > 0. -/
theorem liar_value (k x : Nat) (hx : x ≤ k) : neg k x = x ↔ 2 * x = k := by
  simp only [neg]; omega

/-- Proposition 3.5. In the strong Kleene case (k = 2) the liar's unique value is 1. -/
theorem kleene_liar (x : Nat) (hx : x ≤ 2) : neg 2 x = x ↔ x = 1 := by
  simp only [neg]; omega

/-- n-fold iteration of D. -/
def Diter (k : Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => D k (Diter k n x)

/-- Lemma 4.2. In L_k with k = 2^n + 1, iterating D m times on 2^n
(for m ≤ n) yields 2^n - 2^m + 1. -/
theorem iterate (n : Nat) : ∀ m, m ≤ n →
    Diter (2 ^ n + 1) m (2 ^ n) = 2 ^ n - 2 ^ m + 1 := by
  intro m
  induction m with
  | zero =>
    intro _
    have := @Nat.one_le_two_pow n
    simp only [Diter, Nat.pow_zero]
    omega
  | succ m ih =>
    intro hm
    have h1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
    have h2 : 2 ^ (m + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hm
    have h3 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    simp only [Diter]
    rw [ih (Nat.le_of_succ_le hm), D_eq _ _ (by omega)]
    omega

/-- Theorem 4.3. For every n, the D^n-liar (the sentence that says of itself
that it is not D^n-true) has the value 2^n in L_k with k = 2^n + 1: it is
neither true nor false. -/
theorem revenge_blocked (n : Nat) :
    neg (2 ^ n + 1) (Diter (2 ^ n + 1) n (2 ^ n)) = 2 ^ n ∧
    0 < 2 ^ n ∧ 2 ^ n < 2 ^ n + 1 := by
  refine ⟨?_, Nat.two_pow_pos n, Nat.lt_succ_self _⟩
  rw [iterate n n (Nat.le_refl n)]
  have := Nat.two_pow_pos n
  simp only [neg, Nat.sub_self, Nat.zero_add]
  omega

/-- Definition 4.5. The "exactly true" operator: value k on truth, 0 elsewhere. -/
def E (k x : Nat) : Nat := if x = k then k else 0

/-- Proposition 4.6. The liar built from E has no value. Hence E is not
definable in a language that has a liar for each of its operators. -/
theorem exact_truth_revenge (k : Nat) (hk : 0 < k) (x : Nat) : neg k (E k x) ≠ x := by
  simp only [neg, E]
  split <;> omega

/-- Proposition 5.1. The truth-teller, which says of itself that it is true,
accepts every value: its defect is underdetermination, not paradox. -/
theorem truth_teller (k x : Nat) (hx : x ≤ k) : x = x ∧ x ≤ k := ⟨rfl, hx⟩

/-- Proposition 5.2. Curry's sentence C, equivalent to C → ⊥, has an
acceptable value iff 2x = k, the same condition as the liar. -/
theorem curry_value (k x : Nat) (hx : x ≤ k) : imp k x 0 = x ↔ 2 * x = k := by
  simp only [imp]; omega

/-- Proposition 5.3. In the Nixon–Dean pair (each says that what the other
says is not true), a pair of values (x, y) is acceptable iff x + y = k. -/
theorem nixon_dean (k x y : Nat) (hx : x ≤ k) (hy : y ≤ k) :
    (neg k y = x ∧ neg k x = y) ↔ x + y = k := by
  simp only [neg]; omega

end Philosophy.LOG_01

#print axioms Philosophy.LOG_01.revenge_blocked
#print axioms Philosophy.LOG_01.exact_truth_revenge
