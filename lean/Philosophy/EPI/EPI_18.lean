/-
EPI-18 · Sleeping Beauty: The Thirder Solution
Formalization of Theorem 3.3 (revised version of 7 October 2026).

Credences in the three centred situations H1 (heads, Monday), T1 (tails,
Monday) and T2 (tails, Tuesday) are represented by natural-number weights
proportional to them, so that normalization is expressed without real
arithmetic: the credence in H1 is one third exactly when 3 * h1 equals the
total weight.

What this file establishes. The thirder answer follows from Lemma 3.1
(h1 = t1) and Lemma 3.2 (t1 = t2). It does not establish the lemmas, which
rest on the restricted Principal Principle and on restricted indifference,
and which hold only under the standard protocol (Assumption 2.1).
-/

namespace Philosophy.EPI_18

/-- Theorem 3.3. Given Lemmas 3.1 and 3.2, the credence in heads is 1/3. -/
theorem thirder (h1 t1 t2 : Nat)
    (monday : h1 = t1) (indifference : t1 = t2) :
    3 * h1 = h1 + t1 + t2 := by
  omega

/-- Proposition 4.1 (arithmetic part). Halfer weights h1 = 2, t1 = t2 = 1
give a credence in heads, conditional on Monday, of 2/3: 3 * h1 = 2 * (h1 + t1). -/
theorem halfer_conditional : 3 * 2 = 2 * (2 + 1) := by
  decide

/-- Sum of the tails weights t 0, ..., t (n-1). -/
def tailsTotal (t : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => tailsTotal t k + t k

/-- Theorem 6.1. With one heads waking and n tails wakings, Lemma 3.1 and
indifference among tails wakings give credence 1/(n+1) in heads. -/
theorem general (n h : Nat) (t : Nat → Nat)
    (monday : h = t 0) (indifference : ∀ i, i < n → t i = t 0) :
    (n + 1) * h = h + tailsTotal t n := by
  have key : ∀ k, k ≤ n → tailsTotal t k = k * t 0 := by
    intro k
    induction k with
    | zero => intro _; simp [tailsTotal]
    | succ k ih =>
      intro hk
      simp only [tailsTotal]
      rw [ih (Nat.le_of_succ_le hk), indifference k (Nat.lt_of_succ_le hk)]
      rw [Nat.succ_mul]
  rw [key n (Nat.le_refl n), ← monday, Nat.succ_mul, Nat.add_comm]

end Philosophy.EPI_18

#print axioms Philosophy.EPI_18.thirder
#print axioms Philosophy.EPI_18.general
