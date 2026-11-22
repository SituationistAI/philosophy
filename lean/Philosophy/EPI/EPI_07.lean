/-
EPI-07 · Moderate Conciliationism
Formalization of Theorem 3.2, Propositions 3.3 and 3.4 and Corollary 3.5.

Credences are integers on a fixed scale. The weight given to the first-order
evidence is the fraction `k / n`. To keep all quantities integral, every
credence after disclosure is represented multiplied by `2 * n`: the rational
credence `r = (k/n) f + (1 - k/n) (a + b)/2` is represented by
`2 k f + (n - k)(a + b)`, and the output of the moderate policy for a party
whose own credence is `a` and whose peer's is `b` by `2 k a + (n - k)(a + b)`.

What this file establishes. Given the combination principle (Principle P3)
and that both weights are positive (Principles P1 and P2), the policy
conciliates and gives additional weight to one's own credence (Theorem 3.2);
its output coincides with the rational credence exactly for the party whose
credence is the one the first-order evidence supports (Proposition 3.3), so it
does so for at most one party (Corollary 3.5); and the rational credence
depends on what the first-order evidence supports (Proposition 3.4).

What it does not establish. The three principles, or the value of the weight.
-/

namespace Philosophy.EPI_07

/-- The weight on the first-order evidence is `k / n` (Definition 2.4). -/
axiom n : Int
axiom k : Int

/-- Principle P1 (higher-order evidence counts): `k / n < 1`. -/
axiom higher_order_counts : k < n

/-- Principle P2 (first-order evidence is not screened off): `0 < k / n`. -/
axiom first_order_counts : 0 < k

/-- `RationalAfter f a b x`: on the shared evidence after disclosure, where the
first-order evidence supports `f` and the parties' credences are `a` and `b`,
the credence represented by `x` (scaled by `2 n`) is rational. -/
axiom RationalAfter : Int → Int → Int → Int → Prop

/-- Principle P3 (combination). The rational credence after disclosure is the
weighted average of what the first-order evidence supports and the midpoint of
the two credences. -/
axiom combination :
  ∀ f a b x, RationalAfter f a b x ↔ x = 2 * k * f + (n - k) * (a + b)

/-- Definition 3.1 (the moderate policy), scaled by `2 n`. -/
noncomputable def policy (own peer : Int) : Int := 2 * k * own + (n - k) * (own + peer)

theorem policy_minus_own (a b : Int) :
    policy a b - 2 * n * a = (n - k) * (b - a) := by
  unfold policy
  simp only [Int.mul_sub, Int.sub_mul, Int.mul_add, Int.add_mul, Int.mul_assoc]
  omega

theorem peer_minus_policy (a b : Int) :
    2 * n * b - policy a b = (n + k) * (b - a) := by
  unfold policy
  simp only [Int.mul_sub, Int.sub_mul, Int.mul_add, Int.add_mul, Int.mul_assoc]
  omega

/-- Theorem 3.2. If `a < b`, the policy moves strictly toward the peer
(conciliation) and ends strictly closer to one's own credence than to the
peer's (additional weight). The case `b < a` is symmetric. -/
theorem moderate (a b : Int) (h : a < b) :
    2 * n * a < policy a b ∧ policy a b < 2 * n * b ∧
    policy a b - 2 * n * a < 2 * n * b - policy a b := by
  have h1 : 0 < (n - k) * (b - a) :=
    Int.mul_pos (by have := higher_order_counts; omega) (by omega)
  have h2 : 0 < (n + k) * (b - a) :=
    Int.mul_pos (by have := higher_order_counts; have := first_order_counts; omega) (by omega)
  have h3 : (n - k) * (b - a) < (n + k) * (b - a) :=
    Int.mul_lt_mul_of_pos_right (by have := first_order_counts; omega) (by omega)
  have e1 := policy_minus_own a b
  have e2 := peer_minus_policy a b
  omega

theorem policy_minus_rational (f a b : Int) :
    policy a b - (2 * k * f + (n - k) * (a + b)) = (2 * k) * (a - f) := by
  unfold policy
  simp only [Int.mul_sub, Int.sub_mul, Int.mul_add, Int.add_mul, Int.mul_assoc]
  omega

/-- Proposition 3.3. The policy yields the rational credence iff one's own
credence is the one the first-order evidence supports. -/
theorem policy_rational_iff (f a b : Int) :
    RationalAfter f a b (policy a b) ↔ a = f := by
  rw [combination]
  have e := policy_minus_rational f a b
  have hk := first_order_counts
  constructor
  · intro h
    have h0 : (2 * k) * (a - f) = (2 * k) * 0 := by omega
    have := Int.eq_of_mul_eq_mul_left (by omega) h0
    omega
  · intro h
    subst h
    simp only [Int.sub_self, Int.mul_zero] at e
    omega

/-- Proposition 3.4. The rational credence depends on what the first-order
evidence supports. -/
theorem first_order_matters (f f' a b x : Int) (hne : f ≠ f')
    (h : RationalAfter f a b x) : ¬ RationalAfter f' a b x := by
  intro h'
  rw [combination] at h h'
  have hk := first_order_counts
  have h0 : (2 * k) * f = (2 * k) * f' := by
    simp only [Int.mul_assoc] at h h' ⊢
    omega
  exact hne (Int.eq_of_mul_eq_mul_left (by omega) h0)

/-- Corollary 3.5. In a disagreement (`a ≠ b`), the policy yields the rational
credence for at most one party. -/
theorem at_most_one (f a b : Int) (hne : a ≠ b) :
    ¬ (RationalAfter f a b (policy a b) ∧ RationalAfter f a b (policy b a)) := by
  intro ⟨hA, hB⟩
  have ha := (policy_rational_iff f a b).mp hA
  have hB' : RationalAfter f b a (policy b a) := by
    rw [combination] at hB ⊢
    rw [hB, Int.add_comm a b]
  have hb := (policy_rational_iff f b a).mp hB'
  exact hne (ha.trans hb.symm)

end Philosophy.EPI_07

#print axioms Philosophy.EPI_07.moderate
#print axioms Philosophy.EPI_07.policy_rational_iff
#print axioms Philosophy.EPI_07.at_most_one
