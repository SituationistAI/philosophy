/-
SCI-19 · Self-Correction in Science
Formalization of Lemma 3.4, Theorem 3.5, Lemma 3.6, Theorem 3.7 and
Theorem 3.8.

A false finding enters the record with evidential weight `W`, measured in
units of one replication study. `R t` is the number of published
disconfirming replications by time `t`, each of weight `w`. The record is
corrected at `t` when the pooled weight of the replications reaches the
weight of the original evidence (Definition 3.1).

What this file establishes. If at least one replication is published in
every interval of length `k` (Assumption 3.2), the record is corrected by
time `n * k` for any `n` with `W ≤ w * n`: correction is certain. If at most
one is published per interval and none before the first (Assumption 3.3),
the record is not corrected at any time up to `n * k` whenever `w * n < W`:
correction is delayed by a time proportional to `k` and to `W / w`. It does
not establish the values of `k`, `w` and `W` in any actual field; these are
discussed in Section 4 of the manuscript. Theorem 3.8 applies the two
results to every field, given Assumptions 3.2 and 3.3 stated as axioms.
-/

namespace Philosophy.SCI_19

/-- Definition 3.1. The record is corrected at time `t`. -/
def Corrected (R : Nat → Nat) (w W t : Nat) : Prop := W ≤ w * R t

/-- Assumption 3.2 (Steady replication), as a hypothesis: at least one
replication in every interval of length `k`. -/
def Steady (R : Nat → Nat) (k : Nat) : Prop := ∀ t, R t + 1 ≤ R (t + k)

/-- Assumption 3.3 (Bounded replication), as a hypothesis: none at the start,
the count never decreases, and at most one in every interval of length `k`. -/
def Bounded (R : Nat → Nat) (k : Nat) : Prop :=
  R 0 = 0 ∧ (∀ a b, a ≤ b → R a ≤ R b) ∧ ∀ t, R (t + k) ≤ R t + 1

/-- Lemma 3.4. Under steady replication, at least `n` replications have
appeared by time `n * k`. -/
theorem steady_count (R : Nat → Nat) (k : Nat) (h : Steady R k) :
    ∀ n, n ≤ R (n * k) := by
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    rw [Nat.succ_mul]
    have := h (m * k)
    omega

/-- Theorem 3.5 (Eventual correction). Under steady replication the record is
corrected by time `n * k` whenever `W ≤ w * n`. -/
theorem eventual_correction (R : Nat → Nat) (k w W n : Nat) (h : Steady R k)
    (hn : W ≤ w * n) : Corrected R w W (n * k) := by
  unfold Corrected
  exact Nat.le_trans hn (Nat.mul_le_mul_left w (steady_count R k h n))

/-- Lemma 3.6. Under bounded replication, at most `n` replications have
appeared by any time up to `n * k`. -/
theorem bounded_count (R : Nat → Nat) (k : Nat) (h : Bounded R k) :
    ∀ n t, t ≤ n * k → R t ≤ n := by
  obtain ⟨h0, hmono, hstep⟩ := h
  have key : ∀ n, R (n * k) ≤ n := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ m ih =>
      rw [Nat.succ_mul]
      have := hstep (m * k)
      omega
  intro n t ht
  exact Nat.le_trans (hmono t (n * k) ht) (key n)

/-- Theorem 3.7 (Delay). Under bounded replication the record is not corrected
at any time up to `n * k` whenever `w * n < W`. -/
theorem delay (R : Nat → Nat) (k w W n : Nat) (h : Bounded R k)
    (hn : w * n < W) : ∀ t, t ≤ n * k → ¬ Corrected R w W t := by
  intro t ht hc
  unfold Corrected at hc
  have := Nat.mul_le_mul_left w (bounded_count R k h n t ht)
  omega

/-- Primitive: research fields. -/
axiom Field : Type
/-- Primitive: the count of published disconfirming replications of a given
false finding in a field, by time. -/
axiom replications : Field → Nat → Nat
/-- Primitive: the replication interval of a field. -/
axiom interval : Field → Nat

/-- Assumption 3.2 (Steady replication), as a premise about fields. -/
axiom steady_fields : ∀ f, Steady (replications f) (interval f)
/-- Assumption 3.3 (Bounded replication), as a premise about fields. -/
axiom bounded_fields : ∀ f, Bounded (replications f) (interval f)

/-- Theorem 3.8 (Self-correction, slowly). In every field, a false finding of
weight `W` is corrected by time `n * k` if `W ≤ w * n`, and not before time
`m * k` if `w * m < W`, where `k` is the field's replication interval. -/
theorem self_correcting_slowly (f : Field) (w W n m : Nat)
    (hn : W ≤ w * n) (hm : w * m < W) :
    Corrected (replications f) w W (n * interval f) ∧
    ∀ t, t ≤ m * interval f → ¬ Corrected (replications f) w W t :=
  ⟨eventual_correction _ _ w W n (steady_fields f) hn,
   delay _ _ w W m (bounded_fields f) hm⟩

end Philosophy.SCI_19

#print axioms Philosophy.SCI_19.eventual_correction
#print axioms Philosophy.SCI_19.delay
#print axioms Philosophy.SCI_19.self_correcting_slowly
