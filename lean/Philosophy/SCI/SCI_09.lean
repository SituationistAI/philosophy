/-
SCI-09 · The Everett Interpretation Defended
Formalization of Lemma 5.3, Lemma 5.4, Theorem 5.5 and Corollary 5.7.

A measurement on an equal-amplitude superposition of `n` decohered branches
is followed by branching into `n` branches, indexed by the natural numbers
below `n`. A rational agent assigns each branch a decision weight on a
common scale (Definition 3.5); the weight of an event is the sum of the
weights of the branches in which it occurs (Definition 3.6). The
transposition of two branches of an equal-amplitude state is implemented by
a unitary that leaves the state invariant (Assumption 3.7), and the agent's
weights are invariant under such symmetries (Assumption 3.8, state
supervenience together with the symmetry principle of Deutsch and Wallace).

What this file establishes. Under these assumptions all branches receive
equal weight, and every event receives, as a fraction of the total weight,
the number of branches in which it occurs divided by `n`: the Born weight.
Given branching indifference (Assumption 3.9), the same holds for an
outcome of rational squared amplitude realized by `m` of `n` equal
fine-grained branches.

What it does not establish. It does not establish the physical premises
(that decoherence yields the branches, that transpositions are symmetries),
nor the rationality axioms that justify Assumptions 3.8 and 3.9, nor the
extension to irrational amplitudes, which requires a continuity axiom and
the real numbers. Weights are natural numbers on a scale that may depend on
`n`; the theorem is stated as an equation of ratios to avoid division.
Theorem `assumptions_satisfiable` shows that the conditions imposed by the
axioms are jointly satisfiable, by uniform weights.
-/

namespace Philosophy.SCI_09

/-- Definition 3.4. The transposition of branches `i` and `j`. -/
def swap (i j k : Nat) : Nat := if k = i then j else if k = j then i else k

/-- Sum of `f 0, …, f (n-1)`. -/
def total (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => total f k + f k

/-- Definition 3.6. The weight of an event `E` among `n` branches. -/
def eventWeight (f : Nat → Nat) (E : Nat → Bool) (n : Nat) : Nat :=
  total (fun i => if E i then f i else 0) n

/-- The number of the `n` branches in which `E` occurs. -/
def count (E : Nat → Bool) (n : Nat) : Nat :=
  total (fun i => if E i then 1 else 0) n

/-- Definition 3.3. `IsSymmetry n σ`: the permutation `σ` of the `n`
branches is implemented by a unitary that leaves the equal-amplitude
state of `n` branches invariant. -/
axiom IsSymmetry : Nat → (Nat → Nat) → Prop

/-- Assumption 3.7 (physics). In an equal-amplitude state, the transposition
of any two branches is a symmetry. -/
axiom swap_symmetry : ∀ n i j, i < n → j < n → IsSymmetry n (swap i j)

/-- Definition 3.5. `weight n i`: the rational agent's decision weight for
branch `i` of the `n`-branch equal-amplitude measurement. -/
axiom weight : Nat → Nat → Nat

/-- Definition 3.5. The total of the weights (the scale) for `n` branches. -/
axiom scale : Nat → Nat

/-- Definition 3.5. The weights of the `n` branches sum to the scale. -/
axiom normalization : ∀ n, total (weight n) n = scale n

/-- Assumption 3.8 (state supervenience and symmetry). Branches related by
a symmetry of the state receive the same weight. -/
axiom symmetry_invariance :
  ∀ n σ i, i < n → IsSymmetry n σ → weight n (σ i) = weight n i

/-- Definition 3.6 (continued). `coarse n E`: the agent's weight for an
outcome realized by the branches `E` of an `n`-fold equal-amplitude
fine-graining. -/
axiom coarse : Nat → (Nat → Bool) → Nat

/-- Assumption 3.9 (branching indifference). The weight of a coarse-grained
outcome is the weight of the event consisting of its fine-grained branches. -/
axiom branching_indifference : ∀ n E, coarse n E = eventWeight (weight n) E n

theorem swap_left (i j : Nat) : swap i j i = j := by simp [swap]

/-- Lemma 5.3. In an equal-amplitude state all branches have equal weight. -/
theorem equal_weights (n i j : Nat) (hi : i < n) (hj : j < n) :
    weight n i = weight n j := by
  have h := symmetry_invariance n (swap i j) i hi (swap_symmetry n i j hi hj)
  rw [swap_left] at h
  exact h.symm

/-- A constant sum. -/
theorem total_const (f : Nat → Nat) (c : Nat) :
    ∀ n, (∀ i, i < n → f i = c) → total f n = n * c
  | 0, _ => by simp [total]
  | n + 1, h => by
    simp only [total]
    rw [total_const f c n (fun i hi => h i (by omega)), h n (by omega),
      Nat.succ_mul]

/-- Lemma 5.4. If all branches have weight `c`, an event has weight `c`
times the number of its branches. -/
theorem event_const (f : Nat → Nat) (c : Nat) (E : Nat → Bool) :
    ∀ n, (∀ i, i < n → f i = c) → eventWeight f E n = count E n * c
  | 0, _ => by simp [eventWeight, count, total]
  | n + 1, h => by
    have ih := event_const f c E n (fun i hi => h i (by omega))
    simp only [eventWeight, count, total] at ih ⊢
    rw [ih, h n (by omega)]
    cases E n <;> simp [Nat.add_mul]

/-- Theorem 5.5 (Born rule, equal amplitudes). The weight of any event,
as a fraction of the scale, is the number of its branches divided by `n`. -/
theorem born_equal (n : Nat) (E : Nat → Bool) :
    n * eventWeight (weight n) E n = count E n * scale n := by
  cases n with
  | zero => simp [eventWeight, count, total]
  | succ m =>
    have hc : ∀ i, i < m + 1 → weight (m + 1) i = weight (m + 1) 0 :=
      fun i hi => equal_weights (m + 1) i 0 hi (by omega)
    rw [event_const _ _ E (m + 1) hc, ← normalization (m + 1),
      total_const _ _ (m + 1) hc, Nat.mul_left_comm]

/-- Corollary 5.7 (rational amplitudes). An outcome realized by the branches
`E` of an `n`-fold equal fine-graining has weight `count E n / n`. -/
theorem born_rational (n : Nat) (E : Nat → Bool) :
    n * coarse n E = count E n * scale n := by
  rw [branching_indifference]
  exact born_equal n E

/-- The conditions imposed by Assumption 3.8 and Definition 3.5 are
jointly satisfiable, by uniform weights, whatever the symmetries are. -/
theorem assumptions_satisfiable (Sym : Nat → (Nat → Nat) → Prop) :
    ∃ (w : Nat → Nat → Nat) (s : Nat → Nat),
      (∀ n, total (w n) n = s n) ∧
      (∀ n σ i, i < n → Sym n σ → w n (σ i) = w n i) :=
  ⟨fun _ _ => 1, fun n => n,
   fun n => by rw [total_const (fun _ => 1) 1 n (fun _ _ => rfl), Nat.mul_one],
   fun _ _ _ _ _ => rfl⟩

end Philosophy.SCI_09

#print axioms Philosophy.SCI_09.born_equal
#print axioms Philosophy.SCI_09.born_rational
#print axioms Philosophy.SCI_09.assumptions_satisfiable
