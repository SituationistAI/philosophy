/-
ETH-28 · The Demandingness of Morality
Formalization of Theorem 3.1 and Corollary 3.2.

For an agent with annual income I, measured with all costs in
income-equivalents, the cost required by beneficence, by rescue and by
supererogation are given as functions of I. Their values are taken from
the other manuscripts of the cluster: beneficence requires a tenth of income
(ETH-06, Assumption 2.1), the required rescues of a year cost at most a tenth
of income (ETH-18, Assumption 2.2), and supererogatory acts are by definition
not required (ETH-14, Assumption 2.3). The decency line is the total
requirement; the saintly bound is at most the agent's income (Assumption 2.4).

What this file establishes. The total requirement lies between a tenth and a
fifth of income; at least four fifths of income is left to the agent's
personal prerogative; and if the saintly bound exceeds a fifth of income,
there is room for supererogation between the decency line and that bound.

What it does not establish. The three imported results are premises here,
proved (as far as they are formal) in ETH_06 and ETH_18 or argued in ETH-14.
-/

namespace Philosophy.ETH_28

/-- The cost required by the duty of beneficence for income `I`. -/
axiom beneficence : Nat → Nat
/-- The total cost of the rescues required in a year for income `I`. -/
axiom rescue : Nat → Nat
/-- The cost required by supererogation for income `I`. -/
axiom supererogation : Nat → Nat
/-- The saintly bound on self-sacrifice for income `I`. -/
axiom saintly : Nat → Nat

/-- Assumption 2.1 (from ETH-06). Beneficence requires a tenth of income. -/
axiom beneficence_tenth : ∀ I, beneficence I = I / 10

/-- Assumption 2.2 (from ETH-18). The required rescues of a year cost at most
a tenth of income. -/
axiom rescue_tenth : ∀ I, rescue I ≤ I / 10

/-- Assumption 2.3 (from ETH-14). Supererogatory acts are not required. -/
axiom supererogation_zero : ∀ I, supererogation I = 0

/-- Assumption 2.4. The saintly bound does not exceed income. -/
axiom saintly_le : ∀ I, saintly I ≤ I

/-- Definition 2.5. The total requirement, which is the decency line. -/
noncomputable def required (I : Nat) : Nat := beneficence I + rescue I + supererogation I

/-- Definition 2.6. The prerogative: what remains free of requirement. -/
noncomputable def prerogative (I : Nat) : Nat := I - required I

/-- Theorem 3.1 (moderate demandingness). The total requirement is at least a
tenth and at most a fifth of income, and the prerogative is at least four
fifths of income. -/
theorem moderate (I : Nat) :
    I / 10 ≤ required I ∧ required I ≤ I / 5 ∧ 4 * I / 5 ≤ prerogative I := by
  have hb := beneficence_tenth I
  have hr := rescue_tenth I
  have hs := supererogation_zero I
  unfold prerogative required
  omega

/-- Corollary 3.2 (room for supererogation). If the saintly bound exceeds a
fifth of income, some level of sacrifice lies strictly above the decency line
and within the saintly bound, and it is not more than the agent's income. -/
theorem room_for_supererogation (I : Nat) (h : I / 5 < saintly I) :
    ∃ k, required I < k ∧ k ≤ saintly I ∧ k ≤ I := by
  have hm := (moderate I).2.1
  have hs := saintly_le I
  exact ⟨saintly I, by omega, Nat.le_refl _, hs⟩

end Philosophy.ETH_28

#print axioms Philosophy.ETH_28.moderate
#print axioms Philosophy.ETH_28.room_for_supererogation
