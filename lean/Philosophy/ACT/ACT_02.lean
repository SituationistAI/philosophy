/-
ACT-02 · Frankfurt Cases Vindicated
Formalization of Theorem 3.1 and Corollary 3.2.

Scenarios are primitive. Each has an actual sequence (the agent's
deliberation, decision and action as they in fact unfold, Definition 2.1);
responsibility and the availability of alternatives are primitive predicates.

What this file establishes. From the actual-sequence principle
(Principle P1), the Frankfurt construction (Assumption 2.3) and the existence
of an ordinary case of responsible action (Assumption 2.4), it follows that
some agent is responsible although she could not have done otherwise, and so
that the principle of alternative possibilities is false. It does not
establish the premises; in particular it does not establish that a buffered
Frankfurt case can be built for every responsible action, which the
manuscript defends in Section 4 against the dilemma objection.
-/

namespace Philosophy.ACT_02

/-- Scenarios: an agent, her situation, and what she does in it. -/
axiom Scenario : Type

/-- Definition 2.1. Actual sequences of deliberation, decision and action. -/
axiom Sequence : Type

/-- The actual sequence of a scenario. -/
axiom seq : Scenario → Sequence

/-- The agent is morally responsible for what she does. -/
axiom Responsible : Scenario → Prop

/-- Definition 2.2. The agent could have done otherwise. -/
axiom Alternatives : Scenario → Prop

/-- Principle P1 (actual sequence). Responsibility depends only on the
actual sequence: scenarios with the same actual sequence agree on it. -/
axiom actual_sequence :
  ∀ w v, seq w = seq v → (Responsible w ↔ Responsible v)

/-- Assumption 2.3 (Frankfurt construction). For any scenario there is one
with the same actual sequence in which a counterfactual intervener, idle in
the actual sequence, removes every alternative. -/
axiom frankfurt_construction :
  ∀ w, ∃ v, seq v = seq w ∧ ¬ Alternatives v

/-- Assumption 2.4. Some agent is responsible for what she does. -/
axiom ordinary_case : ∃ w, Responsible w

/-- Theorem 3.1. Some agent is responsible without alternative possibilities. -/
theorem responsible_without_alternatives :
    ∃ v, Responsible v ∧ ¬ Alternatives v := by
  obtain ⟨w, hw⟩ := ordinary_case
  obtain ⟨v, hs, hn⟩ := frankfurt_construction w
  exact ⟨v, (actual_sequence v w hs).mpr hw, hn⟩

/-- Corollary 3.2. The principle of alternative possibilities is false. -/
theorem pap_false : ¬ (∀ w, Responsible w → Alternatives w) := by
  intro pap
  obtain ⟨v, hr, hn⟩ := responsible_without_alternatives
  exact hn (pap v hr)

end Philosophy.ACT_02

#print axioms Philosophy.ACT_02.pap_false
