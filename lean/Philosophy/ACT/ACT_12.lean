/-
ACT-12 · External Reasons Exist
Formalization of Theorem 3.2 and Corollary 3.3.

Agents and acts are primitive. An agent's subjective motivational set is
represented by a predicate on motives; sound deliberation is a primitive
relation from motives to acts (Definition 2.1). A reason is internal if some
motive in the agent's set leads to the act by sound deliberation
(Definition 2.2), external otherwise.

What this file establishes. From the principle that what an agent ought to
do she has reason to do (Principle P1), the verdict that the agent of the
Tuesday case ought to avoid the agony (Assumption 2.3), and the fact that
no sound deliberation from her motives reaches that conclusion
(Assumption 2.4), it follows that she has an external reason, and so that
Williams's internalism is false. It does not establish the premises.
-/

namespace Philosophy.ACT_12

axiom Agent : Type
axiom Act : Type
axiom Motive : Type

/-- The agent's subjective motivational set. -/
axiom InS : Agent → Motive → Prop

/-- Definition 2.1. Sound deliberation leads from the motive to the act. -/
axiom SoundRoute : Motive → Act → Prop

/-- The agent has a (normative) reason to perform the act. -/
axiom Reason : Agent → Act → Prop

/-- The agent ought, all things considered, to perform the act. -/
axiom Ought : Agent → Act → Prop

/-- Definition 2.2. The act is reachable by sound deliberation from the
agent's motivational set. -/
def Reachable (a : Agent) (x : Act) : Prop := ∃ m, InS a m ∧ SoundRoute m x

/-- Definition 2.2. An external reason: a reason that no sound deliberation
from the agent's motivational set reaches. -/
def ExternalReason (a : Agent) (x : Act) : Prop := Reason a x ∧ ¬ Reachable a x

/-- Principle P1 (ought implies reason). -/
axiom ought_reason : ∀ a x, Ought a x → Reason a x

/-- The agent of the Tuesday case and the act of avoiding the agony. -/
axiom tuesday : Agent
axiom avoid : Act

/-- Assumption 2.3. The Tuesday agent ought to avoid the agony. -/
axiom tuesday_ought : Ought tuesday avoid

/-- Assumption 2.4. No motive in her set leads to avoiding it by sound
deliberation. -/
axiom tuesday_unreachable : ∀ m, InS tuesday m → ¬ SoundRoute m avoid

/-- Lemma 3.1. Avoiding the agony is not reachable for the Tuesday agent. -/
theorem not_reachable : ¬ Reachable tuesday avoid := by
  intro ⟨m, hm, hr⟩
  exact tuesday_unreachable m hm hr

/-- Theorem 3.2. External reasons exist. -/
theorem external_reasons_exist : ∃ a x, ExternalReason a x :=
  ⟨tuesday, avoid, ought_reason _ _ tuesday_ought, not_reachable⟩

/-- Corollary 3.3. Internalism (every reason is reachable) is false. -/
theorem internalism_false : ¬ (∀ a x, Reason a x → Reachable a x) := by
  intro h
  exact not_reachable (h _ _ (ought_reason _ _ tuesday_ought))

end Philosophy.ACT_12

#print axioms Philosophy.ACT_12.external_reasons_exist
#print axioms Philosophy.ACT_12.internalism_false
