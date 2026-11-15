/-
MND-04 · Mary's Room and the Ability Hypothesis
Formalization of Lemma 3.2 and of the logical structure of the knowledge
argument (Section 1).

What this file establishes. Given premise (K1) and physicalism
(Assumption 3.1), Mary knows after her release no fact she did not know
before. Consequently, the knowledge argument's premise (K2), read as
"Mary comes to know a fact she did not know", is inconsistent with (K1) and
physicalism. The file does not establish physicalism.
-/

namespace Philosophy.MND_04

/-- Facts about colour vision. -/
axiom Fact : Type

/-- Physical facts. -/
axiom Physical : Fact → Prop

/-- Mary's knowledge before and after her release. -/
axiom KnowsBefore : Fact → Prop
axiom KnowsAfter : Fact → Prop

/-- (K1). Before her release, Mary knows every physical fact. -/
axiom k1 : ∀ f, Physical f → KnowsBefore f

/-- Assumption 3.1 (physicalism). Every fact about colour vision is physical. -/
axiom physicalism : ∀ f, Physical f

/-- Lemma 3.2. Mary knows no new fact after her release. -/
theorem no_new_fact (f : Fact) : KnowsAfter f → KnowsBefore f :=
  fun _ => k1 f (physicalism f)

/-- The knowledge argument, with (K2) read as learning a new fact, is
inconsistent with (K1) and physicalism. -/
theorem k2_inconsistent (k2 : ∃ f, KnowsAfter f ∧ ¬ KnowsBefore f) : False := by
  obtain ⟨f, hafter, hnot⟩ := k2
  exact hnot (no_new_fact f hafter)

end Philosophy.MND_04

#print axioms Philosophy.MND_04.no_new_fact
#print axioms Philosophy.MND_04.k2_inconsistent
