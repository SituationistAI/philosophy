/-
ACT-15 · Luck and Libertarian Freedom
Formalization of Theorem 3.1, Corollary 3.2 and Proposition 3.3.

A self-forming choice has a set of competing outcomes, one of which occurs
indeterministically. Trying, occurring, and responsibility for an outcome
are primitive predicates.

What this file establishes. (i) From the attribution principle
(Principle P1), the agent's control over her efforts (Assumption 2.2) and
dual effort (Assumption 2.3), she is responsible for whichever outcome
occurs; nothing about which outcome occurs is assumed. (ii) In the
four-world model of Bratman's video game, each intention is consistent
with the agent's belief that she will not hit both targets, although their
conjunction is not; so intending each is consistent with what she believes.
It does not establish the premises, and in particular not that agents make
dual efforts in actual hard choices.
-/

namespace Philosophy.ACT_15

/-- Definition 2.1. The competing outcomes of a self-forming choice. -/
axiom Outcome : Type

/-- The agent tries to bring the outcome about. -/
axiom Tries : Outcome → Prop

/-- The outcome occurs. -/
axiom Occurs : Outcome → Prop

/-- The agent is responsible for the outcome. -/
axiom ResponsibleFor : Outcome → Prop

/-- The agent's efforts issue from a reasons-responsive mechanism of her own. -/
axiom Control : Prop

/-- Principle P1 (attribution). An outcome that occurs as the result of an
effort the agent controls and makes is one she is responsible for, even if
the effort might have failed. -/
axiom attribution : ∀ o, Control → Tries o → Occurs o → ResponsibleFor o

/-- Assumption 2.2. The agent controls her efforts. -/
axiom control : Control

/-- Assumption 2.3 (dual effort). The agent tries to bring about each of the
competing outcomes. -/
axiom dual_effort : ∀ o, Tries o

/-- Theorem 3.1. Whichever outcome occurs, the agent is responsible for it. -/
theorem responsible_whichever : ∀ o, Occurs o → ResponsibleFor o :=
  fun o h => attribution o control (dual_effort o) h

/-- Corollary 3.2. If some outcome occurs, the agent is responsible for an
outcome that occurs. -/
theorem responsible_for_occurring (h : ∃ o, Occurs o) :
    ∃ o, Occurs o ∧ ResponsibleFor o := by
  obtain ⟨o, ho⟩ := h
  exact ⟨o, ho, responsible_whichever o ho⟩

/-- The video game: a world records whether target 1 and target 2 are hit. -/
abbrev World := Bool × Bool

/-- The agent's belief: the machine shuts down before both are hit. -/
def believed (w : World) : Bool := !(w.1 && w.2)

/-- Proposition 3.3. Each intention is consistent with the belief; the
conjunction of the two is not. -/
theorem video_game :
    (∃ w : World, believed w = true ∧ w.1 = true) ∧
    (∃ w : World, believed w = true ∧ w.2 = true) ∧
    ¬ (∃ w : World, believed w = true ∧ w.1 = true ∧ w.2 = true) := by
  refine ⟨⟨(true, false), rfl, rfl⟩, ⟨(false, true), rfl, rfl⟩, ?_⟩
  intro ⟨⟨a, b⟩, hb, h1, h2⟩
  simp at h1 h2
  subst h1; subst h2
  simp [believed] at hb

end Philosophy.ACT_15

#print axioms Philosophy.ACT_15.responsible_whichever
#print axioms Philosophy.ACT_15.video_game
