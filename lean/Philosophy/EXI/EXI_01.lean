/-
EXI-01 · On the Meaning of Life
Formalization of Theorem 4.

What this file establishes. Given Definition 1 and Assumption 3, a life of
positive meaning is available to every agent. The proof also uses the bridge
axiom `engagement_realizable` (if an agent can engage in a project, some life
available to her includes that engagement), which the manuscript leaves
implicit; see EXI-01-b, Prop. 8.1. The proof is immediate; the
substance of the manuscript lies in its assumptions, which are discussed in
the commentary (EXI-01-b).
-/

namespace Philosophy.EXI_01

/-- Agents capable of intentional action. -/
axiom Agent : Type

/-- Projects. -/
axiom Project : Type

/-- Lives available to an agent. -/
axiom Life : Agent → Type

/-- `ObjectivelyWorthy p`: the value of `p` does not depend on the attitudes
of those engaged in it (Assumption 2 asserts that such projects exist). -/
axiom ObjectivelyWorthy : Project → Prop

/-- `CanEngage a p`: agent `a` is able to engage actively in project `p`. -/
axiom CanEngage : (a : Agent) → Project → Prop

/-- `Includes l p`: life `l` includes active engagement with `p`. -/
axiom Includes : {a : Agent} → Life a → Project → Prop

/-- An agent who can engage in a project has a life that includes it. -/
axiom engagement_realizable :
  ∀ (a : Agent) (p : Project), CanEngage a p → ∃ l : Life a, Includes l p

/-- Definition 1, positive case. A life has positive meaning if it includes
active engagement with some objectively worthy project. -/
def PositivelyMeaningful {a : Agent} (l : Life a) : Prop :=
  ∃ p, ObjectivelyWorthy p ∧ Includes l p

/-- Assumption 3. Every agent can engage in some objectively worthy project. -/
axiom assumption_3 : ∀ a : Agent, ∃ p, ObjectivelyWorthy p ∧ CanEngage a p

/-- Theorem 4. For every agent, a life of positive meaning is available. -/
theorem meaning_available (a : Agent) : ∃ l : Life a, PositivelyMeaningful l := by
  obtain ⟨p, hw, hc⟩ := assumption_3 a
  obtain ⟨l, hl⟩ := engagement_realizable a p hc
  exact ⟨l, p, hw, hl⟩

end Philosophy.EXI_01

#print axioms Philosophy.EXI_01.meaning_available
