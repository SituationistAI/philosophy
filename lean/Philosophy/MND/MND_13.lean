/-
MND-13 · Eliminativism Is Self-Undermining
Formalization of Theorem 3.1 of MND-13-a.

What this file establishes. If sincere assertion requires belief in what is
asserted (Assumption 2.1) and eliminativism has been sincerely asserted
(Assumption 2.2), then there are beliefs, and eliminativism is false.

What it does not establish. It does not establish either assumption; in
particular it does not answer the charge that Assumption 2.1 begs the
question, which the manuscript discusses.
-/

namespace Philosophy.MND_13

/-- Agents. -/
axiom Agent : Type

/-- Contents of assertions and beliefs. -/
axiom Content : Type

/-- `Believes a c`: agent `a` believes `c`. -/
axiom Believes : Agent → Content → Prop

/-- `SincerelyAsserts a c`: agent `a` sincerely asserts `c`. -/
axiom SincerelyAsserts : Agent → Content → Prop

/-- The content of eliminativism: that there are no beliefs. -/
axiom elim : Content

/-- Eliminativism, as a thesis about the world. -/
def Eliminativism : Prop := ¬ ∃ a c, Believes a c

/-- Assumption 2.1. Sincere assertion requires belief. -/
axiom assumption_2_1 : ∀ a c, SincerelyAsserts a c → Believes a c

/-- Assumption 2.2. Someone has sincerely asserted eliminativism. -/
axiom assumption_2_2 : ∃ a, SincerelyAsserts a elim

/-- Theorem 3.1 (main result). There are beliefs, so eliminativism is false. -/
theorem beliefs_exist : (∃ a c, Believes a c) ∧ ¬ Eliminativism :=
  match assumption_2_2 with
  | ⟨a, h⟩ =>
    have hb : ∃ a c, Believes a c := ⟨a, elim, assumption_2_1 a elim h⟩
    ⟨hb, fun he => he hb⟩

end Philosophy.MND_13

#print axioms Philosophy.MND_13.beliefs_exist
