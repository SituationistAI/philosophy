/-
MND-21 · Computation Without a Central Processor
Formalization of Section 3 of MND-21-a.

What this file establishes. Given that every cognitive process computes
(Assumption 2.5), that a mind whose cognitive processes all compute itself
computes (Assumption 2.6), and that some two cognitive processes are
sequenced by no unit (Assumption 2.7): the mind computes (Lemma 3.1), it is
not a single computer in the sense of Definition 2.3 (Lemma 3.2), and it
contains a semi-autonomous pair of cognitive processes (Theorem 3.3).

What it does not establish. It does not establish the assumptions, which are
empirical, and it does not analyse computation or sequencing, which are
primitives. That semi-autonomous processes exchange results is not modelled.
-/

namespace Philosophy.MND_21

/-- Processes of the system. -/
axiom Process : Type
/-- Units (candidate controllers) of the system. -/
axiom Ctrl : Type
/-- Being a cognitive process. -/
axiom Cog : Process → Prop
/-- Definition 2.1. The process computes (mechanistic sense). -/
axiom Computes : Process → Prop
/-- Definition 2.2. `Sequences c p q`: unit `c` fixes the relative order and
timing of the steps of `p` and `q`. -/
axiom Sequences : Ctrl → Process → Process → Prop
/-- The mind, as the system of its cognitive processes, computes. -/
axiom MindComputes : Prop

/-- Definition 2.3. The mind is a single computer: some unit sequences every
pair of its cognitive processes. -/
def SingleComputer : Prop :=
  ∃ c : Ctrl, ∀ p q, Cog p → Cog q → Sequences c p q

/-- Definition 2.4. `p` and `q` are semi-autonomous: no unit sequences them. -/
def SemiAutonomous (p q : Process) : Prop := ∀ c : Ctrl, ¬ Sequences c p q

/-- Assumption 2.5 (Computation). -/
axiom assumption_2_5 : ∀ p, Cog p → Computes p
/-- Assumption 2.6 (Composition). -/
axiom assumption_2_6 : (∀ p, Cog p → Computes p) → MindComputes
/-- Assumption 2.7 (Dissociation). -/
axiom assumption_2_7 : ∃ p q, Cog p ∧ Cog q ∧ SemiAutonomous p q

/-- Lemma 3.1. The mind computes. -/
theorem lemma_3_1 : MindComputes := assumption_2_6 assumption_2_5

/-- Lemma 3.2. The mind is not a single computer. -/
theorem lemma_3_2 : ¬ SingleComputer := by
  intro ⟨c, hc⟩
  obtain ⟨p, q, hp, hq, hsemi⟩ := assumption_2_7
  exact hsemi c (hc p q hp hq)

/-- Theorem 3.3. The mind computes, is not a single computer, and contains a
semi-autonomous pair of cognitive processes. -/
theorem theorem_3_3 :
    MindComputes ∧ ¬ SingleComputer ∧
    ∃ p q, Cog p ∧ Cog q ∧ SemiAutonomous p q :=
  ⟨lemma_3_1, lemma_3_2, assumption_2_7⟩

end Philosophy.MND_21

#print axioms Philosophy.MND_21.theorem_3_3
