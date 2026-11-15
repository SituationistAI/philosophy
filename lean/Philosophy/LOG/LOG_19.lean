/-
LOG-19 · Fitch's Paradox Accepted
Formalization of Lemma 3.1, Theorem 3.2, Corollaries 3.3 and 3.4 and
Propositions 3.5 and 3.6.

Propositions are sets of worlds. Knowledge is an operator `K` on
propositions (Definition 2.1), not a predicate of sentences: no sentence
can refer to itself. Possibility is truth at some accessible world
(Definition 2.2), with no condition on accessibility. The premises are
factivity (Assumption 2.3) and distribution over conjunction (Assumption
2.4). The knowability principle (Definition 2.5) is a hypothesis of the
theorem, not an axiom, since the manuscript rejects it. Non-omniscience
(Assumption 2.6) says that some truth is unknown at the actual world.

What this file establishes. Under factivity and distribution, the
knowability principle implies that every truth is known (Fitch's theorem),
at every world; given non-omniscience, the knowability principle fails at
the actual world, and the unknown truth p yields the unknowable truth
"p and it is not known that p". A two-world model shows that the premises
are jointly consistent with non-omniscience. The file does not establish
non-omniscience, which is a premise, and it does not treat any restricted
knowability principle.
-/

namespace Philosophy.LOG_19

/-- Worlds. -/
axiom World : Type

/-- Propositions are sets of worlds. -/
abbrev Pr := World → Prop

/-- Definition 2.1. Knowledge as an operator on propositions: `K p w`
means that, at world w, it is known (by someone, at some time) that p. -/
axiom K : Pr → Pr

/-- Definition 2.2. Accessibility for possibility; no condition is
imposed on it. -/
axiom R : World → World → Prop

/-- Definition 2.2. Possibility: truth at some accessible world. -/
def Pos (p : Pr) : Pr := fun w => ∃ v, R w v ∧ p v

/-- Conjunction and negation of propositions. -/
def And' (p q : Pr) : Pr := fun w => p w ∧ q w
def Not' (p : Pr) : Pr := fun w => ¬ p w

/-- Assumption 2.3 (factivity). What is known is true. -/
axiom factive : ∀ (p : Pr) (w : World), K p w → p w

/-- Assumption 2.4 (distribution). Knowing a conjunction is knowing each
conjunct. -/
axiom distrib : ∀ (p q : Pr) (w : World), K (And' p q) w → K p w ∧ K q w

/-- Definition 2.5. The knowability principle: every truth is knowable. -/
def Knowability : Prop := ∀ (p : Pr) (w : World), p w → Pos (K p) w

/-- The actual world. -/
axiom actual : World

/-- Assumption 2.6 (non-omniscience). Some truth is not known at the
actual world. -/
axiom nonomniscience : ∃ p : Pr, p actual ∧ ¬ K p actual

/-- Lemma 3.1. No one knows a proposition of the form
"p and it is not known that p" (a Fitch conjunction). -/
theorem fitch_unknowable (p : Pr) (v : World) : ¬ K (And' p (Not' (K p))) v := by
  intro h
  have ⟨hp, hnk⟩ := distrib p (Not' (K p)) v h
  exact factive (Not' (K p)) v hnk hp

/-- Theorem 3.2 (Fitch). If every truth is knowable, every truth is
known. -/
theorem fitch (kp : Knowability) : ∀ (p : Pr) (w : World), p w → K p w := by
  intro p w hp
  apply Classical.byContradiction
  intro hnk
  have ⟨v, _, hv⟩ := kp (And' p (Not' (K p))) w ⟨hp, hnk⟩
  exact fitch_unknowable p v hv

/-- Corollary 3.3. Given non-omniscience, the knowability principle is
false. -/
theorem knowability_fails : ¬ Knowability := by
  intro kp
  have ⟨p, hp, hnk⟩ := nonomniscience
  exact hnk (fitch kp p actual hp)

/-- Corollary 3.4. Given non-omniscience, there is a truth at the actual
world that is not knowable there: "p and it is not known that p". -/
theorem unknowable_truth :
    ∃ q : Pr, q actual ∧ ¬ Pos (K q) actual := by
  have ⟨p, hp, hnk⟩ := nonomniscience
  refine ⟨And' p (Not' (K p)), ⟨hp, hnk⟩, ?_⟩
  intro ⟨v, _, hv⟩
  exact fitch_unknowable p v hv

/-- Proposition 3.5 (the intuitionistic version). Without classical
reasoning, the knowability principle implies that no truth is unknown:
every truth is not-not known. -/
theorem fitch_intuitionistic (kp : Knowability) :
    ∀ (p : Pr) (w : World), p w → ¬ ¬ K p w := by
  intro p w hp hnk
  have ⟨v, _, hv⟩ := kp (And' p (Not' (K p))) w ⟨hp, hnk⟩
  exact fitch_unknowable p v hv

/-- Proposition 3.6. The premises are consistent with non-omniscience: in
a two-world model in which every world is accessible from every world and
a proposition is known just when it is true at both worlds, knowledge is
factive and distributes over conjunction, and some truth is unknown. -/
theorem premises_consistent :
    let Kb : (Bool → Prop) → (Bool → Prop) := fun p _ => p true ∧ p false
    (∀ (p : Bool → Prop) w, Kb p w → p w) ∧
    (∀ (p q : Bool → Prop) w,
      Kb (fun u => p u ∧ q u) w → Kb p w ∧ Kb q w) ∧
    (∃ (p : Bool → Prop), p true ∧ ¬ Kb p true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p w h; cases w
    · exact h.2
    · exact h.1
  · intro p q _ h
    exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩
  · exact ⟨fun u => u = true, rfl, fun h => absurd h.2 (by decide)⟩

end Philosophy.LOG_19

#print axioms Philosophy.LOG_19.fitch
#print axioms Philosophy.LOG_19.knowability_fails
#print axioms Philosophy.LOG_19.fitch_intuitionistic
#print axioms Philosophy.LOG_19.premises_consistent
