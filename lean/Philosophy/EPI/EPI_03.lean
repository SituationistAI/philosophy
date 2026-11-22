/-
EPI-03 · The Problem of Induction
Formalization of Propositions 4.1, 4.2 and 4.4, Theorem 4.3 and
Proposition 6.1.

A world is an infinite binary sequence of observations. A one-step rule
predicts the next observation from the current one. Induction (the straight
rule) predicts that the next observation will be like the current one;
counter-induction predicts that it will differ. A rule is reliable in a
world if its predictions are correct at every step (Definition 3.1).

The track record of a rule in a world is the sequence recording, at each
step, whether the rule's prediction was correct. A rule-circular argument
for a rule applies a rule to that rule's own track record (Definition 3.3).

What this file establishes. No rule is reliable in every world, and every
rule is reliable in some world (Hume's point, in the form of a no-free-lunch
result). In a uniform world induction is reliable and the inductive
argument for induction is reliable as well, while the parallel
counter-inductive argument for counter-induction has false conclusions at
every step. It does not establish that the actual world is uniform.
-/

namespace Philosophy.EPI_03

/-- Worlds: infinite sequences of binary observations. -/
abbrev World := Nat → Bool

/-- One-step prediction rules. -/
abbrev Rule := Bool → Bool

/-- Definition 3.1. A rule is reliable in a world if every prediction is correct. -/
def Reliable (f : Rule) (w : World) : Prop := ∀ n, f (w n) = w (n + 1)

/-- Definition 3.2. Induction and counter-induction. -/
def induction : Rule := fun b => b
def counter : Rule := fun b => !b

/-- Definition 3.3. The track record of a rule in a world. -/
def record (f : Rule) (w : World) : World := fun n => f (w n) == w (n + 1)

/-- A world built to defeat a rule: each observation is the opposite of
what the rule predicts from the previous one. -/
def spoiler (f : Rule) : World
  | 0 => true
  | n + 1 => !(f (spoiler f n))

/-- A world built to confirm a rule. -/
def follower (f : Rule) : World
  | 0 => true
  | n + 1 => f (follower f n)

/-- Proposition 4.1 (Hume). No rule is reliable in every world. -/
theorem no_universal_rule (f : Rule) : ∃ w, ¬ Reliable f w := by
  refine ⟨spoiler f, fun h => ?_⟩
  have h0 := h 0
  simp only [spoiler] at h0
  cases hf : f true <;> simp [hf] at h0

/-- Proposition 4.2. Every rule is reliable in some world. -/
theorem every_rule_somewhere (f : Rule) : ∃ w, Reliable f w :=
  ⟨follower f, fun _ => rfl⟩

/-- A uniform world: every observation is the same. -/
def Uniform (w : World) : Prop := ∀ n, w (n + 1) = w n

/-- Theorem 4.3. In a uniform world, induction is reliable, its track record
is uniformly successful, and induction applied to that track record (the
rule-circular argument for induction) is reliable as well. -/
theorem inductive_support (w : World) (hu : Uniform w) :
    Reliable induction w ∧ (∀ n, record induction w n = true) ∧
    Reliable induction (record induction w) := by
  have hr : ∀ n, record induction w n = true := by
    intro n; simp [record, induction, hu n]
  refine ⟨fun n => (hu n).symm, hr, fun n => ?_⟩
  simp [induction, hr n, hr (n + 1)]

/-- Proposition 4.4. In a uniform world, counter-induction is not reliable,
its track record is uniformly unsuccessful, and counter-induction applied
to that track record predicts success at every step, wrongly. -/
theorem counter_support_fails (w : World) (hu : Uniform w) :
    ¬ Reliable counter w ∧ (∀ n, record counter w n = false) ∧
    (∀ n, counter (record counter w n) ≠ record counter w (n + 1)) := by
  have hr : ∀ n, record counter w n = false := by
    intro n; simp [record, counter, hu n]
  refine ⟨fun h => ?_, hr, fun n => ?_⟩
  · have h0 := h 0
    simp [counter, hu 0] at h0
  · simp [counter, hr n, hr (n + 1)]

/-- Rules with memory: predict observation n + p from observation n. A
`p`-step rule is reliable in a world if its predictions are always correct. -/
def ReliableAt (p : Nat) (f : Rule) (w : World) : Prop := ∀ n, f (w n) = w (n + p)

/-- Track record of a p-step rule. -/
def recordAt (p : Nat) (f : Rule) (w : World) : World := fun n => f (w n) == w (n + p)

/-- Proposition 6.1. In a world with period p, the rule "copy the observation
p steps back" is reliable, and its track record is a uniform world, in which
induction is reliable (by Theorem 4.3). -/
theorem periodic_support (p : Nat) (w : World) (hp : ∀ n, w (n + p) = w n) :
    ReliableAt p induction w ∧ Uniform (recordAt p induction w) := by
  refine ⟨fun n => (hp n).symm, fun n => ?_⟩
  simp [recordAt, induction, hp]

end Philosophy.EPI_03

#print axioms Philosophy.EPI_03.no_universal_rule
#print axioms Philosophy.EPI_03.inductive_support
#print axioms Philosophy.EPI_03.counter_support_fails
#print axioms Philosophy.EPI_03.periodic_support
