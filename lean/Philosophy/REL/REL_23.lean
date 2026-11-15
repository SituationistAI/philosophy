/-
REL-23 · Gaunilo's Island, the Devil and an Asymmetry
Formalization of Lemma 3.1, Theorem 3.2 and Proposition 3.3.

Framework. The modal framework of REL-01 (worlds, an accessibility
relation, a constant domain of beings with an existence predicate) is
restated here, since this module is checked on its own. Maximal greatness
is defined as in REL-01 (Definition 2.4 there): existence and maximal
excellence at every accessible world. The parody replaces maximal
excellence by maximal wickedness: omnipotence together with perfect evil,
where a perfectly evil being wills an outcome at least as bad as any it can
bring about (Definitions 2.1 to 2.3). Badness is measured on the natural
numbers.

What this file establishes. If for every possible outcome there is a worse
possible outcome (Assumption 2.4), maximal wickedness is impossible
(Lemma 3.1), so the possibility premise of the parody is false at every
world, given only reflexivity of accessibility (Theorem 3.2). By contrast,
an omnipotent and morally perfect being is consistent with the same
unboundedness assumption: a concrete model satisfies both (Proposition
3.3). It does not establish that a maximally great being is possible; that
is the possibility premise of REL-01.
-/

namespace Philosophy.REL_23

/-- Possible worlds. -/
axiom World : Type

/-- Accessibility (as in REL-01). Only reflexivity is used here. -/
axiom R : World → World → Prop

/-- Reflexivity of accessibility (clause (i) of the S5 assumption of
REL-01). -/
axiom R_refl : ∀ w, R w w

abbrev WProp := World → Prop

def Box (p : WProp) : WProp := fun w => ∀ v, R w v → p v
def Dia (p : WProp) : WProp := fun w => ∃ v, R w v ∧ p v

/-- Beings (constant domain). -/
axiom Being : Type

/-- Existence at a world. -/
axiom Exists : Being → WProp

/-- Outcomes (states of affairs an agent may bring about). -/
axiom Outcome : Type

/-- `Possible o`: the outcome is possible. -/
axiom Possible : Outcome → Prop

/-- `bad o`: the degree of badness of `o`. -/
axiom bad : Outcome → Nat

/-- `CanBring x o w`: at `w`, `x` is able to bring about `o`. -/
axiom CanBring : Being → Outcome → World → Prop

/-- `Wills x o w`: at `w`, `x` wills `o`. -/
axiom Wills : Being → Outcome → World → Prop

/-- Definition 2.1. Omnipotence with respect to outcomes: the ability to
bring about every possible outcome. (Outcomes are described without
reference to the agent's powers, so this is omnipotence in the sense of
REL-04.) -/
def Omnipotent (x : Being) (w : World) : Prop :=
  ∀ o, Possible o → CanBring x o w

/-- Definition 2.2. Perfect evil: `x` wills an outcome at least as bad as
any outcome `x` can bring about. -/
def PerfectlyEvil (x : Being) (w : World) : Prop :=
  ∃ o, Wills x o w ∧ ∀ o', CanBring x o' w → bad o' ≤ bad o

/-- Definition 2.3. Maximal wickedness at a world, and maximal evil-greatness:
existence and maximal wickedness at every accessible world (the parody of
REL-01, Definition 2.4). -/
def MaximallyWicked (x : Being) : WProp :=
  fun w => Exists x w ∧ Omnipotent x w ∧ PerfectlyEvil x w

def MaximallyEvil (x : Being) : WProp := Box (MaximallyWicked x)

def SomeMaximallyEvil : WProp := fun w => ∃ x, MaximallyEvil x w

/-- Assumption 2.4 (unboundedness of badness). For every outcome there is a
possible outcome that is worse. -/
axiom unbounded : ∀ o, ∃ o', Possible o' ∧ bad o' > bad o

/-- Lemma 3.1. No being is omnipotent and perfectly evil at any world. -/
theorem no_wicked_maximum (x : Being) (w : World) :
    ¬ (Omnipotent x w ∧ PerfectlyEvil x w) := by
  intro ⟨hom, o, _, hmax⟩
  obtain ⟨o', hp, hgt⟩ := unbounded o
  have hle := hmax o' (hom o' hp)
  omega

/-- Theorem 3.2 (main result). At every world, it is not possible that a
maximally evil being exists: the possibility premise of the parody is
false. -/
theorem parody_premise_false (w : World) : ¬ Dia SomeMaximallyEvil w := by
  intro ⟨v, _, x, hx⟩
  obtain ⟨_, hom, hev⟩ := hx v (R_refl v)
  exact no_wicked_maximum x v ⟨hom, hev⟩

/-! ## The asymmetry

Proposition 3.3. Moral perfection, defined by a threshold (never bringing
about a wrong outcome), is consistent with omnipotence under the same
unboundedness assumption. Model: outcomes are natural numbers, badness is
the identity, every outcome is possible, the being can bring about every
outcome, an outcome is wrong when its badness is positive, and the being
brings about only the outcome of badness zero. -/

namespace Model

def possible (_ : Nat) : Prop := True
def badness (o : Nat) : Nat := o
def canBring (_ : Nat) : Prop := True
def brings (o : Nat) : Prop := o = 0
def wrong (o : Nat) : Prop := badness o > 0

/-- Proposition 3.3. In the model, badness is unbounded, the being is
omnipotent, it brings about some outcome, and it brings about no wrong
outcome. -/
theorem perfection_consistent :
    (∀ o, ∃ o', possible o' ∧ badness o' > badness o) ∧
    (∀ o, possible o → canBring o) ∧
    (∃ o, brings o) ∧
    (∀ o, brings o → ¬ wrong o) := by
  refine ⟨fun o => ⟨o + 1, trivial, ?_⟩, fun _ _ => trivial, ⟨0, rfl⟩, ?_⟩
  · simp [badness]
  · intro o h hw
    simp [brings] at h
    simp [wrong, badness, h] at hw

end Model

end Philosophy.REL_23

#print axioms Philosophy.REL_23.parody_premise_false
#print axioms Philosophy.REL_23.Model.perfection_consistent
