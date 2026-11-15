/-
MND-11 · Mental Causes Are Proportional
Formalization of Section 3 of MND-11-a.

What this file establishes. Over the serious possibilities for a realizing
variable, given that a mental property is actual, multiply realized, not
necessary, and such that the effect occurs under an intervention exactly when
the mental property is instantiated (Assumptions 2.5-2.8): the mental
property is proportional to the effect (Lemma 3.1); the actual physical
realizer is overly specific and its absence is an ambiguous intervention
(Lemma 3.2); every proportional cause is coextensive with the mental property
(Proposition 3.3); and, given that proportional difference-makers are causes
(Principle P1), the mental property causes the effect (Theorem 3.4).

What it does not establish. It does not establish the assumptions, and it
does not analyse causation: `Causes` is a primitive constrained only by
Principle P1.
-/

namespace Philosophy.MND_11

/-- Serious possibilities for the realizing variable (Definition 2.1). -/
axiom Val : Type

/-- The actual value: the actual physical realizer. -/
axiom actual : Val

/-- The mental property, as a coarse-graining of the realizing variable. -/
axiom M : Val → Prop

/-- `E v`: the effect occurs under the intervention that sets the variable to `v`. -/
axiom E : Val → Prop

/-- The primitive causal relation between a property and the effect. -/
axiom Causes : (Val → Prop) → Prop

/-- Definition 2.2. `C` is proportional to the effect. -/
def Proportional (C : Val → Prop) : Prop := C actual ∧ ∀ v, C v ↔ E v

/-- Definition 2.3. `C` is overly specific for the effect. -/
def OverlySpecific (C : Val → Prop) : Prop :=
  C actual ∧ (∀ v, C v → E v) ∧ ∃ v, ¬ C v ∧ E v

/-- Definition 2.4. The intervention that makes `C` absent is ambiguous. -/
def Ambiguous (C : Val → Prop) : Prop :=
  ∃ v w, ¬ C v ∧ ¬ C w ∧ E v ∧ ¬ E w

/-- The actual physical realizer, as a maximally specific property. -/
def P : Val → Prop := fun v => v = actual

/-- Assumption 2.5. The mental property is actually instantiated. -/
axiom assumption_2_5 : M actual

/-- Assumption 2.6 (Realization insensitivity). -/
axiom assumption_2_6 : ∀ v, M v → E v

/-- Assumption 2.7 (Dependence). -/
axiom assumption_2_7 : ∀ v, ¬ M v → ¬ E v

/-- Assumption 2.8 (Multiple realizability and contingency). -/
axiom assumption_2_8 : (∃ v, v ≠ actual ∧ M v) ∧ ∃ w, ¬ M w

/-- Principle P1. A proportional difference-maker is a cause. -/
axiom principle_P1 : ∀ C, Proportional C → Causes C

/-- Lemma 3.1. The mental property is proportional to the effect. -/
theorem mental_proportional : Proportional M :=
  ⟨assumption_2_5, fun v =>
    ⟨assumption_2_6 v, fun he =>
      Classical.byContradiction fun hm => assumption_2_7 v hm he⟩⟩

/-- Lemma 3.2. The physical realizer is overly specific, and its absence is
an ambiguous intervention. -/
theorem realizer_overly_specific : OverlySpecific P ∧ Ambiguous P := by
  obtain ⟨⟨v, hv, hmv⟩, ⟨w, hw⟩⟩ := assumption_2_8
  have hEa : E actual := assumption_2_6 actual assumption_2_5
  have hwa : ¬ P w := fun h => by
    simp only [P] at h
    subst h
    exact hw assumption_2_5
  refine ⟨⟨rfl, ?_, v, hv, assumption_2_6 v hmv⟩,
    v, w, hv, hwa, assumption_2_6 v hmv, assumption_2_7 w hw⟩
  intro u hu
  simp only [P] at hu
  subst hu
  exact hEa

/-- Proposition 3.3 (Uniqueness). Every proportional cause is coextensive
with the mental property. -/
theorem uniqueness (C : Val → Prop) (h : Proportional C) : ∀ v, C v ↔ M v :=
  fun v => (h.2 v).trans (mental_proportional.2 v).symm

/-- Theorem 3.4 (main result). The mental property causes the effect, and
the physical realizer is overly specific and not proportional. -/
theorem mental_causation :
    Causes M ∧ OverlySpecific P ∧ ¬ Proportional P := by
  refine ⟨principle_P1 M mental_proportional, realizer_overly_specific.1, ?_⟩
  intro ⟨_, h⟩
  obtain ⟨_, _, v, hv, he⟩ := realizer_overly_specific.1
  exact hv ((h v).2 he)

end Philosophy.MND_11

#print axioms Philosophy.MND_11.mental_causation
