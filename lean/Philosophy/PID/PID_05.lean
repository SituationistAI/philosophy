/-
PID-05 · Animalism Defended
Formalization of Theorem 3.1, Theorem 3.2 and Corollary 3.3.

The module fixes a brain-in-a-vat case with two times, now and later.
`ExistsLater x` says that `x` exists at the later time, `VatOccupant x`
that `x` is then wholly located in the vat as a brain sustained by its
machinery, `LivingOrganismLater x` that `x` is then a living organism.

What this file establishes. Given the thinking-animal premises
(Assumptions 2.4 to 2.6), you are an organism (Theorem 3.1); given in
addition the biological persistence condition (Assumption 2.7) and the
description of the vat (Assumption 2.8), you do not survive as the brain in
the vat (Theorem 3.2); and, given the psychological continuity of the vat
occupant (Assumption 2.9), there is later a person psychologically
continuous with you who is not you (Corollary 3.3).

What it does not establish. It does not establish any of the assumptions,
in particular the single-thinker premise (Assumption 2.5), which carries
the weight of the argument, and it does not model the persistence of
persons as such (PID-01), which the manuscript discusses in Section 4.
-/

namespace Philosophy.PID_05

/-- Things, of whatever kind. -/
axiom Thing : Type

/-- You: the referent of the first-person pronoun as used by the reader. -/
axiom you : Thing

/-- Definition 2.1. Being a (human) organism. -/
axiom Organism : Thing → Prop

/-- `Thinks x`: `x` thinks your present thoughts (non-derivatively). -/
axiom Thinks : Thing → Prop

/-- Definition 2.2. Being a person at the later time (phase sortal). -/
axiom PersonLater : Thing → Prop

/-- Existing at the later time. -/
axiom ExistsLater : Thing → Prop

/-- Being, at the later time, a brain wholly located in the vat. -/
axiom VatOccupant : Thing → Prop

/-- Being, at the later time, a living organism. -/
axiom LivingOrganismLater : Thing → Prop

/-- Psychological continuity between you now and a later thing. -/
axiom PsychContinuous : Thing → Thing → Prop

/-- Definition 2.3. To survive as the brain in the vat is to exist later as
the vat occupant; a vat occupant exists at the later time. -/
axiom definition_2_3 : ∀ x, VatOccupant x → ExistsLater x

/-- Assumption 2.4. There is an organism that thinks your thoughts. -/
axiom assumption_2_4 : ∃ o, Organism o ∧ Thinks o

/-- Assumption 2.5. Your thoughts have at most one (non-derivative) thinker. -/
axiom assumption_2_5 : ∀ x y, Thinks x → Thinks y → x = y

/-- Assumption 2.6. You think your thoughts. -/
axiom assumption_2_6 : Thinks you

/-- Assumption 2.7. An organism exists at a later time only if it is then a
living organism. -/
axiom assumption_2_7 : ∀ x, Organism x → ExistsLater x → LivingOrganismLater x

/-- Assumption 2.8. The brain in the vat is not a living organism. -/
axiom assumption_2_8 : ∀ x, VatOccupant x → ¬ LivingOrganismLater x

/-- Assumption 2.9. The vat occupant is a person psychologically continuous
with you. -/
axiom assumption_2_9 : ∃ y, VatOccupant y ∧ PersonLater y ∧ PsychContinuous you y

/-- Theorem 3.1. You are an organism. -/
theorem you_are_organism : Organism you := by
  obtain ⟨o, ho, hto⟩ := assumption_2_4
  have h : o = you := assumption_2_5 o you hto assumption_2_6
  exact h ▸ ho

/-- Theorem 3.2. You would not survive as a brain in a vat. -/
theorem not_vat_survivor : ¬ VatOccupant you := fun hv =>
  assumption_2_8 you hv
    (assumption_2_7 you you_are_organism (definition_2_3 you hv))

/-- Corollary 3.3. There is later a person psychologically continuous with
you who is not you. -/
theorem continuant_not_you :
    ∃ y, PersonLater y ∧ PsychContinuous you y ∧ y ≠ you := by
  obtain ⟨y, hv, hp, hc⟩ := assumption_2_9
  refine ⟨y, hp, hc, ?_⟩
  intro h
  exact not_vat_survivor (h ▸ hv)

end Philosophy.PID_05

#print axioms Philosophy.PID_05.not_vat_survivor
#print axioms Philosophy.PID_05.continuant_not_you
