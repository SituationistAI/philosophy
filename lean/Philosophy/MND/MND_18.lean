/-
MND-18 · The Combination Problem Is Unsolvable
Formalization of Sections 2-4 of MND-18-a.

What this file establishes. From Principles P1 (Inclusion), P2 (Ownership)
and P3 (Exclusivity): no experience of any subject is grounded in the
experiences of other subjects (Lemma 3.1). Adding that there is a
non-fundamental subject with an experience (Assumption 2.5), that under
panpsychism such experience is grounded in fundamental natures (clause (b)
of Definition 2.2) and that this grounding is then grounding in others
(Assumption 2.6): panpsychism is false (Theorem 3.2). It also exhibits a
model in which P1-P3 hold, a non-fundamental subject has an experience
grounded in fundamental natures, and nothing is grounded in others: the
consistency half of Proposition 4.1 (protophenomenal monism).

What it does not establish. It does not establish the principles or the
assumptions, and it does not analyse grounding, parthood or belonging,
which are primitives.
-/

namespace Philosophy.MND_18

/-- Experiences (Definition 2.1). -/
axiom Exp : Type
/-- Subjects (Definition 2.1). -/
axiom Subj : Type
/-- `Of e S`: experience `e` belongs to subject `S` (Definition 2.1). -/
axiom Of : Exp → Subj → Prop
/-- `PartOf f e`: experience `f` is a part of experience `e`. -/
axiom PartOf : Exp → Exp → Prop
/-- Being a fundamental entity. -/
axiom Fundamental : Subj → Prop
/-- `e` is fully grounded in the intrinsic natures of fundamental entities. -/
axiom GroundedInNatures : Exp → Prop
/-- Definition 2.4. `e`, an experience of `S`, is fully grounded in
experiences of subjects distinct from `S`. -/
axiom GroundedInOthers : Exp → Subj → Prop
/-- Panpsychism (Definition 2.2). -/
axiom Panpsychism : Prop

/-- Principle P1 (Inclusion). -/
axiom principle_P1 : ∀ e S, Of e S → GroundedInOthers e S →
  ∃ f T, T ≠ S ∧ Of f T ∧ (PartOf f e ∨ PartOf e f)
/-- Principle P2 (Ownership). -/
axiom principle_P2 : ∀ f e S, PartOf f e → Of e S → Of f S
/-- Principle P3 (Exclusivity). -/
axiom principle_P3 : ∀ e S T, Of e S → Of e T → S = T
/-- Assumption 2.5 (Macro-subjects). -/
axiom assumption_2_5 : ∃ e S, Of e S ∧ ¬ Fundamental S
/-- Definition 2.2, clause (b): under panpsychism, every experience of a
non-fundamental subject is fully grounded in fundamental natures. -/
axiom definition_2_2_b : Panpsychism →
  ∀ e S, Of e S → ¬ Fundamental S → GroundedInNatures e
/-- Assumption 2.6 (Panpsychist grounding). -/
axiom assumption_2_6 : Panpsychism →
  ∀ e S, Of e S → ¬ Fundamental S → GroundedInNatures e → GroundedInOthers e S

/-- Lemma 3.1 (No subject-summing). -/
theorem no_subject_summing : ∀ e S, Of e S → ¬ GroundedInOthers e S := by
  intro e S hOf hG
  obtain ⟨f, T, hne, hfT, hpart⟩ := principle_P1 e S hOf hG
  cases hpart with
  | inl h => exact hne (principle_P3 f T S hfT (principle_P2 f e S h hOf))
  | inr h => exact hne (principle_P3 e T S (principle_P2 e f T h hfT) hOf)

/-- Theorem 3.2. Panpsychism is false. -/
theorem panpsychism_false : ¬ Panpsychism := by
  intro hP
  obtain ⟨e, S, hOf, hnf⟩ := assumption_2_5
  exact no_subject_summing e S hOf
    (assumption_2_6 hP e S hOf hnf (definition_2_2_b hP e S hOf hnf))

/-- A frame for the consistency half of Proposition 4.1. -/
structure Frame where
  E : Type
  S : Type
  of : E → S → Prop
  part : E → E → Prop
  fund : S → Prop
  natures : E → Prop
  others : E → S → Prop

/-- The principles and the protophenomenal situation, as conditions on a frame. -/
def ProtoModel (F : Frame) : Prop :=
  (∀ e s, F.of e s → F.others e s →
      ∃ f t, t ≠ s ∧ F.of f t ∧ (F.part f e ∨ F.part e f)) ∧
  (∀ f e s, F.part f e → F.of e s → F.of f s) ∧
  (∀ e s t, F.of e s → F.of e t → s = t) ∧
  (∃ e s, F.of e s ∧ ¬ F.fund s ∧ F.natures e) ∧
  (∀ e s, ¬ F.others e s)

/-- One experience, one non-fundamental subject, grounded in protophenomenal
natures, nothing grounded in others. -/
def protoFrame : Frame :=
  { E := Unit, S := Unit, of := fun _ _ => True, part := fun _ _ => True,
    fund := fun _ => False, natures := fun _ => True, others := fun _ _ => False }

/-- Proposition 4.1 (consistency half). -/
theorem proposition_4_1 : ProtoModel protoFrame := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ h; exact h.elim
  · intro _ _ _ _ _; trivial
  · intro _ _ _ _ _; rfl
  · exact ⟨(), (), trivial, fun h => h, trivial⟩
  · intro _ _ h; exact h

end Philosophy.MND_18

#print axioms Philosophy.MND_18.panpsychism_false
#print axioms Philosophy.MND_18.proposition_4_1
