/-
POL-02 · The Legitimacy of the State
Formalization of Lemmas 4.1 and 4.2, Theorem 4.3, Corollary 4.5 and
Propositions 5.3, 5.5 and 5.6.

A state is legitimate when its coercion of each person subject to it is
permissible (Definition 3.1). Coercion of a person is permissible only if it
is justifiable to her when she is reasonable (Principle P1); justifiability to
a reasonable person suffices for its permissibility (Principle P2); and
coercion of an unreasonable person is permissible when the state is
justifiable to all its reasonable subjects (Principle P3). Every state coerces
every person subject to it (Assumption 3.5).

What this file establishes. Given P1–P3 and Assumption 3.5, a state is
legitimate if and only if it is justifiable to every reasonable person subject
to it (Theorem 4.3); consent of every subject is sufficient but not required
(Proposition 5.3); the criterion is antitone in the class of persons counted
as reasonable, and degenerates at both extremes (Propositions 5.5, 5.6).

What it does not establish. It does not establish P1–P3, the conception of
reasonableness of Definition 3.2, or that any actual state is justifiable to
all its reasonable subjects; Assumption 4.4 is the premise that some state is.
-/

namespace Philosophy.POL_02

/-- Persons. -/
axiom Person : Type

/-- States. -/
axiom State : Type

/-- Definition 3.4. `Subject x s`: `x` is subject to the authority of `s`. -/
axiom Subject : Person → State → Prop

/-- Definition 3.2. `x` is a reasonable person. -/
axiom Reasonable : Person → Prop

/-- Definition 3.3. `Justifiable s x`: the coercive authority of `s` can be
justified to `x` from her own reasonable standpoint. -/
axiom Justifiable : State → Person → Prop

/-- `s` coerces `x`. -/
axiom Coerces : State → Person → Prop

/-- The coercion of `x` by `s` is permissible. -/
axiom Permissible : State → Person → Prop

/-- Definition 3.1. A state is legitimate when its coercion of each person
subject to it is permissible. -/
def Legitimate (s : State) : Prop := ∀ x, Subject x s → Permissible s x

/-- The criterion: `s` is justifiable to every reasonable person subject to it. -/
def JustifiedToAll (s : State) : Prop :=
  ∀ x, Reasonable x → Subject x s → Justifiable s x

/-- Assumption 3.5 (coercion). A state coerces every person subject to it. -/
axiom assumption_3_5 : ∀ s x, Subject x s → Coerces s x

/-- Principle P1 (justification requirement). Coercion of a reasonable person
is permissible only if it is justifiable to her. -/
axiom principle_P1 : ∀ s x, Coerces s x → Reasonable x → Permissible s x →
  Justifiable s x

/-- Principle P2 (sufficiency). Coercion that is justifiable to a reasonable
person is permissible with respect to her. -/
axiom principle_P2 : ∀ s x, Reasonable x → Justifiable s x → Permissible s x

/-- Principle P3 (the unreasonable). If a state is justifiable to all its
reasonable subjects, its coercion of an unreasonable subject is permissible. -/
axiom principle_P3 : ∀ s x, ¬ Reasonable x → JustifiedToAll s → Permissible s x

/-- Lemma 4.1 (necessity). -/
theorem necessity (s : State) : Legitimate s → JustifiedToAll s :=
  fun h x hr hs => principle_P1 s x (assumption_3_5 s x hs) hr (h x hs)

/-- Lemma 4.2 (sufficiency). -/
theorem sufficiency (s : State) : JustifiedToAll s → Legitimate s := by
  intro h x hs
  by_cases hr : Reasonable x
  · exact principle_P2 s x hr (h x hr hs)
  · exact principle_P3 s x hr h

/-- Theorem 4.3. A state is legitimate if and only if it is justifiable to
every reasonable person subject to it. -/
theorem legitimacy_iff (s : State) : Legitimate s ↔ JustifiedToAll s :=
  ⟨necessity s, sufficiency s⟩

/-- Corollary 4.5. Under Assumption 4.4 (some state is justifiable to all its
reasonable subjects), some state is legitimate, and philosophical anarchism,
the thesis that no state is legitimate, is false. -/
theorem not_anarchism (h : ∃ s, JustifiedToAll s) :
    ¬ ∀ s, ¬ Legitimate s :=
  fun hall => match h with
    | ⟨s, hs⟩ => hall s (sufficiency s hs)

/-- Actual consent of `x` to the authority of `s`. -/
axiom Consents : Person → State → Prop

/-- Definition 5.1. The consent criterion. -/
def ConsentLegitimate (s : State) : Prop := ∀ x, Subject x s → Consents x s

/-- Assumption 5.2 (volenti). A state is justifiable to a reasonable person
who has consented to its authority. -/
axiom assumption_5_2 : ∀ s x, Reasonable x → Consents x s → Justifiable s x

/-- Proposition 5.3. Universal consent is sufficient for legitimacy. -/
theorem consent_sufficient (s : State) : ConsentLegitimate s → Legitimate s :=
  fun h => sufficiency s (fun x hr hs => assumption_5_2 s x hr (h x hs))

/-- Definition 5.4. The criterion relative to a standard `R` of reasonableness. -/
def JustifiedTo (R : Person → Prop) (s : State) : Prop :=
  ∀ x, R x → Subject x s → Justifiable s x

/-- Proposition 5.5 (antitonicity). The more persons a standard counts as
reasonable, the fewer states satisfy the criterion. -/
theorem antitone (R R' : Person → Prop) (hsub : ∀ x, R x → R' x) (s : State) :
    JustifiedTo R' s → JustifiedTo R s :=
  fun h x hr hs => h x (hsub x hr) hs

/-- Proposition 5.6 (limiting cases). (a) If every person counts as reasonable
and some person is subject to every state but no state is justifiable to her,
no state satisfies the criterion. (b) If no one counts as reasonable, every
state satisfies it. -/
theorem limiting_cases :
    ((∃ x, ∀ s, Subject x s ∧ ¬ Justifiable s x) →
      ∀ s, ¬ JustifiedTo (fun _ => True) s) ∧
    (∀ s, JustifiedTo (fun _ => False) s) := by
  constructor
  · intro ⟨x, hx⟩ s h
    exact (hx s).2 (h x trivial (hx s).1)
  · intro s x hr _
    exact False.elim hr

end Philosophy.POL_02

#print axioms Philosophy.POL_02.legitimacy_iff
#print axioms Philosophy.POL_02.not_anarchism
#print axioms Philosophy.POL_02.consent_sufficient
#print axioms Philosophy.POL_02.limiting_cases
