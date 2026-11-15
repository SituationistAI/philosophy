/-
LNG-07 · Against Private Language
Formalization of Theorems 3.1 and 3.3, Corollary 3.2 and Proposition 3.4.

A rule is private to a speaker if no one other than the speaker could know
it (Definition 2.1). Following a rule requires a standard of correctness
independent of how things seem to the follower (Assumption 2.3); any such
standard is one that someone other than the follower could come to know,
and so makes the rule knowable by another (Assumption 2.4); and
communicating by a rule requires that the hearer, who is someone other than
the speaker, could know it (Assumption 2.5).

What this file establishes. No speaker follows a rule private to her
(Theorem 3.1); no one communicates by such a rule (Corollary 3.2); the two
together give Theorem 3.3. Proposition 3.4 exhibits a model in which the
assumptions hold and a speaker follows a rule that, as it happens, only she
knows: the argument does not exclude a solitary language, only a private one.

What it does not establish. It does not establish Assumptions 2.3 and 2.4,
which the manuscript defends in Section 4, and it does not deny that there
are private sensations.
-/

namespace Philosophy.LNG_07

/-- Speakers, actual and possible. -/
axiom Agent : Type

/-- Rules of use. -/
axiom Rule : Type

/-- `CouldKnow a r`: it is possible for `a` to know what rule `r` requires. -/
axiom CouldKnow : Agent → Rule → Prop

/-- Definition 2.1. A rule is private to `s` if no one other than `s` could know it. -/
def Private (r : Rule) (s : Agent) : Prop := ∀ a, CouldKnow a r → a = s

/-- `Follows s r`: `s` follows rule `r`. -/
axiom Follows : Agent → Rule → Prop

/-- Definition 2.2. `Standard s r`: there is a standard of correctness for `s`'s
applications of `r` that is independent of how things seem to `s`. -/
axiom Standard : Agent → Rule → Prop

/-- `Communicates s h r`: `s` communicates with `h` by means of rule `r`. -/
axiom Communicates : Agent → Agent → Rule → Prop

/-- Assumption 2.3. Following a rule requires an independent standard. -/
axiom following_requires_standard : ∀ s r, Follows s r → Standard s r

/-- Assumption 2.4. An independent standard makes the rule knowable by
someone other than the follower. -/
axiom standard_shareable : ∀ s r, Standard s r → ∃ a, a ≠ s ∧ CouldKnow a r

/-- Assumption 2.5. Communication by a rule is with someone other than the
speaker, who could know the rule. -/
axiom communication_requires_knowledge :
  ∀ s h r, Communicates s h r → h ≠ s ∧ CouldKnow h r

/-- Theorem 3.1. No speaker follows a rule private to her. -/
theorem private_not_followed (s : Agent) (r : Rule) (hp : Private r s) :
    ¬ Follows s r := fun hf =>
  let ⟨a, hne, hk⟩ := standard_shareable s r (following_requires_standard s r hf)
  hne (hp a hk)

/-- Corollary 3.2. No one communicates by a rule private to her. -/
theorem private_not_communicable (s : Agent) (r : Rule) (hp : Private r s) :
    ∀ h, ¬ Communicates s h r := fun h hc =>
  let ⟨hne, hk⟩ := communication_requires_knowledge s h r hc
  hne (hp h hk)

/-- Theorem 3.3 (main result). A rule private to its speaker can neither be
followed nor used to communicate. -/
theorem no_private_language (s : Agent) (r : Rule) (hp : Private r s) :
    ¬ Follows s r ∧ ∀ h, ¬ Communicates s h r :=
  ⟨private_not_followed s r hp, private_not_communicable s r hp⟩

/-- A model of the framework, with actual as well as possible knowledge. -/
structure Model where
  Agent : Type
  Rule : Type
  couldKnow : Agent → Rule → Prop
  knows : Agent → Rule → Prop
  follows : Agent → Rule → Prop
  standard : Agent → Rule → Prop

/-- Proposition 3.4 (Crusoe). There is a model satisfying Assumptions 2.3 and
2.4 in which a speaker follows a rule that only she actually knows. -/
theorem crusoe : ∃ M : Model, ∃ (s : M.Agent) (r : M.Rule),
    (∀ s r, M.follows s r → M.standard s r) ∧
    (∀ s r, M.standard s r → ∃ a, a ≠ s ∧ M.couldKnow a r) ∧
    M.follows s r ∧ (∀ a, M.knows a r → a = s) := by
  refine ⟨⟨Bool, Unit, fun _ _ => True, fun a _ => a = true,
    fun a _ => a = true, fun a _ => a = true⟩, true, (), ?_, ?_, rfl, fun _ h => h⟩
  · intro _ _ h; exact h
  · intro s _ _
    exact ⟨!s, by cases s <;> decide, trivial⟩

end Philosophy.LNG_07

#print axioms Philosophy.LNG_07.no_private_language
#print axioms Philosophy.LNG_07.crusoe
