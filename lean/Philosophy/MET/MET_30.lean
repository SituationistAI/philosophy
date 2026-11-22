/-
MET-30 · On the Possibility of Metaphysics
Formalization of Theorem 3.1 and Corollary 3.2.

Questions are primitive, as are the predicates of being metaphysical, having
a determinate answer, being answerable trivially within a linguistic
framework, being merely verbal, and being internal to a framework. A question
is substantive if it is neither trivial nor merely verbal (Definition 2.1).
Metaphysics is possible as a discipline with determinate answers if some
metaphysical question is determinate and substantive (Definition 2.3).

What this file establishes. Given that the questions of MET-03 and MET-28
are metaphysical, determinate and substantive (Assumption 2.4), metaphysics
is possible and general deflationism is false (Theorem 3.1); Carnap's
dichotomy, Hirsch's verbalism, its extension to all metaphysical questions,
and anti-realism about ontological questions, in their general forms, are
each false (Corollary 3.2). It does not establish
Assumption 2.4, which rests on the arguments of those manuscripts and of
Section 3, and it does not establish that every metaphysical question is
determinate.
-/

namespace Philosophy.MET_30

/-- Questions. -/
axiom Question : Type

/-- The question is metaphysical. -/
axiom Metaphysical : Question → Prop

/-- The question is ontological (a question about what there is). -/
axiom Ontological : Question → Prop

/-- Definition 2.2. The question has a determinate answer. -/
axiom Determinate : Question → Prop

/-- The question is internal to a linguistic framework. -/
axiom Internal : Question → Prop

/-- The question is answerable trivially, by the rules of a framework. -/
axiom Trivial : Question → Prop

/-- The question is merely verbal. -/
axiom Verbal : Question → Prop

/-- Definition 2.1. A question is substantive if it is neither trivial nor
merely verbal. -/
def Substantive (q : Question) : Prop := ¬ Trivial q ∧ ¬ Verbal q

/-- Definition 2.3. Metaphysics is possible as a discipline with determinate
answers. -/
def MetaphysicsPossible : Prop :=
  ∃ q, Metaphysical q ∧ Determinate q ∧ Substantive q

/-- Definition 2.3. General deflationism. -/
def Deflationism : Prop :=
  ∀ q, Metaphysical q → ¬ (Determinate q ∧ Substantive q)

/-- The question of MET-03 (does the external world exist?) and that of
MET-28 (is the identity of indiscernibles true?). -/
axiom q03 : Question
axiom q28 : Question

/-- Assumption 2.4 (witnesses). The question of MET-03 is ontological,
metaphysical, determinate, not trivial and not verbal. -/
axiom w03 : Ontological q03 ∧ Metaphysical q03 ∧ Determinate q03 ∧
  ¬ Trivial q03 ∧ ¬ Verbal q03

/-- Assumption 2.4 (witnesses). The question of MET-28, in each of its
disambiguations, is metaphysical, determinate, not trivial and not verbal. -/
axiom w28 : Metaphysical q28 ∧ Determinate q28 ∧ ¬ Trivial q28 ∧ ¬ Verbal q28

/-- Theorem 3.1 (main result). Metaphysics is possible, and general
deflationism is false. -/
theorem metaphysics_possible : MetaphysicsPossible ∧ ¬ Deflationism :=
  have ⟨_, m, d, t, v⟩ := w03
  ⟨⟨q03, m, d, t, v⟩, fun h => h q03 m ⟨d, t, v⟩⟩

/-- Carnap's dichotomy: every metaphysical question is either internal and
trivial, or external and without a determinate (theoretical) answer. -/
def CarnapDichotomy : Prop :=
  ∀ q, Metaphysical q → (Internal q ∧ Trivial q) ∨ (¬ Internal q ∧ ¬ Determinate q)

/-- Hirsch's verbalism: every ontological question is merely verbal. -/
def Verbalism : Prop := ∀ q, Ontological q → Verbal q

/-- Verbalism extended beyond ontology: every metaphysical question is
merely verbal. -/
def GeneralVerbalism : Prop := ∀ q, Metaphysical q → Verbal q

/-- Anti-realism about ontology, generalized: no ontological question is
determinate. -/
def OntologicalAntiRealism : Prop := ∀ q, Ontological q → ¬ Determinate q

/-- Corollary 3.2. Carnap's dichotomy, Hirsch's verbalism and its extension
beyond ontology, and anti-realism about ontology, in their general forms,
are false. -/
theorem deflationary_theses_fail :
    ¬ CarnapDichotomy ∧ ¬ Verbalism ∧ ¬ GeneralVerbalism ∧
    ¬ OntologicalAntiRealism := by
  obtain ⟨o, m, d, t, v⟩ := w03
  obtain ⟨m', _, _, v'⟩ := w28
  refine ⟨fun h => ?_, fun h => v (h q03 o), fun h => v' (h q28 m'),
    fun h => h q03 o d⟩
  rcases h q03 m with ⟨_, ht⟩ | ⟨_, hd⟩
  · exact t ht
  · exact hd d

end Philosophy.MET_30

#print axioms Philosophy.MET_30.metaphysics_possible
#print axioms Philosophy.MET_30.deflationary_theses_fail
