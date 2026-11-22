/-
MND-01 · On the Hard Problem of Consciousness
Formalization of Volume I, Chapter 4: Theorem 4.2 and Corollaries 4.3–4.4.

The two-dimensional argument against materialism (Chalmers 2009) is
represented propositionally. `Conceivable`, `PrimarilyPossible` and
`SecondarilyPossible` concern the zombie hypothesis P ∧ ¬Q, where P is the
conjunction of the microphysical truths and Q a phenomenal truth.

What this file establishes. From the premises of the two-dimensional
argument, the disjunction "materialism is false or Russellian monism is
true" follows; with materialism in the extended sense of MND-02, Russellian
monism follows, and the zombie hypothesis is primarily but not secondarily
possible. It does not establish the premises of the two-dimensional
argument, which are defended in Chapters 2 and 3, nor materialism.
-/

namespace Philosophy.MND_01

/-- The zombie hypothesis P ∧ ¬Q is ideally conceivable. -/
axiom Conceivable : Prop
/-- P ∧ ¬Q is true at some world considered as actual (primary possibility). -/
axiom PrimarilyPossible : Prop
/-- P ∧ ¬Q is true at some world considered as counterfactual (secondary possibility). -/
axiom SecondarilyPossible : Prop
/-- Materialism: every positive truth is necessitated by P. -/
axiom Materialism : Prop
/-- Russellian monism: the intrinsic natures that physics describes only
structurally are phenomenal or protophenomenal. -/
axiom RussellianMonism : Prop

/-- Premise 4.1 (a). The zombie hypothesis is ideally conceivable. -/
axiom conceivable : Conceivable
/-- Premise 4.1 (b). Ideal conceivability entails primary possibility. -/
axiom cp : Conceivable → PrimarilyPossible
/-- Premise 4.1 (c). Primary possibility entails secondary possibility,
unless physical terms pick out intrinsic natures not fixed by their
structural roles, which is Russellian monism. -/
axiom primary_secondary : PrimarilyPossible → SecondarilyPossible ∨ RussellianMonism
/-- Premise 4.1 (d). If the zombie hypothesis is secondarily possible,
materialism is false. -/
axiom secondary_refutes : SecondarilyPossible → ¬ Materialism

/-- Theorem 4.2. Materialism is false or Russellian monism is true. -/
theorem dilemma : ¬ Materialism ∨ RussellianMonism :=
  match primary_secondary (cp conceivable) with
  | Or.inl h => Or.inl (secondary_refutes h)
  | Or.inr h => Or.inr h

/-- Corollary 4.3. Given materialism (MND-02), Russellian monism is true. -/
theorem russellian (m : Materialism) : RussellianMonism :=
  match dilemma with
  | Or.inl h => absurd m h
  | Or.inr h => h

/-- Corollary 4.4. Given materialism, the zombie hypothesis is primarily
possible but not secondarily possible: the gap lies between two modes of
presentation, not between two sets of facts. -/
theorem gap (m : Materialism) : PrimarilyPossible ∧ ¬ SecondarilyPossible :=
  ⟨cp conceivable, fun h => secondary_refutes h m⟩

end Philosophy.MND_01

#print axioms Philosophy.MND_01.dilemma
#print axioms Philosophy.MND_01.gap
