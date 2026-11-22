/-
PID-11 · Perdurantism and Persons
Formalization of Theorem 3.3 and Corollary 3.4.

Accounts of persistence are represented by an inductive type with five
constructors: perdurance, and four rivals (endurance with time-relative
properties, presentist endurance, adverbial endurance, and the stage view).
That these five exhaust the serious options is Assumption 2.4, encoded in the
type itself. The four adequacy conditions are Principles P1 to P4.

What this file establishes. Given the verdicts of Lemmas 3.1 and 3.2 (which
the manuscript argues for informally and which enter here as premises),
perdurance is the only account that satisfies all four principles
(Theorem 3.3); given in addition that the true account satisfies them
(Assumption 2.5) and Definition 2.2, every person has a temporal part at
every time at which it exists (Corollary 3.4).

What it does not establish. It does not establish the principles, the
verdicts of the lemmas, or the exhaustiveness of the list. It does not model
which sums of stages compose persons (Definition 2.3).
-/

namespace Philosophy.PID_11

/-- Assumption 2.4. The accounts of persistence. -/
inductive Account where
  | perdurance
  | relational
  | presentist
  | adverbial
  | stage
  deriving DecidableEq

/-- Principles P1 (monadic intrinsics), P2 (reality of the past),
P3 (having simpliciter), P4 (extended subjects). -/
inductive Principle where
  | monadic
  | pastReal
  | simpliciter
  | extended

/-- `Satisfies a p`: account `a` satisfies principle `p`. -/
axiom Satisfies : Account → Principle → Prop

/-- Lemma 3.1 (premise here). Each rival violates one principle. -/
axiom lemma_3_1_relational : ¬ Satisfies .relational .monadic
axiom lemma_3_1_presentist : ¬ Satisfies .presentist .pastReal
axiom lemma_3_1_adverbial : ¬ Satisfies .adverbial .simpliciter
axiom lemma_3_1_stage : ¬ Satisfies .stage .extended

/-- Lemma 3.2 (premise here). Perdurance satisfies every principle. -/
axiom lemma_3_2 : ∀ p, Satisfies .perdurance p

/-- An account is adequate if it satisfies P1 to P4. -/
def Adequate (a : Account) : Prop := ∀ p, Satisfies a p

/-- Theorem 3.3. Perdurance is the unique adequate account. -/
theorem unique_adequate (a : Account) : Adequate a ↔ a = .perdurance := by
  constructor
  · intro h
    cases a with
    | perdurance => rfl
    | relational => exact absurd (h .monadic) lemma_3_1_relational
    | presentist => exact absurd (h .pastReal) lemma_3_1_presentist
    | adverbial => exact absurd (h .simpliciter) lemma_3_1_adverbial
    | stage => exact absurd (h .extended) lemma_3_1_stage
  · intro h
    subst h
    exact lemma_3_2

/-- The true account of the persistence of persons. -/
axiom trueAccount : Account

/-- Assumption 2.5. The true account is adequate. -/
axiom assumption_2_5 : Adequate trueAccount

/-- Persons, times, and stages. -/
axiom Person : Type
axiom Time : Type
axiom Stage : Type
axiom ExistsAt : Person → Time → Prop
axiom TemporalPartAt : Stage → Person → Time → Prop

/-- Definition 2.2. If perdurance is the true account, every person has a
temporal part at every time at which it exists. -/
axiom definition_2_2 : trueAccount = .perdurance →
  ∀ x t, ExistsAt x t → ∃ s, TemporalPartAt s x t

/-- Corollary 3.4. Persons have temporal parts. -/
theorem persons_have_temporal_parts :
    ∀ x t, ExistsAt x t → ∃ s, TemporalPartAt s x t :=
  definition_2_2 ((unique_adequate trueAccount).mp assumption_2_5)

end Philosophy.PID_11

#print axioms Philosophy.PID_11.unique_adequate
#print axioms Philosophy.PID_11.persons_have_temporal_parts
