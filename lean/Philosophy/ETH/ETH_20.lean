/-
ETH-20 · The Asymmetry Argument Fails
Formalization of Proposition 3.1, Theorem 3.2, Lemma 3.3, Corollary 3.4,
Proposition 3.5 and Theorem 3.6.

A possible life is described by the amount of good and of bad it would
contain (Definition 2.1). Benatar's argument compares, column by column,
the scenario in which the person exists with the scenario in which she
never exists. A column verdict is an integer: its sign says which scenario
the column favors (positive: existence; negative: non-existence; zero:
neither). Each column is evaluated by a standard (Definition 2.2): the
personal standard, on which a state of affairs is good or bad only if it is
good or bad for someone, and the impersonal standard, on which it is good or
bad simpliciter. Benatar's own evaluation (Definition 2.3) evaluates the
pain column impersonally and the pleasure column personally.

What this file establishes. Benatar's dominance argument is valid on his
evaluation (Proposition 3.1). On either uniform standard, dominance favors
non-existence only for lives containing no good (Theorem 3.2). Given that
both columns are evaluated by one standard (Principle P1) and that the
absence of pain is good, as Benatar holds (Assumption 2.5), the standard is
the impersonal one (Lemma 3.3), so the absence of pleasure is not neutral
(Corollary 3.4). Given Principle P2, creating a person whose life would
contain at least as much good as bad is not wrong on the child-regarding
ground (Theorem 3.6).

What it does not establish. It does not establish the premises, nor that
actual lives contain more good than bad. It does not address objections to
procreation from consent (ETH-20-b) or from the effects of a child's
existence on others.
-/

namespace Philosophy.ETH_20

/-- Definition 2.1. A possible life: the good and the bad it would
contain. -/
structure Life where
  good : Nat
  bad : Nat

/-- Definition 2.2. Standards of evaluation. -/
inductive Standard
  | personal
  | impersonal
  deriving DecidableEq

/-- Definition 2.2 (pain column). Verdict of a standard on the pain column:
under the personal standard the absence of pain is good for no one, so
neither scenario is favored; under the impersonal standard pain is bad and
its absence good, so non-existence is favored by the amount of bad. -/
def painColumn : Standard → Life → Int
  | .personal, _ => 0
  | .impersonal, l => -(l.bad : Int)

/-- Definition 2.2 (pleasure column). -/
def pleasureColumn : Standard → Life → Int
  | .personal, _ => 0
  | .impersonal, l => (l.good : Int)

/-- Definition 2.4. Dominance: non-existence is favored in some column and
existence in none. -/
def NonExistenceDominates (c1 c2 : Int) : Prop :=
  (c1 < 0 ∨ c2 < 0) ∧ c1 ≤ 0 ∧ c2 ≤ 0

/-- Definition 2.3. Benatar's evaluation: pain column impersonal, pleasure
column personal. -/
def benatarPain (l : Life) : Int := painColumn .impersonal l
def benatarPleasure (l : Life) : Int := pleasureColumn .personal l

/-- Proposition 3.1. On Benatar's evaluation, non-existence dominates for
every life containing any bad. -/
theorem benatar_valid (l : Life) (h : l.bad > 0) :
    NonExistenceDominates (benatarPain l) (benatarPleasure l) := by
  simp only [NonExistenceDominates, benatarPain, benatarPleasure,
    painColumn, pleasureColumn]
  omega

/-- Theorem 3.2. On either uniform standard, non-existence dominates only
for lives containing no good. -/
theorem uniform_blocks (s : Standard) (l : Life)
    (h : NonExistenceDominates (painColumn s l) (pleasureColumn s l)) :
    l.good = 0 := by
  cases s with
  | personal =>
    simp only [NonExistenceDominates, painColumn, pleasureColumn] at h
    omega
  | impersonal =>
    simp only [NonExistenceDominates, painColumn, pleasureColumn] at h
    omega

/-- Principle P1 (parity). There is one standard by which both columns are
correctly evaluated: the correct verdicts are `painColumn std` and
`pleasureColumn std`, for one and the same `std`. -/
axiom std : Standard

/-- Assumption 2.5 (Benatar's first claim). The absence of pain is good: for a
life containing bad, the pain column favors non-existence. -/
axiom absence_of_pain_good : ∀ l : Life, l.bad > 0 → painColumn std l < 0

/-- Lemma 3.3. The standard is the impersonal one. -/
theorem std_impersonal : std = .impersonal := by
  have h := absence_of_pain_good ⟨0, 1⟩ (by decide)
  cases hs : std with
  | personal => rw [hs] at h; simp [painColumn] at h
  | impersonal => rfl

/-- Corollary 3.4. The absence of pleasure is not neutral: for a life
containing good, the pleasure column favors existence; and the dominance
argument fails for every such life. -/
theorem absence_not_neutral (l : Life) (h : l.good > 0) :
    pleasureColumn std l > 0 ∧
    ¬ NonExistenceDominates (painColumn std l) (pleasureColumn std l) := by
  refine ⟨?_, fun hd => ?_⟩
  · rw [std_impersonal]; simp only [pleasureColumn]; omega
  · have := uniform_blocks std l hd; omega

/-- Proposition 3.5. Under the impersonal standard, the sum of the column
verdicts favors existence exactly when the life contains more good than
bad. -/
theorem overall (l : Life) :
    painColumn .impersonal l + pleasureColumn .impersonal l > 0 ↔ l.good > l.bad := by
  simp only [painColumn, pleasureColumn]
  omega

/-- Creating a person who would live this life is wrong on the
child-regarding ground. -/
axiom WrongToCreate : Life → Prop

/-- Principle P2. Creating a person is wrong on the child-regarding ground
only if the column verdicts, correctly evaluated, sum to a verdict favoring
non-existence. -/
axiom wrong_only_if_worse :
    ∀ l, WrongToCreate l → painColumn std l + pleasureColumn std l < 0

/-- Theorem 3.6 (main result). Creating a person whose life would contain at
least as much good as bad is not wrong on the child-regarding ground, and
for any life containing good the asymmetry argument fails. -/
theorem not_wrong (l : Life) (h : l.good ≥ l.bad) :
    ¬ WrongToCreate l ∧
    (l.good > 0 → ¬ NonExistenceDominates (painColumn std l) (pleasureColumn std l)) := by
  refine ⟨fun hw => ?_, fun hg => (absence_not_neutral l hg).2⟩
  have h1 := wrong_only_if_worse l hw
  rw [std_impersonal] at h1
  simp only [painColumn, pleasureColumn] at h1
  omega

end Philosophy.ETH_20

#print axioms Philosophy.ETH_20.benatar_valid
#print axioms Philosophy.ETH_20.uniform_blocks
#print axioms Philosophy.ETH_20.absence_not_neutral
#print axioms Philosophy.ETH_20.not_wrong
