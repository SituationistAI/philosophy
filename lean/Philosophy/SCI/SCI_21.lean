/-
SCI-21 · Survival of the Fittest Is Not a Tautology
Formalization of Propositions 3.1, 3.2 and 3.3.

A selection scenario has finitely many possible outcomes, each with a
chance (on a natural-number scale) and a number of offspring for each of
two types A and B; one outcome is actual. Record fitness compares the
actual offspring numbers (Definition 2.1). Propensity fitness compares the
expected offspring numbers, the chance-weighted sums over all outcomes
(Definition 2.2).

What this file establishes. With record fitness, "the fitter type leaves
more offspring" holds in every scenario: it is a logical truth. With
propensity fitness it fails in some scenario, and propensity fitness is not
fixed by the actual record: two scenarios with the same actual outcome can
rank the types in opposite ways.

What it does not establish. It does not establish that fitness is a
propensity, which is argued in the manuscript, nor that actual fitness
differences explain actual evolutionary change; nor does it model the
grounding of chances in traits and environment. The module uses no axioms
beyond Lean's core logic: the philosophical content lies in the choice
between the two definitions, which is the thesis under discussion.
-/

namespace Philosophy.SCI_21

/-- A selection scenario with `size` possible outcomes. -/
structure Scenario where
  size : Nat
  chance : Nat → Nat
  offA : Nat → Nat
  offB : Nat → Nat
  actual : Nat

/-- Sum of `f 0, …, f (n-1)`. -/
def total (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => total f k + f k

/-- Definition 2.1. A is record-fitter than B: A actually left more offspring. -/
def RecordFitter (s : Scenario) : Prop := s.offA s.actual > s.offB s.actual

/-- Expected offspring of a type, on the chance scale. -/
def expected (s : Scenario) (off : Nat → Nat) : Nat :=
  total (fun o => s.chance o * off o) s.size

/-- Definition 2.2. A is propensity-fitter than B: A's expected offspring
number exceeds B's. -/
def PropensityFitter (s : Scenario) : Prop := expected s s.offA > expected s s.offB

/-- The principle of the survival of the fittest, relative to a notion of
fitness: if A is fitter, A actually leaves more offspring. -/
def SurvivalOfFittest (Fitter : Scenario → Prop) (s : Scenario) : Prop :=
  Fitter s → s.offA s.actual > s.offB s.actual

/-- Proposition 3.1. With record fitness, the principle holds in every
scenario. -/
theorem record_tautology (s : Scenario) : SurvivalOfFittest RecordFitter s :=
  fun h => h

/-- A scenario: outcome 0 (chance 9) gives A three offspring and B one;
outcome 1 (chance 1) gives A none and B two. Outcome 1 is actual. -/
def unlucky : Scenario :=
  { size := 2, chance := fun o => if o = 0 then 9 else 1,
    offA := fun o => if o = 0 then 3 else 0,
    offB := fun o => if o = 0 then 1 else 2, actual := 1 }

/-- The same outcomes and actual outcome, with the chances reversed. -/
def reversed : Scenario :=
  { unlucky with chance := fun o => if o = 0 then 1 else 9 }

/-- Proposition 3.2. With propensity fitness, the principle fails in some
scenario. -/
theorem propensity_not_tautology :
    ∃ s, ¬ SurvivalOfFittest PropensityFitter s :=
  ⟨unlucky, fun h => absurd (h (by unfold PropensityFitter; decide)) (by decide)⟩

/-- Proposition 3.3. Propensity fitness is not fixed by the record: two
scenarios agree on the actual offspring numbers but rank A and B oppositely. -/
theorem propensity_not_record :
    ∃ s t : Scenario,
      s.offA s.actual = t.offA t.actual ∧ s.offB s.actual = t.offB t.actual ∧
      PropensityFitter s ∧ ¬ PropensityFitter t :=
  ⟨unlucky, reversed, rfl, rfl, by unfold PropensityFitter; decide,
   by unfold PropensityFitter; decide⟩

end Philosophy.SCI_21

#print axioms Philosophy.SCI_21.record_tautology
#print axioms Philosophy.SCI_21.propensity_not_tautology
#print axioms Philosophy.SCI_21.propensity_not_record
