/-
MTH-18 · Can Machines Do Philosophy?
Formalization of Proposition 2.1.

What this file establishes. For every proposition C there is a valid
argument for C and a valid argument for its negation. Validity, which is
what a proof checker verifies, therefore does not discriminate between a
thesis and its denial; what discriminates between them is the choice of
premises. It does not establish anything about how premises are, or should
be, chosen.
-/

namespace Philosophy.MTH_18

/-- Proposition 2.1. Every proposition and its negation each follow validly
from some premise. -/
theorem both_ways (C : Prop) : (∃ P : Prop, P → C) ∧ (∃ Q : Prop, Q → ¬ C) :=
  ⟨⟨C, id⟩, ⟨¬ C, id⟩⟩

end Philosophy.MTH_18

#print axioms Philosophy.MTH_18.both_ways
