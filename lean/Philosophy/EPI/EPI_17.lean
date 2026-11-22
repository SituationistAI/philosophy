/-
EPI-17 · Uniqueness Defended
Formalization of Theorem 3.1, Corollary 3.2 and Proposition 3.3.

`EI c d` is the expected inaccuracy of credence `d` in a fixed proposition, as
computed by the lights of credence `c`. `Rational E c` says that credence `c` is
rational on the body of evidence `E`.

What this file establishes. If accuracy is measured by a strictly proper
measure (Principle P1) and every credence rational on a body of evidence is, by
the lights of any credence rational on it, expected to be no less accurate
(Principle P2), then for any body of evidence at most one credence is rational
(Theorem 3.1), so there are no permissive cases (Corollary 3.2). The Brier
measure on a grid of eleven credences is strictly proper (Proposition 3.3), so
Principle P1 is satisfiable.

What it does not establish. Principle P2, which is defended in Section 4 of
the manuscript; nor that some credence is rational on every body of evidence;
nor which credence that is.
-/

namespace Philosophy.EPI_17

/-- Bodies of evidence. -/
axiom Evidence : Type
/-- Credences in a fixed proposition. -/
axiom Credence : Type

/-- Definition 2.1. `Rational E c`: credence `c` is rational on evidence `E`. -/
axiom Rational : Evidence → Credence → Prop

/-- Definition 2.2. `EI c d`: expected inaccuracy of `d` by the lights of `c`. -/
axiom EI : Credence → Credence → Int

/-- Principle P1 (strict propriety). Every credence expects itself to be
strictly more accurate than any other. -/
axiom strict_propriety : ∀ c d : Credence, c ≠ d → EI c c < EI c d

/-- Principle P2 (rational endorsement). A credence rational on `E` expects any
credence rational on `E` to be no less accurate than itself. -/
axiom endorsement :
  ∀ (E : Evidence) (c d : Credence), Rational E c → Rational E d → EI c d ≤ EI c c

/-- Theorem 3.1 (uniqueness). -/
theorem uniqueness (E : Evidence) (c d : Credence)
    (hc : Rational E c) (hd : Rational E d) : c = d :=
  Classical.byContradiction fun hne =>
    Int.lt_irrefl _ (Int.lt_of_lt_of_le (strict_propriety c d hne) (endorsement E c d hc hd))

/-- Corollary 3.2. There is no permissive case. -/
theorem no_permissive_case :
    ¬ ∃ (E : Evidence) (c d : Credence), c ≠ d ∧ Rational E c ∧ Rational E d :=
  fun ⟨E, c, d, hne, hc, hd⟩ => hne (uniqueness E c d hc hd)

/-! Proposition 3.3: the Brier measure on the grid 0, 1/10, ..., 1. -/

/-- Expected Brier inaccuracy of credence `d/10` by the lights of `c/10`,
multiplied by 100. -/
def brier (c d : Nat) : Nat :=
  c * ((10 - d) * (10 - d)) + (10 - c) * (d * d)

/-- Proposition 3.3. The Brier measure is strictly proper on the grid. -/
theorem brier_strictly_proper :
    ∀ c d : Fin 11, c ≠ d → brier c c < brier c d := by
  decide

end Philosophy.EPI_17

#print axioms Philosophy.EPI_17.uniqueness
#print axioms Philosophy.EPI_17.brier_strictly_proper
