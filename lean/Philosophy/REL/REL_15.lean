/-
REL-15 · A Uniqueness Theorem for Maximal Greatness
Formalization of Theorem 3.1.

Revision of 2026-10-07. The formalization of the original argument failed at
the step where a maximally great being was taken to be able to thwart the
will of any other being. That step requires that maximal greatness entail
omnipotence, which the published version used without stating it. The
premise is now stated explicitly as Assumption 2.1.

What this file establishes. Given Assumption 2.1 and the conflict principle
(Assumption 2.2), there is at most one maximally great being. It does not
establish either assumption.
-/

namespace Philosophy.REL_15

/-- Beings. -/
axiom Being : Type

/-- Maximal greatness (non-modal reading, at a fixed world). -/
axiom MaximallyGreat : Being → Prop

/-- Omnipotence. -/
axiom Omnipotent : Being → Prop

/-- `CanThwart x y`: `x` is able to prevent any state of affairs that `y`
wills from obtaining. -/
axiom CanThwart : Being → Being → Prop

/-- Assumption 2.1 (added in the revision of 2026-10-07). Maximal greatness
entails omnipotence. -/
axiom assumption_2_1 : ∀ x, MaximallyGreat x → Omnipotent x

/-- Assumption 2.2 (conflict principle). An omnipotent being can thwart any
being distinct from itself. -/
axiom omnipotence_thwarts : ∀ x y, Omnipotent x → x ≠ y → CanThwart x y

/-- Assumption 2.3. No being that can be thwarted by another is omnipotent. -/
axiom thwartable_not_omnipotent : ∀ x y, CanThwart x y → ¬ Omnipotent y

/-- Theorem 3.1 (main result). There is at most one maximally great being. -/
theorem uniqueness (x y : Being)
    (hx : MaximallyGreat x) (hy : MaximallyGreat y) : x = y :=
  Classical.byContradiction fun hne =>
    thwartable_not_omnipotent x y
      (omnipotence_thwarts x y (assumption_2_1 x hx) hne)
      (assumption_2_1 y hy)

end Philosophy.REL_15

#print axioms Philosophy.REL_15.uniqueness
