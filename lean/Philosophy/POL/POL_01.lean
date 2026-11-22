/-
POL-01 · On Justice
Formalization of Volume I, Chapter 5: Propositions 5.2, 5.3 and 5.5 and
Theorem 5.4.

A distribution is summarized by two quantities (Definition 5.1): the level
of primary goods of the worst-off representative position and the total
level across positions. The modified difference principle ranks
distributions first by the level of the worst-off position and, among
distributions that tie on it, by the total.

What this file establishes. The modified difference principle is a strict
weak order (irreflexive, transitive, negatively transitive); a choice that
maximizes it over any finite feasible set selects an undominated
distribution; and it differs both from utilitarianism and from strict
maximin. It does not establish that the parties in the original position
would choose it, which is argued in Chapter 4.
-/

namespace Philosophy.POL_01

/-- Definition 5.1. A distribution: worst-off level and total. -/
structure Dist where
  worst : Nat
  total : Nat

/-- The modified difference principle: `Better x y` iff x is strictly
preferred to y. -/
def Better (x y : Dist) : Prop :=
  x.worst > y.worst ∨ (x.worst = y.worst ∧ x.total > y.total)

instance (x y : Dist) : Decidable (Better x y) := by
  unfold Better; exact inferInstance

/-- Proposition 5.2. The ordering is irreflexive and transitive. -/
theorem irrefl (x : Dist) : ¬ Better x x := by
  unfold Better; omega

theorem trans {x y z : Dist} (h1 : Better x y) (h2 : Better y z) : Better x z := by
  unfold Better at *; omega

/-- Proposition 5.3. Not being worse is transitive (negative transitivity). -/
theorem neg_trans {x y z : Dist} (h1 : ¬ Better x y) (h2 : ¬ Better y z) : ¬ Better x z := by
  unfold Better at *; omega

/-- Choosing from a finite feasible set, starting from a default. -/
def choose : List Dist → Dist → Dist
  | [], d => d
  | y :: ys, d => choose ys (if Better y d then y else d)

theorem choose_not_worse : ∀ (l : List Dist) (d : Dist), ¬ Better d (choose l d) := by
  intro l
  induction l with
  | nil => intro d; exact irrefl d
  | cons y ys ih =>
    intro d
    simp only [choose]
    by_cases h : Better y d
    · simp only [h, if_true]
      intro hd
      exact ih y (trans h hd)
    · simp only [h, if_false]
      exact ih d

/-- Theorem 5.4. The chosen distribution is not worse than any feasible one. -/
theorem choose_best : ∀ (l : List Dist) (d : Dist), ∀ y ∈ l, ¬ Better y (choose l d) := by
  intro l
  induction l with
  | nil => intro d y hy; cases hy
  | cons y ys ih =>
    intro d z hz
    simp only [choose]
    cases hz with
    | head =>
      by_cases h : Better y d
      · simp only [h, if_true]; exact choose_not_worse ys y
      · simp only [h, if_false]; exact neg_trans h (choose_not_worse ys d)
    | tail _ hz' => exact ih _ z hz'

/-- Proposition 5.5 (a). The principle departs from utilitarianism: a
distribution with a lower total can be better. -/
theorem not_utilitarian :
    ∃ x y : Dist, x.total < y.total ∧ Better x y :=
  ⟨⟨3, 7⟩, ⟨2, 12⟩, by decide, by decide⟩

/-- Proposition 5.5 (b). It departs from strict maximin, which is indifferent
between distributions with the same worst-off level: of two such
distributions, the one with the greater total is better. -/
theorem not_strict_maximin :
    ∃ x y : Dist, x.worst = y.worst ∧ Better x y :=
  ⟨⟨3, 100⟩, ⟨3, 7⟩, rfl, by decide⟩

end Philosophy.POL_01

#print axioms Philosophy.POL_01.choose_best
#print axioms Philosophy.POL_01.not_utilitarian
