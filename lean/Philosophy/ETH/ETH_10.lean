/-
ETH-10 · The Ethics of Eating Animals
Formalization of Theorem 3.1, Proposition 3.2, Theorem 3.3 and
Corollary 3.4.

Practices form a primitive type, with two distinguished practices: factory
farming (Definition 2.1) and humane farming (Definition 2.2). The
properties used in the assumptions and principles are primitive
predicates. A practice is morally neutral when there is no moral reason
against it (Definition 2.3).

What this file establishes. Given the moral status of farmed animals
(Assumption 2.4, from ETH-07), the facts about the two practices
(Assumptions 2.5 and 2.6) and Principles P1 to P3, factory farming is
impermissible, and humane farming is permissible but not morally neutral.
The permission for humane farming does not depend on the premises that
condemn factory farming.

What it does not establish. It does not establish the premises, and in
particular not the judgment, defended in Section 4 of the manuscript, that
a farmed animal's time-relative interest in continuing to live is weak
enough for Principle P3 to apply. Nothing here concerns individual
purchases (Section 5).
-/

namespace Philosophy.ETH_10

/-- Practices of raising animals for food. -/
axiom Practice : Type

/-- Definition 2.1. Factory farming. -/
axiom factory : Practice

/-- Definition 2.2. Humane farming. -/
axiom humane : Practice

/-- The animals affected by the practice have moral status. -/
axiom StatusVictims : Practice → Prop
/-- The practice causes severe suffering. -/
axiom SevereSuffering : Practice → Prop
/-- The benefits of the practice are necessary (not obtainable or
adequately replaceable by other means). -/
axiom NecessaryBenefit : Practice → Prop
/-- The practice kills beings whose future lives would be good. -/
axiom KillsGoodFutures : Practice → Prop
/-- The animals of the practice live lives that are good on balance. -/
axiom GoodLives : Practice → Prop
/-- The animals' time-relative interest in continuing to live is weak. -/
axiom WeakTRI : Practice → Prop
/-- There is a moral reason against the practice. -/
axiom ReasonAgainst : Practice → Prop
/-- The practice is permissible. -/
axiom Permissible : Practice → Prop

/-- Definition 2.3. A practice is morally neutral if there is no moral
reason against it. -/
def Neutral (p : Practice) : Prop := ¬ ReasonAgainst p

/-- Assumption 2.4 (moral status, from ETH-07). -/
axiom status_victims : StatusVictims factory ∧ StatusVictims humane

/-- Assumption 2.5 (factory farming). -/
axiom factory_facts : SevereSuffering factory ∧ ¬ NecessaryBenefit factory

/-- Assumption 2.6 (humane farming). -/
axiom humane_facts : ¬ SevereSuffering humane ∧ KillsGoodFutures humane ∧
    GoodLives humane ∧ WeakTRI humane

/-- Principle P1 (unnecessary suffering). -/
axiom unnecessary_suffering : ∀ p, StatusVictims p → SevereSuffering p →
    ¬ NecessaryBenefit p → ¬ Permissible p

/-- Principle P2 (deprivation). -/
axiom deprivation : ∀ p, StatusVictims p → KillsGoodFutures p → ReasonAgainst p

/-- Principle P3 (humane permission). -/
axiom humane_permission : ∀ p, ¬ SevereSuffering p → GoodLives p → WeakTRI p →
    Permissible p

/-- Theorem 3.1. Factory farming is impermissible. -/
theorem factory_impermissible : ¬ Permissible factory :=
  unnecessary_suffering factory status_victims.1 factory_facts.1 factory_facts.2

/-- Proposition 3.2. Humane farming is not morally neutral. -/
theorem humane_not_neutral : ¬ Neutral humane :=
  fun h => h (deprivation humane status_victims.2 humane_facts.2.1)

/-- Theorem 3.3. Humane farming is permissible. -/
theorem humane_permissible : Permissible humane :=
  humane_permission humane humane_facts.1 humane_facts.2.2.1 humane_facts.2.2.2

/-- Corollary 3.4 (main result). Factory farming is impermissible; humane
farming is permissible but not morally neutral. -/
theorem main : ¬ Permissible factory ∧ Permissible humane ∧ ¬ Neutral humane :=
  ⟨factory_impermissible, humane_permissible, humane_not_neutral⟩

end Philosophy.ETH_10

#print axioms Philosophy.ETH_10.main
#print axioms Philosophy.ETH_10.factory_impermissible
#print axioms Philosophy.ETH_10.humane_permissible
