/-
TSM-07 · Possible Worlds as Abstract Objects
Formalization of Lemma 3.1, Theorems 3.2 and 3.3 and Corollary 3.4.

What this file establishes. Worlds are taken to be maximal consistent sets of
propositions (Definition 2.3), with sets of propositions represented as
predicates on propositions. Given bivalence and noncontradiction for truth
(Assumptions 2.7 and 2.8), the consistency of the actual truths
(Assumption 2.9), the principle that only true propositions are concretely
realized (Assumption 2.10) and the principle that the concrete cosmos
realizes every truth (Assumption 2.11), the module proves that the set of truths is a world,
that it is the only world all of whose members are true, that a world is
concretely realized if and only if it is that world, and that whatever is
actually true is possible. The uniqueness of the actual world does not
depend on bivalence; its existence does.

What this file does not establish. It does not say what propositions are or
what consistency consists in: both are primitives here (Definitions 2.1 and
2.2). The analysis of consistency as consistency with the essences of things
belongs to TSM-10. Nor does it establish any of the five assumptions.
-/

namespace Philosophy.TSM_07

/-- Definition 2.1 (primitive). Propositions. -/
axiom Proposition : Type

/-- Definition 2.1 (primitive). The negation of a proposition. -/
axiom neg : Proposition → Proposition

/-- Definition 2.1 (primitive). Truth simpliciter (truth at actuality). -/
axiom IsTrue : Proposition → Prop

/-- Definition 2.2 (primitive). Consistency of a set of propositions, in the
sense of compossibility. TSM-10 analyses it; here it is left unanalysed. -/
axiom Consistent : (Proposition → Prop) → Prop

/-- Definition 2.3. A world is a maximal consistent set of propositions:
consistent, and containing each proposition or its negation. -/
def World (W : Proposition → Prop) : Prop :=
  Consistent W ∧ ∀ p, W p ∨ W (neg p)

/-- Definition 2.4. A proposition is possible if it belongs to some world. -/
def Possible (p : Proposition) : Prop :=
  ∃ W, World W ∧ W p

/-- Definition 2.5. A world is actual if every proposition in it is true. -/
def Actual (W : Proposition → Prop) : Prop :=
  World W ∧ ∀ p, W p → IsTrue p

/-- Definition 2.6 (primitive). A set of propositions is concretely realized
if some concrete totality of things is as its members represent. -/
axiom ConcretelyRealized : (Proposition → Prop) → Prop

/-- Assumption 2.7 (bivalence). Every proposition or its negation is true. -/
axiom bivalence : ∀ p, IsTrue p ∨ IsTrue (neg p)

/-- Assumption 2.8 (noncontradiction). No proposition is true together with
its negation. -/
axiom noncontradiction : ∀ p, ¬ (IsTrue p ∧ IsTrue (neg p))

/-- Assumption 2.9. The actual truths are jointly consistent. -/
axiom truth_consistent : Consistent IsTrue

/-- Assumption 2.10 (actualism about the concrete). Whatever a concrete
totality realizes is true: there are no concrete totalities other than the
actual one. -/
axiom realization_truth :
  ∀ W, ConcretelyRealized W → ∀ p, W p → IsTrue p

/-- Assumption 2.11. The concrete cosmos realizes the set of truths. -/
axiom cosmos_realizes : ConcretelyRealized IsTrue

/-- Lemma 3.1. The set of truths is a world. -/
theorem truth_is_world : World IsTrue :=
  ⟨truth_consistent, bivalence⟩

/-- Theorem 3.2, uniqueness half. Any actual world coincides with the set of
truths, so there is at most one actual world. Bivalence (Assumption 2.7) is
not used. -/
theorem actual_eq_truth (W : Proposition → Prop) (h : Actual W) :
    W = IsTrue := by
  funext p
  apply propext
  constructor
  · exact h.2 p
  · intro hp
    cases h.1.2 p with
    | inl hw => exact hw
    | inr hn => exact absurd ⟨hp, h.2 (neg p) hn⟩ (noncontradiction p)

/-- Theorem 3.2. There is exactly one actual world, the set of truths. -/
theorem unique_actual :
    Actual IsTrue ∧ ∀ W, Actual W → W = IsTrue :=
  ⟨⟨truth_is_world, fun _ h => h⟩, actual_eq_truth⟩

/-- Theorem 3.3. A world is concretely realized if and only if it is the
actual world. -/
theorem concrete_iff_actual (W : Proposition → Prop) (hW : World W) :
    ConcretelyRealized W ↔ W = IsTrue := by
  constructor
  · intro hc
    exact actual_eq_truth W ⟨hW, realization_truth W hc⟩
  · intro h
    rw [h]
    exact cosmos_realizes

/-- Corollary 3.4. Whatever is true is possible. -/
theorem actual_implies_possible (p : Proposition) (h : IsTrue p) :
    Possible p :=
  ⟨IsTrue, truth_is_world, h⟩

end Philosophy.TSM_07

#print axioms Philosophy.TSM_07.actual_eq_truth
#print axioms Philosophy.TSM_07.unique_actual
#print axioms Philosophy.TSM_07.concrete_iff_actual
