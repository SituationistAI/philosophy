/-
PHE-19 · The Impossible Gift and the Present Collection
Formalization of Theorem 2.2 and Corollary 2.3.

What this file establishes. Given Derrida's two conditions on the gift
(Principles P1 and P2) and the fact that the present collection is
recognized as a gift at its release (Assumption 2.1), nothing recognized as
a gift is a gift, and the collection is not one. It does not establish the
two conditions, which the manuscript discusses, nor that their conjunction
leaves any gift possible.
-/

namespace Philosophy.PHE_19

/-- Things that may be given. -/
axiom Thing : Type

/-- The present collection. -/
axiom collection : Thing

axiom Gift : Thing → Prop
axiom RecognizedAsGift : Thing → Prop
/-- Something returns to the donor: a counter-gift, gratitude, or the
symbolic return constituted by recognition itself. -/
axiom Returned : Thing → Prop

/-- Principle P1. A gift involves no return. -/
axiom no_return : ∀ x, Gift x → ¬ Returned x

/-- Principle P2. Recognition as a gift is already a return. -/
axiom recognition_returns : ∀ x, RecognizedAsGift x → Returned x

/-- Assumption 2.1. The collection is recognized as a gift at its release. -/
axiom released_as_gift : RecognizedAsGift collection

/-- Theorem 2.2. A gift exists only if it is not recognized as a gift. -/
theorem unrecognized (x : Thing) (g : Gift x) : ¬ RecognizedAsGift x :=
  fun r => no_return x g (recognition_returns x r)

/-- Corollary 2.3. The present collection is not a gift. -/
theorem not_a_gift : ¬ Gift collection :=
  fun g => unrecognized collection g released_as_gift

end Philosophy.PHE_19

#print axioms Philosophy.PHE_19.not_a_gift
