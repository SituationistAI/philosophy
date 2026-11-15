/-
SCI-10 · Idealization and Representation
Formalization of Theorems 3.1 and 3.2, Corollary 3.3 and Proposition 3.4.

Targets and models assign a value to every feature (Definition 2.1). A model
is true of a target if it agrees with it on every feature, and similar to it
in a set of respects if it agrees with it on those (Definition 2.2). Whether a
model explains a phenomenon across a class of targets, given the respects
that make a difference to it, is a primitive, constrained by two premises:
an explanatory model is similar to every target in the class in the
difference-making respects (Assumption 2.3), and it is impartial on every
other respect, assigning it a value that no target in the class has
(Assumption 2.4).

What this file establishes. If any respect makes no difference, every
explanatory model is false of every target in its class while being similar
to each in the difference-making respects; a model made true of one target
thereby ceases to explain; and, independently of the explanatory premises,
any single model is false of some member of a class that varies in some
feature. It does not establish Assumptions 2.3 and 2.4, which are defended in
Section 2 of the manuscript.
-/

namespace Philosophy.SCI_10

/-- Primitive: features (respects of comparison). -/
axiom Feature : Type
/-- Primitive: the values a feature may take. -/
axiom Val : Type

/-- Definition 2.1. Targets and models assign a value to every feature. -/
abbrev Assignment := Feature → Val

/-- Definition 2.2. Truth of a model, and similarity in a set of respects. -/
def TrueOf (m t : Assignment) : Prop := ∀ f, m f = t f
def SimilarIn (m t : Assignment) (D : Feature → Prop) : Prop := ∀ f, D f → m f = t f

/-- Primitive: model `m` explains the phenomenon across class `K`, where `D`
are the difference-making respects. -/
axiom Explains : Assignment → (Assignment → Prop) → (Feature → Prop) → Prop

/-- Assumption 2.3 (Similarity). An explanatory model is similar to every
target in its class in the difference-making respects. -/
axiom similarity : ∀ m K D, Explains m K D → ∀ t, K t → SimilarIn m t D

/-- Assumption 2.4 (Impartiality). On a respect that makes no difference, an
explanatory model assigns a value that no target in its class has. -/
axiom impartiality : ∀ m K D, Explains m K D → ∀ f, ¬ D f → ∀ t, K t → m f ≠ t f

/-- Theorem 3.1 (Models are false). If some respect makes no difference, an
explanatory model is false of every target in its class. -/
theorem models_false (m : Assignment) (K : Assignment → Prop) (D : Feature → Prop)
    (he : Explains m K D) (hf : ∃ f, ¬ D f) : ∀ t, K t → ¬ TrueOf m t := by
  intro t ht htrue
  obtain ⟨f, hnd⟩ := hf
  exact impartiality m K D he f hnd t ht (htrue f)

/-- Theorem 3.2 (Partial similarity). An explanatory model is false of each
target in its class and similar to each in the difference-making respects. -/
theorem false_but_similar (m : Assignment) (K : Assignment → Prop) (D : Feature → Prop)
    (he : Explains m K D) (hf : ∃ f, ¬ D f) :
    ∀ t, K t → ¬ TrueOf m t ∧ SimilarIn m t D :=
  fun t ht => ⟨models_false m K D he hf t ht, similarity m K D he t ht⟩

/-- Corollary 3.3 (Idealization is essential). A model true of some target in
the class does not explain the phenomenon across the class, if some respect
makes no difference. -/
theorem deidealized_not_explanatory (m : Assignment) (K : Assignment → Prop)
    (D : Feature → Prop) (hf : ∃ f, ¬ D f) (t : Assignment) (ht : K t)
    (htrue : TrueOf m t) : ¬ Explains m K D :=
  fun he => models_false m K D he hf t ht htrue

/-- Proposition 3.4 (Heterogeneity). Any model is false of some member of a
class that varies in some feature. -/
theorem heterogeneity (m : Assignment) (t1 t2 : Assignment) (f : Feature)
    (hv : t1 f ≠ t2 f) : ¬ TrueOf m t1 ∨ ¬ TrueOf m t2 := by
  apply Classical.byContradiction
  intro h
  apply h
  apply Or.inr
  intro h2
  apply h
  apply Or.inl
  intro h1
  exact hv ((h1 f).symm.trans (h2 f))

end Philosophy.SCI_10

#print axioms Philosophy.SCI_10.false_but_similar
#print axioms Philosophy.SCI_10.deidealized_not_explanatory
