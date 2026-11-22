/-
LOG-20 · Completeness and Its Limits
Formalization of Theorem 3.1 and Proposition 3.2.

A collection of theorems is represented by a set of sentences `Thm`
(Definition 2.1). Truth is a primitive predicate on sentences, with the
classical clause for negation (Assumption 2.2). The collection is sound
(Assumption 2.3) and contains a diagonal sentence that is true exactly
when it is not among the theorems (Assumption 2.4); by Gödel's diagonal
lemma such a sentence exists for every effectively axiomatized collection
that contains elementary arithmetic.

What this file establishes. Under Assumptions 2.2–2.4 the collection is
incomplete: some true sentence is not a theorem, and neither it nor its
negation is a theorem (Theorem 3.1). A collection that contains a sentence
and its negation, and is closed under explosion, contains every sentence
(Proposition 3.2), so that rival philosophical premises cannot simply be
pooled into one complete theory.

What it does not establish. It does not prove the completeness of
first-order logic, which is cited (Gödel 1930), nor the diagonal lemma,
which is assumed in Assumption 2.4.
-/

namespace Philosophy.LOG_20

/-- Definition 2.1. Sentences of the language of the collection (primitive). -/
axiom Sentence : Type
/-- Definition 2.1. Negation. -/
axiom neg : Sentence → Sentence
/-- Definition 2.1. The theorems of the collection (primitive). -/
axiom Thm : Sentence → Prop
/-- Truth (primitive). -/
axiom True' : Sentence → Prop

/-- Assumption 2.2. The negation of a sentence is true iff the sentence is
not true. -/
axiom true_neg : ∀ φ, True' (neg φ) ↔ ¬ True' φ

/-- Assumption 2.3 (soundness). Every theorem of the collection is true. -/
axiom soundness : ∀ φ, Thm φ → True' φ

/-- Assumption 2.4 (diagonal sentence). Some sentence is true iff it is not
a theorem of the collection. -/
axiom diagonal : ∃ G, True' G ↔ ¬ Thm G

/-- Theorem 3.1 (incompleteness). Some sentence is true, not a theorem,
and has a negation that is not a theorem either. -/
theorem incompleteness : ∃ G, True' G ∧ ¬ Thm G ∧ ¬ Thm (neg G) := by
  obtain ⟨G, hG⟩ := diagonal
  have hnot : ¬ Thm G := fun h => (hG.mp (soundness G h)) h
  have htrue : True' G := hG.mpr hnot
  refine ⟨G, htrue, hnot, fun h => ?_⟩
  exact ((true_neg G).mp (soundness _ h)) htrue

/-- Proposition 3.2 (pooling). A set of sentences closed under explosion
that contains a sentence and its negation contains every sentence. -/
theorem pooling (S : Sentence → Prop)
    (explosion : ∀ φ ψ, S φ → S (neg φ) → S ψ)
    (φ : Sentence) (h₁ : S φ) (h₂ : S (neg φ)) : ∀ ψ, S ψ :=
  fun ψ => explosion φ ψ h₁ h₂

end Philosophy.LOG_20

#print axioms Philosophy.LOG_20.incompleteness
