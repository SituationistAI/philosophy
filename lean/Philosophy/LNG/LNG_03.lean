/-
LNG-03 · The Present King of France Is Not Bald
Formalization of Lemma 3.1, Theorem 3.2 and Corollary 3.3.

Russell's analysis (Definition 2.1): "The F is G" is true just in case
exactly one thing is F and it is G. Given that nothing is presently king of
France (Assumption 2.2), "The present King of France is bald" is false, as is
its narrow-scope negation, while its wide-scope negation is true.

What this file establishes. The truth values the Russellian analysis assigns
to the three sentences, given Assumption 2.2. It does not establish that the
analysis is correct; Strawson's objection is answered in Section 4 of the
manuscript.
-/

namespace Philosophy.LNG_03

/-- Individuals. -/
axiom Individual : Type

/-- Being presently king of France. -/
axiom KingOfFrance : Individual → Prop

/-- Being bald. -/
axiom Bald : Individual → Prop

/-- Definition 2.1. Russell's analysis of "The F is G". -/
def The (F G : Individual → Prop) : Prop :=
  ∃ x, F x ∧ (∀ y, F y → y = x) ∧ G x

/-- Assumption 2.2. Nothing is presently king of France. -/
axiom no_king : ∀ x, ¬ KingOfFrance x

/-- Lemma 3.1. If nothing is F, "The F is G" is false, for every G. -/
theorem lemma_3_1 (F G : Individual → Prop) (h : ∀ x, ¬ F x) : ¬ The F G :=
  fun ⟨x, hx, _, _⟩ => h x hx

/-- Theorem 3.2 (main result). "The present King of France is bald" is
false. -/
theorem king_not_bald : ¬ The KingOfFrance Bald :=
  lemma_3_1 KingOfFrance Bald no_king

/-- Corollary 3.3. The narrow-scope negation "The present King of France is
not-bald" is false too, and the wide-scope negation "It is not the case that
the present King of France is bald" is true. -/
theorem scopes :
    ¬ The KingOfFrance (fun x => ¬ Bald x) ∧ ¬ The KingOfFrance Bald :=
  ⟨lemma_3_1 _ _ no_king, king_not_bald⟩

end Philosophy.LNG_03

#print axioms Philosophy.LNG_03.king_not_bald
#print axioms Philosophy.LNG_03.scopes
