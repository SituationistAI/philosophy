/-
MTH-07 · Excluded Middle in Mathematics
Formalization of Proposition 3.1, Theorem 3.2, Proposition 3.3 and
Corollary 3.4.

What this file establishes. (i) No instance of excluded middle can be
refuted, even intuitionistically (Proposition 3.1). (ii) Given the classical
clauses for negation and disjunction and the determinacy of mathematical
truth, every instance of excluded middle for a mathematical sentence is true
(Theorem 3.2). (iii) Given only the negation clause, truth is
not contained in provability in any formal system with an undecided sentence;
this part uses no classical reasoning (Proposition 3.3). (iv) Excluded middle
is true and not every sentence is decided (Corollary 3.4).

What it does not establish. It does not establish the determinacy of
mathematical truth (Assumption 2.4), which the manuscript defends from the
categoricity of second-order arithmetic; nor that the formal system in
question has an undecided sentence, which is Goedel's theorem, taken here as
an assumption (Assumption 2.5). Classical reasoning in the metalanguage is
not used anywhere: the classical premise is the single visible axiom
`determinacy`.
-/

namespace Philosophy.MTH_07

/-- Proposition 3.1. Excluded middle is irrefutable, in intuitionistic
logic. -/
theorem lem_irrefutable (A : Prop) : ¬¬(A ∨ ¬A) :=
  fun h => h (Or.inr fun a => h (Or.inl a))

/-- Definition 2.1. Mathematical sentences, with negation and disjunction. -/
axiom Sent : Type
axiom neg : Sent → Sent
axiom disj : Sent → Sent → Sent

/-- Definition 2.1 (continued). Truth of a mathematical sentence. -/
axiom T : Sent → Prop

/-- Definition 2.2. Provability in a fixed formal system. -/
axiom Pr : Sent → Prop

/-- Assumption 2.3 (classical clauses). Negation. -/
axiom clause_neg : ∀ A, T (neg A) ↔ ¬ T A

/-- Assumption 2.3 (classical clauses). Disjunction. -/
axiom clause_disj : ∀ A B, T (disj A B) ↔ T A ∨ T B

/-- Assumption 2.4 (determinacy). Every mathematical sentence is true or
not true. -/
axiom determinacy : ∀ A, T A ∨ ¬ T A

/-- Assumption 2.5 (incompleteness). Some sentence is neither provable nor
refutable in the system. -/
axiom undecided : ∃ G, ¬ Pr G ∧ ¬ Pr (neg G)

/-- Theorem 3.2 (main result). Every instance of excluded middle is true. -/
theorem lem_true (A : Sent) : T (disj A (neg A)) := by
  apply (clause_disj A (neg A)).2
  cases determinacy A with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr ((clause_neg A).2 h)

/-- Proposition 3.3. Truth is not contained in provability. -/
theorem truth_outruns_proof : ¬ ∀ A, T A → Pr A := by
  intro h
  obtain ⟨G, hG, hnG⟩ := undecided
  have hnt : ¬ T G := fun t => hG (h G t)
  exact hnG (h (neg G) ((clause_neg G).2 hnt))

/-- Corollary 3.4. Excluded middle is true although not every sentence is
decided. -/
theorem lem_without_decision :
    (∀ A, T (disj A (neg A))) ∧ ¬ ∀ A, Pr A ∨ Pr (neg A) := by
  refine ⟨lem_true, ?_⟩
  intro h
  obtain ⟨G, hG, hnG⟩ := undecided
  cases h G with
  | inl p => exact hG p
  | inr p => exact hnG p

end Philosophy.MTH_07

#print axioms Philosophy.MTH_07.lem_irrefutable
#print axioms Philosophy.MTH_07.lem_true
#print axioms Philosophy.MTH_07.truth_outruns_proof
#print axioms Philosophy.MTH_07.lem_without_decision
