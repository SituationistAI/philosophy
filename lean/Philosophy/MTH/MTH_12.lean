/-
MTH-12 · Unknowable Mathematical Truths
Formalization of Theorem 3.1 and Corollary 3.2.

What this file establishes. Given that the arithmetical sentences knowable
in principle form a recursively enumerable set extending Robinson
arithmetic (Assumption 2.3), that knowledge is factive (Assumption 2.4), and
Goedel's first incompleteness theorem in its semantic form (Assumption 2.2),
there is a true arithmetical sentence that is not knowable (Theorem 3.1),
and it is not of Fitch's form (Corollary 3.2).

What it does not establish. It does not prove Goedel's theorem, which is
taken as an axiom about an abstract notion of theory; nor does it establish
Assumption 2.3, which the manuscript defends from MTH-05. It does not
identify the unknowable sentence.
-/

namespace Philosophy.MTH_12

/-- Definition 2.1. Sentences, arithmetical sentences, truth. -/
axiom Sent : Type
/-- Definition 2.1 (continued). Being a sentence of first-order arithmetic. -/
axiom Arith : Sent → Prop
/-- Definition 2.1 (continued). Truth. -/
axiom Tr : Sent → Prop

/-- Definition 2.1 (continued). A set of sentences is recursively
enumerable. -/
axiom RE : (Sent → Prop) → Prop
/-- Definition 2.1 (continued). A set of sentences contains Robinson
arithmetic and is closed under first-order consequence. -/
axiom ExtendsQ : (Sent → Prop) → Prop

/-- Assumption 2.2 (Goedel's first incompleteness theorem, semantic form).
Every recursively enumerable set of truths extending Robinson arithmetic
omits some true arithmetical sentence. -/
axiom goedel : ∀ S : Sent → Prop, RE S → ExtendsQ S → (∀ A, S A → Tr A) →
  ∃ G, Arith G ∧ Tr G ∧ ¬ S G

/-- `Knowable A`: some finite knower of our kind, idealized in time and
memory, could know `A`. -/
axiom Knowable : Sent → Prop

/-- Assumption 2.3 (finitary knowledge). The set of knowable arithmetical
sentences is recursively enumerable and extends Robinson arithmetic. -/
axiom knowable_re : RE (fun A => Arith A ∧ Knowable A)
axiom knowable_q : ExtendsQ (fun A => Arith A ∧ Knowable A)

/-- Assumption 2.4 (factivity). What is knowable is true. -/
axiom factive : ∀ A, Knowable A → Tr A

/-- Definition 2.5. Sentences of Fitch's form, `p ∧ ¬Kp`. -/
axiom FitchForm : Sent → Prop
/-- Definition 2.5 (continued). Sentences of Fitch's form contain the
knowledge operator, so none is a sentence of arithmetic. -/
axiom fitch_not_arith : ∀ A, FitchForm A → ¬ Arith A

/-- Theorem 3.1 (main result). Some true arithmetical sentence is not
knowable. -/
theorem unknowable_truth : ∃ G, Arith G ∧ Tr G ∧ ¬ Knowable G := by
  obtain ⟨G, ha, ht, hn⟩ :=
    goedel _ knowable_re knowable_q (fun A h => factive A h.2)
  exact ⟨G, ha, ht, fun hk => hn ⟨ha, hk⟩⟩

/-- Corollary 3.2. Some true sentence is unknowable and not of Fitch's
form. -/
theorem not_fitch : ∃ G, Tr G ∧ ¬ Knowable G ∧ ¬ FitchForm G := by
  obtain ⟨G, ha, ht, hk⟩ := unknowable_truth
  exact ⟨G, ht, hk, fun hf => fitch_not_arith G hf ha⟩

end Philosophy.MTH_12

#print axioms Philosophy.MTH_12.unknowable_truth
#print axioms Philosophy.MTH_12.not_fitch
