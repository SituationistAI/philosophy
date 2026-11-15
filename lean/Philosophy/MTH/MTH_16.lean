/-
MTH-16 · Against Fictionalism
Formalization of Lemma 3.1, Proposition 3.2 and Theorem 3.3.

What this file establishes. Given that a nominalization of a physical theory
must represent each state figuring in its predictions by a concrete
configuration (Assumption 2.5), that concrete configurations represent only
states that are instantiated (Assumption 2.6), and that some state figuring
in the predictions of quantum mechanics is not instantiated (Assumption
2.7), quantum mechanics cannot be nominalized (Proposition 3.2). Given
further that the fictionalist is entitled to accept a best physical theory
only if it can be nominalized (Assumption 2.3) and that quantum mechanics is
among our best physical theories (Assumption 2.4),
fictionalism fails (Theorem 3.3).

What it does not establish. It does not establish any of the assumptions.
In particular it does not show that no other strategy than representation
by concrete configurations could nominalize physics; Assumption 2.5 says
that none could, and the manuscript defends it.
-/

namespace Philosophy.MTH_16

/-- Physical theories. -/
axiom Theory : Type

/-- The states that figure in a theory's predictions about actual
systems. -/
axiom State : Theory → Type

/-- Definition 2.2. The theory can be nominalized. -/
axiom Nominalizable : Theory → Prop

/-- The theory is among our best physical theories. -/
axiom Best : Theory → Prop

/-- Definition 2.1. Fictionalism: mathematical statements with existential
import are false, and the fictionalist accepts only the nominalistic content of
science. -/
axiom Fictionalism : Prop

/-- `Concretely t s`: state `s` of theory `t` is represented by a concrete
configuration. -/
axiom Concretely : (t : Theory) → State t → Prop

/-- `Instantiated t s`: some physical system is in state `s`. -/
axiom Instantiated : (t : Theory) → State t → Prop

/-- Quantum mechanics. -/
axiom QM : Theory

/-- Assumption 2.3 (entitlement). The fictionalist is entitled to accept a
best physical theory only if it can be nominalized. -/
axiom entitlement : Fictionalism → ∀ t, Best t → Nominalizable t

/-- Assumption 2.4. Quantum mechanics is among our best physical theories. -/
axiom qm_best : Best QM

/-- Assumption 2.5 (representation). A nominalization of a theory represents
every state that figures in its predictions by a concrete configuration. -/
axiom representation : ∀ t, Nominalizable t → ∀ s : State t, Concretely t s

/-- Assumption 2.6 (actuality). A concrete configuration represents only a
state that is instantiated. -/
axiom actuality : ∀ t (s : State t), Concretely t s → Instantiated t s

/-- Assumption 2.7 (uninstantiated states). Some state that figures in the
predictions of quantum mechanics is not instantiated. -/
axiom qm_uninstantiated : ∃ s : State QM, ¬ Instantiated QM s

/-- Lemma 3.1. No theory in whose predictions an uninstantiated state figures
can be nominalized. -/
theorem no_nominalization (t : Theory)
    (h : ∃ s : State t, ¬ Instantiated t s) : ¬ Nominalizable t := by
  intro hn
  obtain ⟨s, hs⟩ := h
  exact hs (actuality t s (representation t hn s))

/-- Proposition 3.2. Quantum mechanics cannot be nominalized. -/
theorem qm_not_nominalizable : ¬ Nominalizable QM :=
  no_nominalization QM qm_uninstantiated

/-- Theorem 3.3 (main result). Fictionalism fails. -/
theorem against_fictionalism : ¬ Fictionalism := fun hf =>
  qm_not_nominalizable (entitlement hf QM qm_best)

end Philosophy.MTH_16

#print axioms Philosophy.MTH_16.qm_not_nominalizable
#print axioms Philosophy.MTH_16.against_fictionalism
