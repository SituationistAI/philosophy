/-
MTH-02 · Benacerraf's Problem Answered
Formalization of Lemma 3.1, Theorem 3.2, Corollary 3.3, Proposition 3.4
and Theorem 3.5.

What this file establishes. (i) Derivation by truth-preserving rules from
true axioms yields only truths (Lemma 3.1). (ii) Given the analysis of
knowledge as safe justified belief, a justified belief formed by a method all
of whose outputs in close cases are true is knowledge (Theorem 3.2). (iii)
The derivational method of arithmetic is such a method (Corollary 3.3), so
a justified belief formed by it is knowledge of abstract objects without
causal contact (Proposition 3.4), and the causal requirement on knowledge is
false (Theorem 3.5).

What it does not establish. It does not establish that the axioms we accept
are true, that the rules we use are truth-preserving, or that any particular
belief-forming method in mathematics is reliable; these are premises.
-/

namespace Philosophy.MTH_02

/-- Propositions (contents of belief). -/
axiom Pn : Type

/-- Truth of a proposition. -/
axiom Tr : Pn → Prop

/-- Definition 2.5 (derivability). Derivability from axioms `Ax` by a two-premise rule `R`
(`R a b c`: from `a` and `b` infer `c`). -/
inductive Derivable (Ax : Pn → Prop) (R : Pn → Pn → Pn → Prop) : Pn → Prop
  | ax {p} : Ax p → Derivable Ax R p
  | rule {a b c} : Derivable Ax R a → Derivable Ax R b → R a b c →
      Derivable Ax R c

/-- Lemma 3.1. Derivation by truth-preserving rules from true axioms yields
only truths. -/
theorem derivation_truth (Ax : Pn → Prop) (R : Pn → Pn → Pn → Prop)
    (hAx : ∀ p, Ax p → Tr p)
    (hR : ∀ a b c, R a b c → Tr a → Tr b → Tr c) :
    ∀ p, Derivable Ax R p → Tr p := by
  intro p h
  induction h with
  | ax h => exact hAx _ h
  | rule _ _ hr iha ihb => exact hR _ _ _ hr iha ihb

/-- Belief-forming methods. -/
axiom Method : Type

/-- `Delivers m p`: in some close case, method `m` delivers belief in `p`. -/
axiom Delivers : Method → Pn → Prop

/-- Definition 2.1. A method is reliable when every proposition it delivers
in close cases is true. -/
def Reliable (m : Method) : Prop := ∀ p, Delivers m p → Tr p

/-- Subjects. -/
axiom Subj : Type

/-- `BelievesBy s m p`: subject `s` believes `p` on the basis of method `m`. -/
axiom BelievesBy : Subj → Method → Pn → Prop

/-- Justification. -/
axiom Justified : Subj → Pn → Prop

/-- Knowledge. -/
axiom Knows : Subj → Pn → Prop

/-- Assumption 2.2 (safety analysis, EPI-01 with the amendment for necessary
truths). A justified belief whose basis delivers only truths in close cases
is knowledge. -/
axiom safety_analysis : ∀ s m p, BelievesBy s m p → Justified s p →
  Reliable m → Knows s p

/-- A belief formed by a method is among that method's deliveries. -/
axiom belief_delivered : ∀ s m p, BelievesBy s m p → Delivers m p

/-- Theorem 3.2. A justified belief formed by a reliable method is knowledge,
and is true. -/
theorem reliable_knowledge (s : Subj) (m : Method) (p : Pn)
    (hb : BelievesBy s m p) (hj : Justified s p) (hm : Reliable m) :
    Knows s p ∧ Tr p :=
  ⟨safety_analysis s m p hb hj hm, hm p (belief_delivered s m p hb)⟩

/-- `CausallyLinked s p`: the facts `p` is about stand in a causal relation
to `s`'s belief that `p`. -/
axiom CausallyLinked : Subj → Pn → Prop

/-- `AboutAbstracta p`: `p` is about abstract objects only. -/
axiom AboutAbstracta : Pn → Prop

/-- Definition 2.3. The causal requirement. -/
def CausalRequirement : Prop := ∀ s p, Knows s p → CausallyLinked s p

/-- Assumption 2.4 (inertness, MTH-01). No belief stands in a causal
relation to facts about abstract objects only. -/
axiom inertness : ∀ s p, AboutAbstracta p → ¬ CausallyLinked s p

/-- Definition 2.5. The derivational method of arithmetic: its axioms, its
rules, and the method itself, which delivers only what is derivable. -/
axiom ArAx : Pn → Prop
/-- Definition 2.5 (continued). The rules of inference. -/
axiom ArR : Pn → Pn → Pn → Prop
/-- Definition 2.5 (continued). The derivational method. -/
axiom deriv : Method
/-- Definition 2.5 (continued). The derivational method delivers, in close
cases, only propositions derivable from the axioms by the rules. -/
axiom deriv_delivers : ∀ q, Delivers deriv q → Derivable ArAx ArR q

/-- Assumption 2.6. The axioms of arithmetic are true. -/
axiom axioms_true : ∀ q, ArAx q → Tr q

/-- Assumption 2.7. The rules of inference preserve truth. -/
axiom rules_preserve : ∀ a b c, ArR a b c → Tr a → Tr b → Tr c

/-- Assumption 2.8. Some subject has a justified belief, formed by the
derivational method, in a proposition about abstract objects only. -/
axiom derivational_belief :
  ∃ s p, AboutAbstracta p ∧ BelievesBy s deriv p ∧ Justified s p

/-- Corollary 3.3. The derivational method is reliable. -/
theorem deriv_reliable : Reliable deriv := fun q hq =>
  derivation_truth ArAx ArR axioms_true rules_preserve q (deriv_delivers q hq)

/-- Proposition 3.4. Some subject knows a truth about abstract objects only,
without causal contact with what it is about. -/
theorem acausal_knowledge :
    ∃ s p, AboutAbstracta p ∧ Knows s p ∧ ¬ CausallyLinked s p := by
  obtain ⟨s, p, ha, hb, hj⟩ := derivational_belief
  exact ⟨s, p, ha, (reliable_knowledge s deriv p hb hj deriv_reliable).1,
    inertness s p ha⟩

/-- Theorem 3.5 (main result). The causal requirement is false. -/
theorem causal_requirement_false : ¬ CausalRequirement := by
  intro hc
  obtain ⟨s, p, _, hk, hn⟩ := acausal_knowledge
  exact hn (hc s p hk)

end Philosophy.MTH_02

#print axioms Philosophy.MTH_02.acausal_knowledge
#print axioms Philosophy.MTH_02.causal_requirement_false
