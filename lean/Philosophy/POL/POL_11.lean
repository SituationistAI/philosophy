/-
POL-11 · The Social Contract as Implicit Framework
Formalization of Proposition 3.1, Theorem 3.2 and Corollaries 3.3 and 3.4.

A framework of mutual expectations is an institution in the sense of MET-20-a:
it comes into existence through collective acceptance and persists as long as
it is not collectively rejected (Assumption 2.3, which is MET-20-a,
Lemma 3.2, together with its converse cases). The social contract of a society
is the framework of mutual expectations that governs its basic cooperation
(Definition 2.2).

What this file establishes. Given the persistence condition and the three
premises about the society considered (Assumptions 2.4–2.6), its social
contract exists and is not an actual agreement (Theorem 3.2); actual
agreement is neither necessary (Corollary 3.3) nor sufficient (Corollary 3.4)
for the existence of a framework; and a member who never agreed and never
actively accepted the framework still falls under it.

What it does not establish. It does not establish the persistence condition,
which is argued for in MET-20-a, nor the historical and empirical premises
2.4–2.6, nor anything about the normative force of the contract.
-/

namespace Philosophy.POL_11

/-- Frameworks of mutual expectations (Definition 2.1). -/
axiom Framework : Type

/-- Persons. -/
axiom Person : Type

/-- The framework came into existence through collective acceptance. -/
axiom Instituted : Framework → Prop

/-- The framework has been collectively rejected by the community whose
practices contain its rules. -/
axiom Rejected : Framework → Prop

/-- The framework exists now. -/
axiom Exists : Framework → Prop

/-- The framework is the content of an actual agreement among all those it
governs. -/
axiom Agreed : Framework → Prop

/-- `Member x f`: `x` belongs to the community whose practices contain the
rules of `f`. -/
axiom Member : Person → Framework → Prop

/-- `x` has agreed to `f`. -/
axiom AgreedBy : Person → Framework → Prop

/-- Assumption 2.3 (persistence; MET-20-a, Lemma 3.2). An instituted framework
exists as long as it is not collectively rejected; collective rejection ends
it; and nothing exists as a framework without having been instituted. -/
axiom persistence : ∀ f, Instituted f → ¬ Rejected f → Exists f
axiom rejection_ends : ∀ f, Rejected f → ¬ Exists f
axiom requires_institution : ∀ f, Exists f → Instituted f

/-- Definition 2.2. The social contract of the society considered: the
framework of mutual expectations governing its basic cooperation. -/
axiom contract : Framework

/-- Assumption 2.4. The framework was instituted. -/
axiom assumption_2_4 : Instituted contract

/-- Assumption 2.5. It has not been collectively rejected. -/
axiom assumption_2_5 : ¬ Rejected contract

/-- Assumption 2.6. It is not the content of an actual agreement among all
those it governs; in particular some member never agreed to it. -/
axiom assumption_2_6 : ¬ Agreed contract
axiom assumption_2_6' : ∃ x, Member x contract ∧ ¬ AgreedBy x contract

/-- Proposition 3.1. A framework exists if and only if it was instituted and
has not been collectively rejected. -/
theorem exists_iff (f : Framework) : Exists f ↔ Instituted f ∧ ¬ Rejected f :=
  ⟨fun h => ⟨requires_institution f h, fun hr => rejection_ends f hr h⟩,
   fun ⟨hi, hr⟩ => persistence f hi hr⟩

/-- Theorem 3.2. There is a social contract, and it is not an actual
agreement. -/
theorem contract_exists : Exists contract ∧ ¬ Agreed contract :=
  ⟨persistence contract assumption_2_4 assumption_2_5, assumption_2_6⟩

/-- Corollary 3.3. Actual agreement is not necessary for the existence of a
framework, and some member falls under the existing contract without having
agreed to it. -/
theorem agreement_not_necessary :
    (∃ f, Exists f ∧ ¬ Agreed f) ∧
    (∃ x, Member x contract ∧ Exists contract ∧ ¬ AgreedBy x contract) :=
  ⟨⟨contract, contract_exists⟩,
   match assumption_2_6' with
   | ⟨x, hm, ha⟩ => ⟨x, hm, contract_exists.1, ha⟩⟩

/-- Corollary 3.4. Actual agreement is not sufficient: an agreed framework
that was never instituted, or that has been collectively rejected, does not
exist. -/
theorem agreement_not_sufficient (f : Framework) (_ : Agreed f)
    (h : ¬ Instituted f ∨ Rejected f) : ¬ Exists f := by
  intro he
  cases h with
  | inl hi => exact hi (requires_institution f he)
  | inr hr => exact rejection_ends f hr he

end Philosophy.POL_11

#print axioms Philosophy.POL_11.contract_exists
#print axioms Philosophy.POL_11.agreement_not_necessary
#print axioms Philosophy.POL_11.agreement_not_sufficient
