/-
MTE-05 · Companions in Guilt and the Error Theory
Formalization of Proposition 4.1, Theorem 4.2, Corollaries 4.3 and 4.4 and
Proposition 4.5.

A domain of discourse is queer, in Mackie's sense, if its putative facts
bear three marks: they are unlike anything else in the natural order
(metaphysical mark), they are knowable only through a faculty unlike
ordinary perception and inference (epistemic mark), and their recognition
rationally requires a response of every rational agent independently of
her desires (mark of authority) (Definition 2.2). The queerness principle
(Principle P1) says that no queer domain has facts. The presupposition
assumption (Assumption 2.3) says that a domain whose positive claims
presuppose facts of its kind, and which has none, has only false positive
claims.

What this file establishes. Given that mathematics bears the three marks
(Assumptions 3.1, 3.2 and 3.3) and that not all mathematical claims are
false (Assumption 3.4), the queerness principle entails that all positive
mathematical claims are false (Proposition 4.1) and is therefore false
(Theorem 4.2). The argument from queerness, which needs both the principle
and the queerness of morality, has a false premise (Corollary 4.3). No
restriction of the principle that is implied by the three marks fares
better (Corollary 4.4), and any restriction that exempts mathematics while
applying to morality uses a criterion that the three marks do not imply
(Proposition 4.5).

What it does not establish. It does not establish the four assumptions
about mathematics, which are defended in Section 3 with MTH-01, MTH-02 and
MTH-16. It does not by itself establish that some moral claims are true;
that conclusion is drawn in Section 5 from MTE-01.
-/

namespace Philosophy.MTE_05

/-- Domains of discourse. -/
axiom Domain : Type

/-- Morality and mathematics. -/
axiom morality : Domain
axiom mathematics : Domain

/-- Definition 2.2 (a): the metaphysical mark. -/
axiom Unlike : Domain → Prop
/-- Definition 2.2 (b): the epistemic mark. -/
axiom SpecialAccess : Domain → Prop
/-- Definition 2.2 (c): the mark of authority. -/
axiom Authority : Domain → Prop

/-- Definition 2.2. Queerness: the three marks together. -/
def Queer (d : Domain) : Prop := Unlike d ∧ SpecialAccess d ∧ Authority d

/-- Definition 2.1 (a): the domain contains facts of the kind its positive
claims presuppose. -/
axiom HasFacts : Domain → Prop
/-- Definition 2.1 (b): every positive claim of the domain is false. -/
axiom AllFalse : Domain → Prop

/-- Principle P1 (the queerness principle). -/
def P1 : Prop := ∀ d, Queer d → ¬ HasFacts d

/-- Assumption 2.3 (presupposition). A domain without the facts its positive
claims presuppose has only false positive claims. -/
axiom assumption_2_3 : ∀ d, ¬ HasFacts d → AllFalse d

/-- Assumption 3.1. Mathematics bears the metaphysical mark. -/
axiom assumption_3_1 : Unlike mathematics
/-- Assumption 3.2. Mathematics bears the epistemic mark. -/
axiom assumption_3_2 : SpecialAccess mathematics
/-- Assumption 3.3. Mathematics bears the mark of authority. -/
axiom assumption_3_3 : Authority mathematics
/-- Assumption 3.4 (MTH-01, MTH-16). Not every positive mathematical claim is
false. -/
axiom assumption_3_4 : ¬ AllFalse mathematics

/-- Mathematics is queer by Mackie's criteria. -/
theorem math_queer : Queer mathematics :=
  ⟨assumption_3_1, assumption_3_2, assumption_3_3⟩

/-- Proposition 4.1 (the argument proves too much). The queerness principle
entails that every positive mathematical claim is false. -/
theorem proves_too_much : P1 → AllFalse mathematics :=
  fun h => assumption_2_3 mathematics (h mathematics math_queer)

/-- Theorem 4.2. The queerness principle is false. -/
theorem p1_false : ¬ P1 :=
  fun h => assumption_3_4 (proves_too_much h)

/-- Corollary 4.3. The premises of the argument from queerness, the principle
and the queerness of morality, are not both true. -/
theorem argument_unsound : ¬ (P1 ∧ Queer morality) :=
  fun h => p1_false h.1

/-- Corollary 4.4. No principle whose antecedent is implied by the three
marks is true. -/
theorem no_weaker_principle (R : Domain → Prop) (hR : ∀ d, Queer d → R d) :
    ¬ (∀ d, R d → ¬ HasFacts d) :=
  fun h => assumption_3_4 (assumption_2_3 mathematics (h mathematics (hR mathematics math_queer)))

/-- Proposition 4.5. A criterion that applies to morality and exempts
mathematics is not implied by the three marks. -/
theorem restriction_adds_feature (R : Domain → Prop)
    (_hmor : R morality) (hmath : ¬ R mathematics) :
    ¬ (∀ d, Queer d → R d) :=
  fun h => hmath (h mathematics math_queer)

end Philosophy.MTE_05

#print axioms Philosophy.MTE_05.p1_false
#print axioms Philosophy.MTE_05.no_weaker_principle
