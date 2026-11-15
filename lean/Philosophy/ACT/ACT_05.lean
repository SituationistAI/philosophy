/-
ACT-05 · Libet Does Not Refute Free Will
Formalization of Theorem 3.1 and Corollary 3.2.

Events in a Libet trial are primitive and carry times. The readiness
potential (RP), the decision to flex (W), the decision to take part, and the
locus of the action's reasons-responsiveness (Definition 2.3) are named
events; freedom and reasons-responsiveness are primitive propositions about
the flexing.

What this file establishes. From Libet's timing data (Assumption 2.4), the
protocol (Assumption 2.5), the location of the locus (Assumption 2.6), the
reasons-responsiveness account of free action (Principle P1, from ACT-01) and
the ordinariness of the participant (Assumption 2.7), it follows that the RP
precedes the decision to flex but not the decision that is the locus of the
action's reasons-responsiveness, and that the flexing is free. It also shows
that Libet's argument, with its precursor principle (P2) and data, is valid
when the locus is taken to be the decision to flex, so that the reply turns
on Assumption 2.6. It does not establish
any of the premises; in particular it does not establish Assumption 2.6,
which the manuscript defends in Section 4.
-/

namespace Philosophy.ACT_05

/-- Events of a Libet trial. -/
axiom Event : Type

/-- The time of an event (in milliseconds relative to the movement). -/
axiom time : Event → Int

/-- Onset of the readiness potential. -/
axiom rp : Event

/-- Definition 2.2. The decision to flex now (Libet's W). -/
axiom flexDecision : Event

/-- Definition 2.1. The decision to take part in the experiment. -/
axiom participation : Event

/-- Definition 2.3. The locus of the flexing's reasons-responsiveness: the
decision through which the reasons bearing on the flexing operate. -/
axiom locus : Event

/-- The participant's mechanism is reasons-responsive and her own. -/
axiom ReasonsResponsive : Prop

/-- The flexing is free. -/
axiom Free : Prop

/-- Assumption 2.4 (Libet's data). The RP begins before the decision to flex. -/
axiom libet_data : time rp < time flexDecision

/-- Assumption 2.5 (protocol). The decision to take part precedes the RP. -/
axiom protocol : time participation < time rp

/-- Assumption 2.6 (locus). The locus of the flexing's reasons-responsiveness
is the decision to take part. -/
axiom locus_is_participation : locus = participation

/-- Principle P1 (ACT-01). An action issuing from a reasons-responsive
mechanism of the agent's own is free. -/
axiom free_of_rr : ReasonsResponsive → Free

/-- Assumption 2.7. The participant's mechanism is reasons-responsive and her
own. -/
axiom ordinary_participant : ReasonsResponsive

/-- Theorem 3.1. The RP precedes the decision to flex, does not precede the
decision that is the locus of the action's reasons-responsiveness, and the
flexing is free. -/
theorem libet_no_refutation :
    time rp < time flexDecision ∧ ¬ time rp < time locus ∧ Free := by
  refine ⟨libet_data, ?_, free_of_rr ordinary_participant⟩
  rw [locus_is_participation]
  have h := protocol
  omega

/-- Corollary 3.2. Libet's argument is valid on its own reading: granting
the precursor principle P2 (if an unconscious precursor precedes the locus,
the mechanism is not reasons-responsive) and taking the locus to be the
decision to flex, the data yield that the mechanism is not
reasons-responsive. Assumption 2.6 is therefore the premise on which the
reply turns. -/
theorem precursor_with_flex_locus
    (p2 : time rp < time locus → ¬ ReasonsResponsive)
    (h : locus = flexDecision) : ¬ ReasonsResponsive := by
  apply p2
  rw [h]
  exact libet_data

end Philosophy.ACT_05

#print axioms Philosophy.ACT_05.libet_no_refutation
#print axioms Philosophy.ACT_05.precursor_with_flex_locus
