/-
MTH-06 · The Continuum Hypothesis Is False
Formalization of Theorem 5.1, Corollaries 5.2 and 5.3 and Proposition 5.4.

Sentences of the language of set theory are a primitive type with a
negation operation. `Proves A φ` means that ZFC together with the axiom `A`
proves `φ`. Truth, justification and independent motivation (with respect
to CH, Definition 3.3) are primitive predicates.

What this file establishes. Given the transfer and coherence principles
(P2, P3) and the independent motivation of Martin's Maximum (Assumption
4.2), the negation of CH is justified and CH is not; given determinacy (P1)
and the soundness of ZFC (Assumption 3.4), CH is false if any of MM, Woodin's
axiom (*) and Freiling's axiom of symmetry is true, and the second-order
sentence expressing not-CH is then valid; and no axiom implying CH, in
particular V = Ultimate-L, is justified.

What it does not establish. The set-theoretic results (Lemmas 4.1, 4.3,
4.4 and the implication from V = Ultimate-L to CH) are imported as axioms:
they are theorems proved in the cited literature, and no forcing argument
is formalized here. The philosophical premises are axioms and are not
proved.
-/

namespace Philosophy.MTH_06

/-- Sentences of the language of set theory. -/
axiom Sent : Type

/-- Negation of a sentence. -/
axiom neg : Sent → Sent

/-- Definition 3.1. The continuum hypothesis. -/
axiom CH : Sent

/-- Martin's Maximum, Woodin's axiom (*), Freiling's axiom of symmetry,
and the axiom V = Ultimate-L. -/
axiom MM : Sent
axiom Star : Sent
axiom AX : Sent
axiom UL : Sent

/-- `Proves A φ`: ZFC together with the axiom `A` proves `φ`. -/
axiom Proves : Sent → Sent → Prop

/-- Truth (in the universe of sets). -/
axiom True' : Sent → Prop

/-- Definition 3.3. Independent motivation with respect to CH. -/
axiom Motivated : Sent → Prop

/-- Justification (Definition 3.2: intrinsic or extrinsic). -/
axiom Justified : Sent → Prop

/-- Principle P1 (Determinacy). Exactly one of a sentence and its negation
is true; we need it for CH. -/
axiom principle_P1 : True' (neg CH) ↔ ¬ True' CH

/-- Principle P2, first clause (Transfer). An independently motivated axiom
is justified. -/
axiom principle_P2a : ∀ A, Motivated A → Justified A

/-- Principle P2, second clause (Transfer). Justification is closed under
consequence in ZFC. -/
axiom principle_P2b : ∀ A φ, Justified A → Proves A φ → Justified φ

/-- Principle P3 (Coherence). No sentence and its negation are both
justified. -/
axiom principle_P3 : ∀ φ, ¬ (Justified φ ∧ Justified (neg φ))

/-- Assumption 3.4 (Soundness of ZFC). -/
axiom assumption_3_4 : ∀ A φ, Proves A φ → True' A → True' φ

/-- Lemma 4.1 (Foreman, Magidor and Shelah). ZFC + MM proves not-CH.
Imported from the literature. -/
axiom lemma_4_1 : Proves MM (neg CH)

/-- Assumption 4.2. Martin's Maximum is independently motivated with
respect to CH. -/
axiom assumption_4_2 : Motivated MM

/-- Lemma 4.3 (Woodin). ZFC + (*) proves not-CH. Imported from the
literature. -/
axiom lemma_4_3 : Proves Star (neg CH)

/-- Lemma 4.4 (Sierpinski, Freiling), the direction used. ZFC + AX proves
not-CH. Imported from the literature. -/
axiom lemma_4_4 : Proves AX (neg CH)

/-- Woodin: V = Ultimate-L implies CH (Section 5.1). Imported from the
literature. -/
axiom ultimate_L_CH : Proves UL CH

/-- Second-order sentences, their validity in the standard semantics, and
the sentence expressing not-CH (Section 5). -/
axiom Sent2 : Type
axiom Valid2 : Sent2 → Prop
axiom sigmaNotCH : Sent2

/-- Zermelo's quasi-categoricity theorem as used in Section 3.1: the
second-order sentence for not-CH is valid exactly when not-CH is true. -/
axiom sigma_spec : Valid2 sigmaNotCH ↔ True' (neg CH)

/-- Theorem 5.1. Not-CH is justified and CH is not. -/
theorem justified_notCH : Justified (neg CH) ∧ ¬ Justified CH := by
  have h : Justified (neg CH) :=
    principle_P2b MM (neg CH) (principle_P2a MM assumption_4_2) lemma_4_1
  exact ⟨h, fun hc => principle_P3 CH ⟨hc, h⟩⟩

/-- Corollary 5.2 (Robustness). If any of MM, (*) and AX is true, CH is
false. -/
theorem robust (h : True' MM ∨ True' Star ∨ True' AX) : ¬ True' CH := by
  apply principle_P1.mp
  rcases h with h | h | h
  · exact assumption_3_4 _ _ lemma_4_1 h
  · exact assumption_3_4 _ _ lemma_4_3 h
  · exact assumption_3_4 _ _ lemma_4_4 h

/-- Corollary 5.3. If any of MM, (*) and AX is true, the second-order
sentence expressing not-CH is valid, and so (by LOG-09) a logical truth. -/
theorem logical_truth (h : True' MM ∨ True' Star ∨ True' AX) :
    Valid2 sigmaNotCH :=
  sigma_spec.mpr (principle_P1.mpr (robust h))

/-- Proposition 5.4, general form. No axiom that proves CH is justified. -/
theorem no_justified_CH_axiom (B : Sent) (hB : Proves B CH) :
    ¬ Justified B :=
  fun hj => justified_notCH.2 (principle_P2b B CH hj hB)

/-- Proposition 5.4. V = Ultimate-L is not justified. -/
theorem rival_excluded : ¬ Justified UL :=
  no_justified_CH_axiom UL ultimate_L_CH

end Philosophy.MTH_06

#print axioms Philosophy.MTH_06.justified_notCH
#print axioms Philosophy.MTH_06.robust
#print axioms Philosophy.MTH_06.logical_truth
#print axioms Philosophy.MTH_06.rival_excluded
