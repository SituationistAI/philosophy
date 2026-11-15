/-
EPI-19 · Phenomenal Conservatism Defended
Formalization of Lemma 3.1, Theorem 3.2 and Corollaries 3.3 and 3.4.

What this file establishes. Given that every justified belief is grounded in
some seeming that confers justification (Assumption 2.3), that some belief is
justified (Assumption 2.4), and that whether a seeming confers prima facie
justification depends only on its assertive character, which every seeming
has (Definition 2.1 and Assumption 2.5), every seeming confers prima facie
justification (Principle P1, proved as Theorem 3.2). An undefeated
seeming that p gives justification for believing p (Corollary 3.3), and the
denial of phenomenal conservatism leaves no belief justified, including
itself (Corollary 3.4).

What it does not establish. Assumptions 2.3 to 2.5, which are argued for in
the manuscript; any account of what defeats prima facie justification; or
that the beliefs so justified are knowledge.
-/

namespace Philosophy.EPI_19

/-- Seemings: states in which it seems to a subject that p. -/
axiom Seeming : Type
/-- Beliefs. -/
axiom Belief : Type
/-- Contents of seemings. -/
axiom Content : Type

/-- The content of a seeming. -/
axiom content : Seeming → Content
/-- Definition 2.1. A seeming has assertive character: it presents its
content as true. -/
axiom Assertive : Seeming → Prop
/-- Definition 2.1: every seeming is assertive. -/
axiom seeming_assertive : ∀ s, Assertive s

/-- Definition 2.2. `Confers s`: the seeming `s` confers prima facie
justification for believing its content. -/
axiom Confers : Seeming → Prop
/-- `Defeated s`: the subject has a defeater for the justification `s`
would confer. -/
axiom Defeated : Seeming → Prop
/-- `JustifiedFor p`: the subject has justification for believing `p`. -/
axiom JustifiedFor : Content → Prop
/-- Definition 2.2 (prima facie). Conferred and undefeated justification is
justification. -/
axiom prima_facie : ∀ s, Confers s → ¬ Defeated s → JustifiedFor (content s)

/-- `Justified b`: the belief `b` is justified. -/
axiom Justified : Belief → Prop
/-- `GroundedIn b s`: the seeming `s` is among the ultimate grounds of `b`. -/
axiom GroundedIn : Belief → Seeming → Prop

/-- Assumption 2.3 (grounding). Every justified belief is ultimately grounded
in some seeming that confers justification. -/
axiom grounding : ∀ b, Justified b → ∃ s, GroundedIn b s ∧ Confers s

/-- Assumption 2.4 (non-scepticism). Some belief is justified. -/
axiom non_scepticism : ∃ b, Justified b

/-- Assumption 2.5 (character supervenience). Whether a seeming confers prima
facie justification depends only on its assertive character. -/
axiom character :
  ∀ s t, Assertive s → Assertive t → (Confers s ↔ Confers t)

/-- Lemma 3.1. If some belief is justified, some seeming confers prima facie
justification. -/
theorem some_confers (h : ∃ b, Justified b) : ∃ s, Confers s := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨s, _, hs⟩ := grounding b hb
  exact ⟨s, hs⟩

/-- Theorem 3.2 (phenomenal conservatism, Principle P1). Every seeming confers
prima facie justification for believing its content. -/
theorem phenomenal_conservatism : ∀ s : Seeming, Confers s := by
  intro t
  obtain ⟨s, hs⟩ := some_confers non_scepticism
  exact (character s t (seeming_assertive s) (seeming_assertive t)).1 hs

/-- Corollary 3.3. If it seems to the subject that `p` and she has no
defeater, she has justification for believing `p`. -/
theorem undefeated_seeming (s : Seeming) (h : ¬ Defeated s) :
    JustifiedFor (content s) :=
  prima_facie s (phenomenal_conservatism s) h

/-- Corollary 3.4 (self-defeat). If some seeming fails to confer prima facie
justification, no belief is justified; in particular, no belief in the
denial of phenomenal conservatism is. Does not use Assumption 2.4. -/
theorem self_defeat (h : ∃ s, ¬ Confers s) : ∀ b, ¬ Justified b := by
  intro b hb
  obtain ⟨t, ht⟩ := h
  obtain ⟨s, _, hs⟩ := grounding b hb
  exact ht ((character s t (seeming_assertive s) (seeming_assertive t)).1 hs)

end Philosophy.EPI_19

#print axioms Philosophy.EPI_19.phenomenal_conservatism
#print axioms Philosophy.EPI_19.undefeated_seeming
#print axioms Philosophy.EPI_19.self_defeat
