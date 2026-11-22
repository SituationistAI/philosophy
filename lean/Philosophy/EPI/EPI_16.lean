/-
EPI-16 · The Epistemic Costs of Prejudice
Formalization of Lemma 3.1, Theorem 3.2, Corollary 3.3, Proposition 3.4 and
Theorem 3.5.

What this file establishes. Testimonial exchanges are represented by
primitive reports, with Boolean primitives for whether the speaker knows, for
whether the credibility actually given meets the acceptance threshold, and for
whether the credibility warranted by the evidence meets it. Given the
transmission principle (Assumption 2.3, from EPI-08), the knowledge gained by
hearers plus the knowledge lost to credibility deficits equals the knowledge
that warranted credibility would have yielded plus the knowledge gained through
credibility excess (Theorem 3.2); without excess, the loss is exactly the
shortfall (Corollary 3.3); and the loss is positive exactly when some knowing
speaker suffers a deficit (Proposition 3.4). Lemma 3.1 shows that the reports
counted as lost are exactly those from which the hearer would have learned
under warranted credibility and does not. For hermeneutical gaps, given the
concept requirement (Assumption 2.6) and the audience assumption
(Assumption 2.7), each gap costs the subject's own knowledge and that of every
hearer she would have informed (Theorem 3.5).

What it does not establish. That the losses are wrongs (Principle P1 and
Theorem 3.6 are argued in prose); that credibility deficits are caused by
prejudice in any actual case; the size of the losses in any actual community.
-/

namespace Philosophy.EPI_16

/-- Counting the members of a list that satisfy a Boolean test. -/
def count {α : Type} (f : α → Bool) : List α → Nat
  | [] => 0
  | a :: as => (bif f a then 1 else 0) + count f as

/-- Summing a numerical function over a list. -/
def sumN {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | a :: as => f a + sumN f as

noncomputable section

/-! Testimonial injustice. -/

/-- Definition 2.1. Testimonial reports: a speaker tells a hearer that `p`. -/
axiom Report : Type

/-- Definition 2.1. The speaker knows the proposition she reports. -/
axiom speakerKnows : Report → Bool
/-- Definition 2.1. The credibility the hearer actually gives meets the
threshold for acceptance. -/
axiom credible : Report → Bool
/-- Definition 2.1. The credibility warranted by the hearer's evidence about
the speaker meets the threshold for acceptance. -/
axiom warranted : Report → Bool

/-- The hearer comes to know the reported proposition from the report. -/
axiom learns : Report → Bool
/-- The hearer would come to know it, were she to give warranted credibility. -/
axiom learnsFair : Report → Bool

/-- Assumption 2.3 (transmission, EPI-08), actual case: the hearer comes to
know from the report exactly when the speaker knows and the hearer accepts. -/
axiom transmission : ∀ r, learns r = (speakerKnows r && credible r)
/-- Assumption 2.3 (transmission, EPI-08), counterfactual case with warranted
credibility. -/
axiom transmission_fair : ∀ r, learnsFair r = (speakerKnows r && warranted r)

/-- Definition 2.2. Credibility deficit: warranted credibility meets the
threshold, actual credibility does not. -/
def deficit (r : Report) : Bool := warranted r && !credible r
/-- Definition 2.2. Credibility excess: actual credibility meets the threshold,
warranted credibility does not. -/
def excess (r : Report) : Bool := credible r && !warranted r

/-- Definition 2.4. Knowledge gained, knowledge that warranted credibility
would yield, knowledge lost to deficits, knowledge gained through excess. -/
def gained (rs : List Report) : Nat := count learns rs
def gainedFair (rs : List Report) : Nat := count learnsFair rs
def lost (rs : List Report) : Nat := count (fun r => speakerKnows r && deficit r) rs
def excessGain (rs : List Report) : Nat := count (fun r => speakerKnows r && excess r) rs

/-- Lemma 3.1 (what is lost): a report counts as lost exactly when the hearer
would learn from it under warranted credibility and does not learn from it. -/
theorem lost_eq (rs : List Report) :
    lost rs = count (fun r => learnsFair r && !learns r) rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [lost, count, deficit] at *
    rw [ih, transmission r, transmission_fair r]
    cases speakerKnows r <;> cases credible r <;> cases warranted r <;> rfl

/-- Theorem 3.2 (accounting identity). -/
theorem accounting (rs : List Report) :
    gained rs + lost rs = gainedFair rs + excessGain rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [gained, gainedFair, lost, excessGain, count, deficit, excess] at *
    rw [transmission r, transmission_fair r]
    cases h1 : speakerKnows r <;> cases h2 : credible r <;> cases h3 : warranted r <;>
      simp <;> omega

/-- Corollary 3.3. Without credibility excess, the knowledge lost to deficits
is exactly the shortfall from the knowledge warranted credibility would yield. -/
theorem shortfall (rs : List Report) (h : excessGain rs = 0) :
    gainedFair rs = gained rs + lost rs := by
  have := accounting rs
  omega

/-- Lemma used for Proposition 3.4: a count is positive exactly when some
member passes the test. -/
theorem count_pos {α : Type} (f : α → Bool) (as : List α) :
    0 < count f as ↔ ∃ a, a ∈ as ∧ f a = true := by
  induction as with
  | nil => simp [count]
  | cons a as ih =>
    simp only [count]
    cases h : f a
    · simp only [cond_false, Nat.zero_add, ih]
      constructor
      · intro ⟨b, hb, hfb⟩; exact ⟨b, List.mem_cons_of_mem a hb, hfb⟩
      · intro ⟨b, hb, hfb⟩
        cases List.mem_cons.mp hb with
        | inl heq => subst heq; rw [h] at hfb; cases hfb
        | inr hm => exact ⟨b, hm, hfb⟩
    · simp only [cond_true]
      constructor
      · intro _; exact ⟨a, List.mem_cons_self a as, h⟩
      · intro _; omega

/-- Proposition 3.4 (the loss is positive exactly when some knowing speaker
suffers a credibility deficit). -/
theorem loss_positive (rs : List Report) :
    0 < lost rs ↔ ∃ r, r ∈ rs ∧ speakerKnows r = true ∧ deficit r = true := by
  unfold lost
  rw [count_pos]
  constructor
  · intro ⟨r, hr, h⟩
    exact ⟨r, hr, (Bool.and_eq_true _ _).mp h |>.1, (Bool.and_eq_true _ _).mp h |>.2⟩
  · intro ⟨r, hr, h1, h2⟩
    exact ⟨r, hr, by rw [h1, h2]; rfl⟩

/-! Hermeneutical injustice. -/

/-- Definition 2.5. Experiences of a subject that bear on a proposition about
her situation. -/
axiom Experience : Type
/-- Definition 2.5. The collective resources supply the concept needed to
form the belief. -/
axiom conceptAvailable : Experience → Bool
/-- Definition 2.5. With the concept, the subject would know the proposition. -/
axiom wouldKnow : Experience → Bool
/-- The subject knows the proposition. -/
axiom knowsExp : Experience → Bool

/-- Assumption 2.6 (concept requirement). -/
axiom concept_requirement : ∀ e, knowsExp e = (conceptAvailable e && wouldKnow e)

/-- Assumption 2.7: the number of hearers the subject would inform. -/
axiom audience : Nat
/-- Hearers who come to know, actually and with the concept available. -/
axiom hearersKnow : Experience → Nat
axiom hearersKnowFair : Experience → Nat
/-- Assumption 2.7 (audience), actual case. -/
axiom audience_actual : ∀ e, hearersKnow e = bif knowsExp e then audience else 0
/-- Assumption 2.7 (audience), case with the concept available. -/
axiom audience_fair : ∀ e, hearersKnowFair e = bif wouldKnow e then audience else 0

/-- Definition 2.8. Total knowledge, actual and with adequate resources, and
the number of hermeneutical gaps. -/
def total (es : List Experience) : Nat :=
  sumN (fun e => (bif knowsExp e then 1 else 0) + hearersKnow e) es
def totalFair (es : List Experience) : Nat :=
  sumN (fun e => (bif wouldKnow e then 1 else 0) + hearersKnowFair e) es
def gaps (es : List Experience) : Nat :=
  count (fun e => wouldKnow e && !conceptAvailable e) es

/-- Theorem 3.5 (hermeneutical loss). -/
theorem hermeneutical_loss (es : List Experience) :
    totalFair es = total es + (audience + 1) * gaps es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [totalFair, total, gaps, count, sumN] at *
    rw [audience_actual e, audience_fair e, concept_requirement e, ih]
    cases h1 : conceptAvailable e <;> cases h2 : wouldKnow e <;>
      simp [Nat.mul_add] <;> omega

end

end Philosophy.EPI_16

#print axioms Philosophy.EPI_16.lost_eq
#print axioms Philosophy.EPI_16.accounting
#print axioms Philosophy.EPI_16.loss_positive
#print axioms Philosophy.EPI_16.hermeneutical_loss
