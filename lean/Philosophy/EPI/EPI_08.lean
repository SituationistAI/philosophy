/-
EPI-08 · Testimony Transmits Knowledge
Formalization of Lemma 3.1, Theorems 3.2 and 3.3 and Corollary 3.4.

A single proposition p is fixed. Agents believe p, are justified in
believing it, and hold beliefs that are safe or unsafe; knowledge is safe,
justified, true belief (Definition 2.1, following EPI-01). `Receives s h`
says that h takes up s's telling that p, either believing p on its basis or
relaying it. Upstream is the reflexive-transitive closure of that relation
(Definition 2.3).

What this file establishes. Given the assumptions of Section 2, (i) every
safe telling has, at or upstream of the teller, a subject with a safe
belief that p (Lemma 3.1); (ii) a justified hearer who believes what a
knowing speaker tells her knows it (Theorem 3.2, transmission); (iii) a
hearer who knows by testimony either has an upstream source who knows, or
contributes safety from her own roots, or supplies a justification that an
upstream safe believer lacks (Theorem 3.3, no generation); and (iv) pure
testimony from sources whose safe beliefs are justified yields knowledge
only where some upstream subject knows (Corollary 3.4).

What it does not establish. It does not establish the assumptions, in
particular that safety is inherited only through safe tellings (Assumption
2.5) or that testimonial chains are finite (Assumption 2.8). No axiom links
the hearer's justification to the speaker's: justification is the hearer's
own, as internalism about justification (EPI-06) requires.
-/

namespace Philosophy.EPI_08

/-- Agents: speakers, hearers and relays. -/
axiom Agent : Type

/-- The agent believes p. -/
axiom Believes : Agent → Prop

/-- The agent is justified in believing p. -/
axiom Justified : Agent → Prop

/-- The agent's belief that p is safe (Definition 2.1, after EPI-01). -/
axiom Safe : Agent → Prop

/-- p is true. -/
axiom Truth : Prop

/-- Definition 2.2. `Receives s h`: h takes up s's telling that p. -/
axiom Receives : Agent → Agent → Prop

/-- Definition 2.2. The agent's telling that p is safe. -/
axiom TellsSafely : Agent → Prop

/-- Definition 2.4. The agent has safe roots of her own, beyond the telling,
sufficient to make her belief that p safe. -/
axiom Own : Agent → Prop

/-- Assumption 2.8 (finite chains). Each agent has a depth, and a teller is
shallower than anyone who takes up her telling. -/
axiom depth : Agent → Nat

/-- Definition 2.1. Knowledge is safe, justified, true belief (EPI-01). -/
def Knows (a : Agent) : Prop := Believes a ∧ Justified a ∧ Safe a ∧ Truth

/-- Definition 2.3. `Upstream u w`: u is w, or lies earlier than w in a
chain of tellings ending at w. -/
inductive Upstream : Agent → Agent → Prop
  | refl (a : Agent) : Upstream a a
  | step {u v w : Agent} : Upstream u v → Receives v w → Upstream u w

/-- Assumption 2.5 (inheritance). A hearer's belief taken up from a telling
is safe only if the telling is safe or the hearer has safe roots of her own. -/
axiom inheritance : ∀ s h, Receives s h → Safe h → TellsSafely s ∨ Own h

/-- Assumption 2.6 (sources of safe tellings). A safe telling expresses the
teller's safe belief, or relays a safe telling taken up from someone else. -/
axiom safe_telling_source :
  ∀ s, TellsSafely s → (Believes s ∧ Safe s) ∨ ∃ u, Receives u s ∧ TellsSafely u

/-- Assumption 2.7 (uptake). A belief taken up from a safe telling is safe,
and a sincere telling that expresses a safe belief is safe. -/
axiom uptake : ∀ s h, Receives s h → TellsSafely s → Believes h → Safe h
axiom sincerity : ∀ s, Believes s → Safe s → TellsSafely s

/-- Assumption 2.8 (finite chains). -/
axiom depth_lt : ∀ u s, Receives u s → depth u < depth s

/-- Lemma 3.1 (grounding). Every safe telling has, at or upstream of the
teller, an agent with a safe belief that p. -/
theorem grounding : ∀ s, TellsSafely s → ∃ u, Upstream u s ∧ Believes u ∧ Safe u := by
  have key : ∀ n, ∀ s, depth s < n → TellsSafely s →
      ∃ u, Upstream u s ∧ Believes u ∧ Safe u := by
    intro n
    induction n with
    | zero => intro s hd _; exact absurd hd (Nat.not_lt_zero _)
    | succ n ih =>
      intro s hd ht
      cases safe_telling_source s ht with
      | inl hb => exact ⟨s, Upstream.refl s, hb.1, hb.2⟩
      | inr hu =>
        obtain ⟨u, hr, htu⟩ := hu
        have hlt := depth_lt u s hr
        obtain ⟨v, hv, hb, hsf⟩ := ih u (by omega) htu
        exact ⟨v, Upstream.step hv hr, hb, hsf⟩
  intro s ht
  exact key (depth s + 1) s (Nat.lt_succ_self _) ht

/-- Theorem 3.2 (transmission). A hearer who believes p on the basis of a
knowing speaker's telling, and is justified in so believing, knows p. -/
theorem transmission (s h : Agent) (hr : Receives s h) (hks : Knows s)
    (hb : Believes h) (hj : Justified h) : Knows h :=
  ⟨hb, hj, uptake s h hr (sincerity s hks.1 hks.2.2.1) hb, hks.2.2.2⟩

/-- Theorem 3.3 (no generation). If a hearer knows p by taking it up from s,
then either some agent at or upstream of s knows p (transmission), or the
hearer has safe roots of her own that make her belief safe, or some agent at or
upstream of s has a safe belief that p that is not justified, while the
hearer's belief is justified (generation by the hearer). -/
theorem no_generation (s h : Agent) (hr : Receives s h) (hk : Knows h) :
    (∃ u, Upstream u s ∧ Knows u) ∨ Own h ∨
    (∃ u, Upstream u s ∧ Believes u ∧ Safe u ∧ ¬ Justified u ∧ Justified h) := by
  cases inheritance s h hr hk.2.2.1 with
  | inr ho => exact Or.inr (Or.inl ho)
  | inl ht =>
    obtain ⟨u, hu, hb, hsf⟩ := grounding s ht
    cases Classical.em (Justified u) with
    | inl hj => exact Or.inl ⟨u, hu, hb, hj, hsf, hk.2.2.2⟩
    | inr hn => exact Or.inr (Or.inr ⟨u, hu, hb, hsf, hn, hk.2.1⟩)

/-- Corollary 3.4 (pure testimony). If the hearer contributes no safety of
her own and every safe believer upstream of the speaker is justified, a
hearer who knows by testimony has an upstream source who knows. -/
theorem pure_testimony (s h : Agent) (hr : Receives s h) (hk : Knows h)
    (hno : ¬ Own h)
    (hjust : ∀ u, Upstream u s → Believes u → Safe u → Justified u) :
    ∃ u, Upstream u s ∧ Knows u := by
  cases no_generation s h hr hk with
  | inl h1 => exact h1
  | inr h2 =>
    cases h2 with
    | inl ho => exact absurd ho hno
    | inr hg =>
      obtain ⟨u, hu, hb, hsf, hn, _⟩ := hg
      exact absurd (hjust u hu hb hsf) hn

end Philosophy.EPI_08

#print axioms Philosophy.EPI_08.transmission
#print axioms Philosophy.EPI_08.no_generation
#print axioms Philosophy.EPI_08.pure_testimony
