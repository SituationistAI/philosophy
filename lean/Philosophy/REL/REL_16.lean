/-
REL-16 · Against Divine Simplicity
Formalization of Lemma 3.1 and Theorem 3.2.

Framework. Propositions are sets of possible worlds. God's knowledge at a
world is the set of propositions God knows there. The doctrine of divine
simplicity is represented by its weakest consequence used in the argument:
God's knowledge is fixed by God's essence (Definition 2.1). The essence is
the same at every world (Assumption 2.2).

What this file establishes. Given that the divine essence does not vary
across worlds, that knowledge is factive, that God knows every truth and
that some truth is contingent, the simplicity thesis is false. It does not
establish any of these premises; Section 4 of the manuscript defends them
against the replies of the tradition.
-/

namespace Philosophy.REL_16

/-- Possible worlds. -/
axiom World : Type

/-- Propositions, as sets of worlds. -/
abbrev WProp := World → Prop

/-- Essences (of God), whatever they are. -/
axiom Essence : Type

/-- `ess w`: God's essence at `w`. -/
axiom ess : World → Essence

/-- `Knows w p`: at `w`, God knows `p`. -/
axiom Knows : World → WProp → Prop

/-- Definition 2.1 (simplicity thesis, weakest form used). God's knowledge
is nothing over and above God's essence: some function takes the essence
to the knowledge, at every world. -/
def Simple : Prop :=
  ∃ f : Essence → (WProp → Prop), ∀ w, Knows w = f (ess w)

/-- Assumption 2.2. The divine essence is the same at every world. -/
axiom ess_rigid : ∀ w w', ess w = ess w'

/-- Assumption 2.3. Knowledge is factive. -/
axiom factive : ∀ w p, Knows w p → p w

/-- Assumption 2.4. God knows every truth. -/
axiom omniscient : ∀ w (p : WProp), p w → Knows w p

/-- Assumption 2.5. Some truth is contingent. -/
axiom contingent : ∃ (p : WProp) (w w' : World), p w ∧ ¬ p w'

/-- Lemma 3.1. If God is simple, God knows the same propositions at every
world. -/
theorem invariance (h : Simple) (w w' : World) : Knows w = Knows w' := by
  obtain ⟨f, hf⟩ := h
  rw [hf w, hf w', ess_rigid w w']

/-- Theorem 3.2 (main result). The simplicity thesis is false. -/
theorem not_simple : ¬ Simple := by
  intro h
  obtain ⟨p, w, w', hp, hnp⟩ := contingent
  have hk : Knows w p := omniscient w p hp
  rw [invariance h w w'] at hk
  exact hnp (factive w' p hk)

end Philosophy.REL_16

#print axioms Philosophy.REL_16.not_simple
