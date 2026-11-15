/-
REL-05 · Foreknowledge Without Fatalism
Formalization of Proposition 3.1, Theorem 3.2, Corollaries 3.3 and 3.4,
Proposition 3.5, Proposition 4.3 and Theorem 4.4.

Framework (Section 2). Worlds, an agent's choice at each world among a type
of options, and God's knowledge of that choice. The open alternatives of
the agent are the worlds that agree with the actual world on every fact
held fixed at the time of choice (Definition 2.1). The fatalist premise is
that God's knowledge is among those facts (Definition 2.6).

Framework (Section 4). A structural model with two equations: the agent's
choice is a function of her reasons and, possibly, of the content of
God's knowledge; the content of God's knowledge is the choice. Assumption
4.2 says that the content of God's knowledge is not an input to the agent's
mechanism.

What this file establishes. The fatalist argument is valid (Proposition
3.1); with the agent's ability (Assumption 2.5), for every option there is
an open alternative in which she takes it and God knows that she does
(Theorem 3.2), so the fatalist premise is false whenever there are two
options (Corollary 3.3), and divine knowledge of the choice is not a
temporally located fact prior to it (Corollary 3.4). The assumptions are
consistent (Proposition 3.5). In the structural model, intervening on the
choice changes God's knowledge while intervening on God's knowledge leaves
the choice unchanged (Theorem 4.4). It does not establish that the agent
has the ability of Assumption 2.5 (see ACT-01), nor that God is timeless
(see REL-19).
-/

namespace Philosophy.REL_05

/-! ## Section 2: worlds, choice and knowledge -/

/-- Possible worlds. -/
axiom World : Type

/-- The actual world. -/
axiom actual : World

/-- The options open to the agent at the time of choice. -/
axiom Choice : Type

/-- `choice w`: the option the agent takes at `w`. -/
axiom choice : World → Choice

/-- `Knows w c`: at `w`, God knows that the agent takes `c`. -/
axiom Knows : World → Choice → Prop

/-- Definition 2.1. `Open w`: `w` agrees with the actual world on every fact
held fixed at the time of the choice (a primitive here). -/
axiom Open : World → Prop

/-- Definition 2.2. The agent can take `c` if some open alternative is one
in which she takes `c`. -/
def CanTake (c : Choice) : Prop := ∃ w, Open w ∧ choice w = c

/-- Assumption 2.3. Divine knowledge is factive. -/
axiom factive : ∀ w c, Knows w c → choice w = c

/-- Assumption 2.4. God knows, at every world, the choice made there. -/
axiom omniscient : ∀ w, Knows w (choice w)

/-- Assumption 2.5 (ability). The agent can take each option. -/
axiom ability : ∀ c, CanTake c

/-- Definition 2.6. The fatalist premise: God's knowledge in every open
alternative is as it is at the actual world. -/
def FatalistPremise : Prop := ∀ w, Open w → ∀ c, (Knows w c ↔ Knows actual c)

/-- `Located`: divine knowledge of the choice is a temporally located fact
prior to the choice. -/
axiom Located : Prop

/-- Assumption 2.7 (fixity of the past). If divine knowledge of the choice
were a temporally located fact prior to the choice, it would be held fixed
in every open alternative. -/
axiom fixity : Located → FatalistPremise

/-- Proposition 3.1 (the fatalist argument is valid). Under the fatalist
premise, the agent takes the actual option in every open alternative. -/
theorem fatalism_valid (h : FatalistPremise) :
    ∀ w, Open w → choice w = choice actual := by
  intro w hw
  exact factive w (choice actual) ((h w hw (choice actual)).2 (omniscient actual))

/-- Theorem 3.2 (main result). For every option there is an open
alternative in which the agent takes it and God knows that she does. -/
theorem compatibility (c : Choice) :
    ∃ w, Open w ∧ choice w = c ∧ Knows w c := by
  obtain ⟨w, hw, hc⟩ := ability c
  exact ⟨w, hw, hc, hc ▸ omniscient w⟩

/-- Corollary 3.3. If there are two distinct options, the fatalist premise
is false: God's knowledge varies with the choice across open alternatives. -/
theorem fatalist_premise_false (c c' : Choice) (hne : c ≠ c') :
    ¬ FatalistPremise := by
  intro h
  obtain ⟨w, hw, hc⟩ := ability c
  obtain ⟨w', hw', hc'⟩ := ability c'
  apply hne
  rw [← hc, ← hc', fatalism_valid h w hw, fatalism_valid h w' hw']

/-- Corollary 3.4. If there are two distinct options, divine knowledge of
the choice is not a temporally located fact prior to the choice. -/
theorem not_located (c c' : Choice) (hne : c ≠ c') : ¬ Located :=
  fun h => fatalist_premise_false c c' hne (fixity h)

/-! ## Proposition 3.5: consistency

A model with two worlds, both open, in which the agent takes a different
option at each and God knows at each world exactly the option taken there.
Divine knowledge is not located, so Assumption 2.7 holds vacuously. -/

namespace Model

def choiceM (w : Bool) : Bool := w
def knowsM (w c : Bool) : Prop := c = w
def openM (_ : Bool) : Prop := True
def locatedM : Prop := False

/-- Proposition 3.5. Assumptions 2.3, 2.4, 2.5 and 2.7 hold in the model,
which has two distinct options. -/
theorem consistent :
    (∀ w c, knowsM w c → choiceM w = c) ∧
    (∀ w, knowsM w (choiceM w)) ∧
    (∀ c, ∃ w, openM w ∧ choiceM w = c) ∧
    (locatedM → ∀ w, openM w → ∀ c, (knowsM w c ↔ knowsM true c)) ∧
    true ≠ false := by
  refine ⟨fun _ _ h => h.symm, fun _ => rfl, fun c => ⟨c, trivial, rfl⟩,
    fun h => absurd h id, by decide⟩

end Model

/-! ## Section 4: the asymmetry of dependence -/

/-- The agent's reasons. -/
axiom Reasons : Type

/-- Definition 4.1 (choice equation). The agent's mechanism takes her
reasons and, possibly, the content of God's knowledge to a choice. -/
axiom choiceEq : Reasons → Choice → Choice

/-- Definition 4.1 (knowledge equation). The content of God's knowledge is
the choice (Assumptions 2.3 and 2.4). -/
def knowEq (c : Choice) : Choice := c

/-- Assumption 4.2 (inertness). The content of God's knowledge is not an
input to the agent's mechanism. -/
axiom inert : ∀ r k k', choiceEq r k = choiceEq r k'

/-- A solution of the model for reasons `r`: a choice and a knowledge
content satisfying both equations. -/
def Solution (r : Reasons) (c k : Choice) : Prop :=
  c = choiceEq r k ∧ k = knowEq c

/-- Proposition 4.3. For any reasons, the model has a solution, every
solution is unique, and in it God's knowledge is correct. -/
theorem solution (r : Reasons) :
    (∃ c k, Solution r c k) ∧
    (∀ c k c' k', Solution r c k → Solution r c' k' → c = c' ∧ k = k') ∧
    (∀ c k, Solution r c k → k = c) := by
  refine ⟨?_, ?_, fun c k h => h.2⟩
  · let c := choiceEq r (choice actual)
    exact ⟨c, c, inert r (choice actual) c, rfl⟩
  · intro c k c' k' ⟨h1, h2⟩ ⟨h1', h2'⟩
    have hc : c = c' := by rw [h1, h1', inert r k k']
    exact ⟨hc, by rw [h2, h2', hc]⟩

/-- Intervention on the choice: set it to `x`; knowledge follows its
equation. -/
def doChoice (x : Choice) : Choice × Choice := (x, knowEq x)

/-- Intervention on God's knowledge: set it to `y`; the choice follows its
equation. -/
noncomputable def doKnow (r : Reasons) (y : Choice) : Choice × Choice := (choiceEq r y, y)

/-- Theorem 4.4 (asymmetry). God's knowledge depends counterfactually on the
choice, and the choice does not depend counterfactually on God's
knowledge. -/
theorem asymmetry :
    (∀ x x' : Choice, x ≠ x' → (doChoice x).2 ≠ (doChoice x').2) ∧
    (∀ r y y', (doKnow r y).1 = (doKnow r y').1) :=
  ⟨fun _ _ h => h, fun r y y' => inert r y y'⟩

end Philosophy.REL_05

#print axioms Philosophy.REL_05.compatibility
#print axioms Philosophy.REL_05.not_located
#print axioms Philosophy.REL_05.asymmetry
#print axioms Philosophy.REL_05.Model.consistent
