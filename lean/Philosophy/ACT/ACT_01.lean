/-
ACT-01 · On Free Will
Formalization of the main argument (Volume I, Chapter 3, Theorem 3.2).

Worlds carry a determinism flag. Reasons-responsiveness and ownership of the
mechanism of action are primitive predicates on worlds (Definitions 2.2 and
2.3); free will is defined from them (Definition 2.4).

What this file establishes. The compatibility thesis follows from the
independence assumption (Assumption 3.1) and from nothing else. It does not
establish the independence assumption, which Volume II defends against the
consequence argument and Volume III against the luck objection.
-/

namespace Philosophy.ACT_01

/-- Possible worlds, each containing a designated agent. -/
axiom World : Type

/-- Whether a world is deterministic. -/
axiom deterministic : World → Bool

/-- Definition 2.2. The agent's mechanism is reasons-responsive. -/
axiom ReasonsResponsive : World → Prop

/-- Definition 2.3. The agent's mechanism is her own. -/
axiom Owned : World → Prop

/-- Determinism as a proposition. -/
def Deterministic (w : World) : Prop := deterministic w = true

/-- Definition 2.4. The agent of `w` has free will. -/
def FreeWill (w : World) : Prop := ReasonsResponsive w ∧ Owned w

/-- Assumption 3.1 (independence). For each value of the determinism flag,
some world with that value contains an agent with a reasons-responsive
mechanism of her own. -/
axiom independence :
  ∀ b : Bool, ∃ w, deterministic w = b ∧ ReasonsResponsive w ∧ Owned w

/-- Theorem 3.2 (compatibility). -/
theorem compatible_both :
    (∃ w, Deterministic w ∧ FreeWill w) ∧ (∃ w, ¬ Deterministic w ∧ FreeWill w) := by
  constructor
  · obtain ⟨w, hd, hr, ho⟩ := independence true
    exact ⟨w, hd, hr, ho⟩
  · obtain ⟨w, hd, hr, ho⟩ := independence false
    exact ⟨w, by simp [Deterministic, hd], hr, ho⟩

end Philosophy.ACT_01

#print axioms Philosophy.ACT_01.compatible_both
