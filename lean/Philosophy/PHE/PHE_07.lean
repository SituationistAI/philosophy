/-
PHE-07 · Anticipatory Resoluteness as a Limit Concept
Formalization of Lemmas 3.1 and 3.2 and Theorem 3.3.

A history of an existing agent assigns to each time (a natural number) whether
the agent is then authentically anticipating death (`true`) or has fallen
back into the public time of the "they" (`false`). Which histories are open
to a finite, thrown agent is a primitive (`Admissible`).

What this file establishes. Given that in every admissible history each time
is followed by a lapse (Assumption 2.4) and that some admissible history
returns to anticipation after every time (Assumption 2.5), authentic
being-towards-death is possible as an orientation (Definition 2.2) and not
possible as a stable achievement (Definition 2.3). It does not establish the
two assumptions, which the manuscript defends from Heidegger's analysis of
falling and of public time, nor anything about anxiety, which is discussed
only in the manuscript.
-/

namespace Philosophy.PHE_07

/-- Definition 2.1. A history: at each time, whether the agent is
authentically anticipating death. -/
abbrev History := Nat → Bool

/-- The histories open to a finite, thrown agent. -/
axiom Admissible : History → Prop

/-- Definition 2.2. Orientation: after every time, the agent returns to
anticipation. -/
def Orientation (h : History) : Prop := ∀ t, ∃ t', t' ≥ t ∧ h t' = true

/-- Definition 2.3. Stable achievement: from some time on, the agent
anticipates at every time. -/
def StableAchievement (h : History) : Prop := ∃ t0, ∀ t, t ≥ t0 → h t = true

/-- Assumption 2.4 (falling into public time). In every admissible history,
each time is followed by a lapse. -/
axiom lapse_recurs : ∀ h, Admissible h → ∀ t, ∃ t', t' > t ∧ h t' = false

/-- Assumption 2.5 (retrieval). Some admissible history returns to
anticipation after every time. -/
axiom retrieval : ∃ h, Admissible h ∧ ∀ t, ∃ t', t' ≥ t ∧ h t' = true

/-- Lemma 3.1. No admissible history is a stable achievement. -/
theorem no_stable (h : History) (ha : Admissible h) : ¬ StableAchievement h := by
  intro ⟨t0, hs⟩
  obtain ⟨t', hgt, hf⟩ := lapse_recurs h ha t0
  have := hs t' (Nat.le_of_lt hgt)
  rw [hf] at this
  exact Bool.false_ne_true this

/-- Lemma 3.2. Some admissible history is an orientation. -/
theorem orientation_possible : ∃ h, Admissible h ∧ Orientation h := retrieval

/-- Theorem 3.3 (main result). Authentic being-towards-death is possible as
an orientation but not as a stable achievement. -/
theorem main :
    (∃ h, Admissible h ∧ Orientation h) ∧
    ¬ ∃ h, Admissible h ∧ StableAchievement h :=
  ⟨orientation_possible, fun ⟨h, ha, hs⟩ => no_stable h ha hs⟩

end Philosophy.PHE_07

#print axioms Philosophy.PHE_07.main
