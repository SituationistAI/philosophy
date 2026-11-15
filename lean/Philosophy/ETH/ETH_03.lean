/-
ETH-03 · The Trolley Problem Solved
Formalization of Theorem 3.1 and Corollary 3.2.

A trolley case is characterized by whether the act redirects an existing
threat and by the numbers saved and killed (Definition 2.1). The doctrine of
the redirected threat (Definition 2.2) permits an act exactly when it
redirects an existing threat and saves more than it kills.

What this file establishes. Every rule satisfying the three adequacy
conditions (Principles P1–P3, stated as hypotheses) agrees with the doctrine
of the redirected threat on every case. It does not establish the adequacy
conditions, and in particular not the invariance condition P3, which is
defended in Section 4 of the manuscript.
-/

namespace Philosophy.ETH_03

/-- Definition 2.1. A trolley case. -/
structure TrolleyCase where
  redirects : Bool
  saved : Nat
  killed : Nat

/-- The Switch case. -/
def switch : TrolleyCase := ⟨true, 5, 1⟩

/-- The Footbridge case. -/
def footbridge : TrolleyCase := ⟨false, 5, 1⟩

/-- Definition 2.2. The doctrine of the redirected threat. -/
def DRT (c : TrolleyCase) : Prop := c.redirects = true ∧ c.saved > c.killed

/-- Theorem 3.1. Any rule satisfying P1 (verdicts), P2 (numbers) and
P3 (invariance) agrees with the doctrine of the redirected threat. -/
theorem uniqueness (rho : TrolleyCase → Prop)
    (verdicts : rho switch ∧ ¬ rho footbridge)
    (numbers : ∀ c, c.killed ≥ c.saved → ¬ rho c)
    (invariance : ∀ c d, c.redirects = d.redirects →
        (c.saved > c.killed ↔ d.saved > d.killed) → (rho c ↔ rho d)) :
    ∀ c, rho c ↔ DRT c := by
  intro c
  by_cases hb : c.saved > c.killed
  · cases hr : c.redirects
    · -- introduces a new threat: same features as Footbridge
      have h := invariance c footbridge (by simp [hr, footbridge])
        (by simp [footbridge]; omega)
      constructor
      · intro hc; exact absurd (h.mp hc) verdicts.2
      · intro ⟨hd, _⟩; simp [hr] at hd
    · -- redirects an existing threat: same features as Switch
      have h := invariance c switch (by simp [hr, switch])
        (by simp [switch]; omega)
      constructor
      · intro _; exact ⟨hr, hb⟩
      · intro _; exact h.mpr verdicts.1
  · constructor
    · intro hc; exact absurd hc (numbers c (by omega))
    · intro ⟨_, h⟩; exact absurd h hb

/-- Proposition 3.3. The doctrine of the redirected threat satisfies P1–P3. -/
theorem drt_adequate :
    (DRT switch ∧ ¬ DRT footbridge) ∧
    (∀ c, c.killed ≥ c.saved → ¬ DRT c) ∧
    (∀ c d, c.redirects = d.redirects →
        (c.saved > c.killed ↔ d.saved > d.killed) → (DRT c ↔ DRT d)) := by
  refine ⟨⟨⟨rfl, by decide⟩, fun ⟨h, _⟩ => by simp [footbridge] at h⟩, ?_, ?_⟩
  · intro c h ⟨_, h'⟩; omega
  · intro c d hr hb
    unfold DRT
    rw [hr, hb]

/-- Corollary 3.2. Any two rules satisfying P1–P3 agree on every case. -/
theorem only_rule (rho sigma : TrolleyCase → Prop)
    (v1 : rho switch ∧ ¬ rho footbridge) (v2 : sigma switch ∧ ¬ sigma footbridge)
    (n1 : ∀ c, c.killed ≥ c.saved → ¬ rho c) (n2 : ∀ c, c.killed ≥ c.saved → ¬ sigma c)
    (i1 : ∀ c d, c.redirects = d.redirects →
        (c.saved > c.killed ↔ d.saved > d.killed) → (rho c ↔ rho d))
    (i2 : ∀ c d, c.redirects = d.redirects →
        (c.saved > c.killed ↔ d.saved > d.killed) → (sigma c ↔ sigma d)) :
    ∀ c, rho c ↔ sigma c := by
  intro c
  rw [uniqueness rho v1 n1 i1 c, uniqueness sigma v2 n2 i2 c]

end Philosophy.ETH_03

#print axioms Philosophy.ETH_03.uniqueness
#print axioms Philosophy.ETH_03.drt_adequate
