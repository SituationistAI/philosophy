/-
MND-02 · Physicalism and Hempel's Dilemma
Formalization of Proposition 3.5 and Theorem 3.6 of MND-02-a.

What this file establishes. With "physical" defined by reference to current
physics and its foreseeable extensions (Definitions 2.2-2.4), (i) an
ungrounded mental property is not physical, so the thesis is not trivial
(Proposition 3.5, the second horn of Hempel's dilemma); (ii) given the four
assumptions of Section 3 about the actual fundamental theory, physicalism is
true (Theorem 3.6).

What it does not establish. It does not establish any of Assumptions 3.1-3.4,
which are empirical or metaphysical premises defended in the manuscript, and
it does not analyse grounding, nomic role or mentality, which are primitives.
-/

namespace Philosophy.MND_02

/-- Properties. -/
axiom Property : Type

/-- Candidate fundamental theories. -/
axiom Theory : Type

/-- `FundamentalIn T p`: `p` is among the fundamental properties posited by `T`. -/
axiom FundamentalIn : Theory → Property → Prop

/-- `Instantiated p`: `p` is instantiated in the actual world. -/
axiom Instantiated : Property → Prop

/-- `GroundedIn p S`: `p` is wholly grounded in properties satisfying `S`. -/
axiom GroundedIn : Property → (Property → Prop) → Prop

/-- Definition 2.2(a): `T` recovers current physics in its domain of success. -/
axiom Recovers : Theory → Prop

/-- Definition 2.2(b): `p` plays a role in the dynamical laws of `T`, or is
the categorical realizer of such a role. -/
axiom NomicRole : Theory → Property → Prop

/-- Mentality (Definition 2.2(c)). -/
axiom Mental : Property → Prop

/-- Definition 2.2. A foreseeable extension of current physics. -/
def Foreseeable (T : Theory) : Prop :=
  Recovers T ∧ (∀ p, FundamentalIn T p → NomicRole T p) ∧
    (∀ p, FundamentalIn T p → ¬ Mental p)

/-- Definition 2.3. A physical property. -/
def Physical (p : Property) : Prop :=
  ∃ T, Foreseeable T ∧ (FundamentalIn T p ∨ GroundedIn p (FundamentalIn T))

/-- Definition 2.4. Physicalism. -/
def Physicalism : Prop := ∀ p, Instantiated p → Physical p

/-- The actual fundamental theory: the theory whose fundamental properties are
the actually instantiated fundamental properties (Section 3). -/
axiom actualTheory : Theory

/-- Assumption 3.1 (Correspondence). -/
axiom assumption_3_1 : Recovers actualTheory

/-- Assumption 3.2 (Nomic integration). -/
axiom assumption_3_2 : ∀ p, FundamentalIn actualTheory p → NomicRole actualTheory p

/-- Assumption 3.3 (No fundamental mentality). -/
axiom assumption_3_3 : ∀ p, FundamentalIn actualTheory p → ¬ Mental p

/-- Assumption 3.4 (Completeness of grounding). -/
axiom assumption_3_4 : ∀ p, Instantiated p →
  FundamentalIn actualTheory p ∨ GroundedIn p (FundamentalIn actualTheory)

/-- Proposition 3.5 (Non-triviality). A mental property that is grounded in
nothing is not physical. -/
theorem non_triviality (p : Property) (hm : Mental p)
    (hu : ∀ S, ¬ GroundedIn p S) : ¬ Physical p := by
  intro ⟨T, ⟨_, _, hnm⟩, h⟩
  cases h with
  | inl hf => exact hnm p hf hm
  | inr hg => exact hu _ hg

/-- Theorem 3.6 (main result). Physicalism is true. -/
theorem physicalism : Physicalism := by
  intro p hp
  exact ⟨actualTheory, ⟨assumption_3_1, assumption_3_2, assumption_3_3⟩,
    assumption_3_4 p hp⟩

end Philosophy.MND_02

#print axioms Philosophy.MND_02.physicalism
#print axioms Philosophy.MND_02.non_triviality
