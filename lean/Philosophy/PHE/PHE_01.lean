/-
PHE-01 · The Duration of the Epoché
Formalization of Lemma 4.1, Theorems 4.2 and 4.3, Corollary 4.4 and
Theorem 4.5.

What this file establishes. Model a course of conscious life in discrete
time, with an attitude (natural or reflective) at each moment and a record of
the moments at which an act of bracketing is performed. Given that the
reflective attitude obtains at the next moment exactly when an act of
bracketing is performed now (Assumption 3.5, default dynamics), that every
window of `span + 1` moments contains a moment without such an act
(Assumption 3.6, lapse), and that for any interval of at most `span` moments
some possible course of life brackets throughout it (Assumption 3.7,
capacity), the reflective attitude can be sustained over every interval of
length at most `span`, no course of life is reflective from some moment on,
and the natural attitude returns within `span + 1` moments of any moment.

What it does not establish. It does not establish the three assumptions,
which the manuscript defends phenomenologically, nor the value of `span`;
discrete time is a simplification of the continuum of the living present.
-/

namespace Philosophy.PHE_01

/-- Definition 3.1 and Definition 3.3: the two attitudes. -/
inductive Attitude where
  | natural
  | reflective
  deriving DecidableEq

/-- Possible courses of conscious life. -/
axiom Life : Type

/-- The attitude of a course of life at a moment. -/
axiom attitude : Life → Nat → Attitude

/-- Definition 3.2. `Brackets l t`: an act of bracketing is performed in
`l` at moment `t`. -/
axiom Brackets : Life → Nat → Prop

/-- The longest stretch over which acts of bracketing can be renewed without
lapse. -/
axiom span : Nat

/-- Assumption 3.5 (default dynamics). The reflective attitude obtains at
the next moment exactly when an act of bracketing is performed now. -/
axiom default_dynamics :
  ∀ l t, attitude l (t + 1) = Attitude.reflective ↔ Brackets l t

/-- Assumption 3.6 (lapse). Every window of `span + 1` moments contains a
moment at which no act of bracketing is performed. -/
axiom lapse :
  ∀ l t, ∃ u, t ≤ u ∧ u ≤ t + span ∧ ¬ Brackets l u

/-- Assumption 3.7 (capacity). For any interval of at most `span` moments,
some possible course of life brackets at every moment of it. -/
axiom capacity :
  ∀ t k, k ≤ span → ∃ l, ∀ u, t ≤ u → u < t + k → Brackets l u

/-- Definition 3.4. A course of life is permanently reflective from `t0`. -/
def PermanentFrom (l : Life) (t0 : Nat) : Prop :=
  ∀ t, t0 ≤ t → attitude l t = Attitude.reflective

/-- Lemma 4.1. The reflective attitude at a moment requires an act of
bracketing at the moment before. -/
theorem reflection_requires_act (l : Life) (t : Nat)
    (h : attitude l (t + 1) = Attitude.reflective) : Brackets l t :=
  (default_dynamics l t).mp h

/-- Theorem 4.2 (sustainability). The reflective attitude can be sustained
throughout any interval of at most `span` moments. -/
theorem sustainable (t k : Nat) (hk : k ≤ span) :
    ∃ l, ∀ u, t < u → u ≤ t + k → attitude l u = Attitude.reflective := by
  obtain ⟨l, hl⟩ := capacity t k hk
  refine ⟨l, fun u h1 h2 => ?_⟩
  cases u with
  | zero => omega
  | succ v => exact (default_dynamics l v).mpr (hl v (by omega) (by omega))

/-- Theorem 4.3 (no permanent epoché). No course of life is permanently
reflective from any moment on. -/
theorem no_permanent (l : Life) (t0 : Nat) : ¬ PermanentFrom l t0 := by
  intro hp
  obtain ⟨u, h1, _, h3⟩ := lapse l t0
  exact h3 ((default_dynamics l u).mp (hp (u + 1) (by omega)))

/-- Corollary 4.4 (return by default). The natural attitude returns within
`span + 1` moments of any moment. -/
theorem returns (l : Life) (t : Nat) :
    ∃ u, t < u ∧ u ≤ t + span + 1 ∧ attitude l u = Attitude.natural := by
  obtain ⟨u, h1, h2, h3⟩ := lapse l t
  refine ⟨u + 1, by omega, by omega, ?_⟩
  cases ha : attitude l (u + 1) with
  | natural => rfl
  | reflective => exact absurd ((default_dynamics l u).mp ha) h3

/-- Theorem 4.5 (main result). The epoché is partial and temporary: it can be
sustained over every interval of at most `span` moments, it is permanent in
no course of life, and the natural attitude returns by default. -/
theorem partial_and_temporary :
    (∀ t k, k ≤ span →
      ∃ l, ∀ u, t < u → u ≤ t + k → attitude l u = Attitude.reflective) ∧
    (∀ l t0, ¬ PermanentFrom l t0) ∧
    (∀ l t, ∃ u, t < u ∧ u ≤ t + span + 1 ∧ attitude l u = Attitude.natural) :=
  ⟨sustainable, no_permanent, returns⟩

end Philosophy.PHE_01

#print axioms Philosophy.PHE_01.partial_and_temporary
