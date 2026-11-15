/-
MET-25 · The Simulation Argument Undermined
Formalization of Lemma 3.1, Theorem 3.2, Proposition 3.3, Corollary 3.4,
Proposition 3.6 and Corollary 3.7.

Worlds and epistemic states are primitive. `Sim w` says that in `w` we are
simulated, so that the physics we observe is not base-level physics.
`Supports w` says that in `w` our physical evidence supports the feasibility
premise P, which is a claim about base-level physics (Definition 2.1).
Rational confidence in S, in not-S and in P are primitive predicates of
states, and `ViaArg` marks a state whose attitude to S rests on the simulation
argument (Definition 2.2). Credences are natural numbers read as
percentages.

What this file establishes. In no world is the argument both evidentially
supported and its conclusion true (Lemma 3.1). No rational state is confident
that we are simulated on the basis of the argument (Theorem 3.2). An
argument-based credence s in S satisfies 2s ≤ 100 + c, where c is the
credence in the conjunction of S and P (Proposition 3.3), so that a credence
of 90 requires a credence of at least 80 in that conjunction
(Corollary 3.4). If, as the evidential base assumption implies, our
evidence is silent on P under S (Assumption 3.5), the argument-based credence
is at most 10000 / (200 - q), where q is the prior credence in P
(Proposition 3.6): at most 66 if q is at most 50, at most 50 if q is 0
(Corollary 3.7). It does not establish the assumptions, in particular the
evidential base assumption (Assumption 2.4), and it does not establish that
we are not simulated.
-/

namespace Philosophy.MET_25

/-- Worlds. -/
axiom World : Type

/-- Definition 2.1. In world `w`, we are simulated. -/
axiom Sim : World → Prop

/-- Definition 2.1. In world `w`, our physical evidence supports P. -/
axiom Supports : World → Prop

/-- Assumption 2.4 (evidential base, worldly part). Our evidence supports a
claim about base-level physics only if our physics is base-level physics. -/
axiom support_requires_base : ∀ w, Supports w → ¬ Sim w

/-- Lemma 3.1 (the dilemma). In no world is the argument evidentially
supported and its conclusion true. -/
theorem dilemma (w : World) : ¬ (Supports w ∧ Sim w) :=
  fun ⟨hs, hS⟩ => support_requires_base w hs hS

/-- Epistemic states. -/
axiom State : Type

/-- Rational confidence in S, in not-S and in P. -/
axiom ConfS : State → Prop
axiom ConfNotS : State → Prop
axiom ConfP : State → Prop

/-- Definition 2.2. The state's attitude to S rests on the argument. -/
axiom ViaArg : State → Prop

/-- Assumption 2.3 (dependence). Argument-based confidence in S requires
confidence in P. -/
axiom dependence : ∀ σ, ConfS σ → ViaArg σ → ConfP σ

/-- Assumption 2.4 (evidential base, epistemic part). Rational confidence in
P requires rational confidence that our physics is base-level physics. -/
axiom evidential_base : ∀ σ, ConfP σ → ConfNotS σ

/-- Assumption 2.5 (coherence). No rational state is confident both in S and
in not-S. -/
axiom coherence : ∀ σ, ¬ (ConfS σ ∧ ConfNotS σ)

/-- Theorem 3.2 (main result). No rational state is confident that we are
simulated on the basis of the simulation argument. -/
theorem no_confidence_via_argument (σ : State) (h : ViaArg σ) : ¬ ConfS σ :=
  fun hS => coherence σ ⟨hS, evidential_base σ (dependence σ hS h)⟩

/-- Credence in S, in P and in the conjunction of S and P, in percent. -/
axiom crS : State → Nat
axiom crP : State → Nat
axiom crSP : State → Nat

/-- Assumption 2.6 (probability). Credences are at most 100; the credence
in P is at most the credence in not-S plus the credence in S and P. -/
axiom crS_le : ∀ σ, crS σ ≤ 100
axiom total_probability : ∀ σ, crP σ ≤ (100 - crS σ) + crSP σ

/-- Assumption 2.7 (transmission). An argument-based credence in S is at
most the credence in P. -/
axiom transmission : ∀ σ, ViaArg σ → crS σ ≤ crP σ

/-- Proposition 3.3. An argument-based credence `s` in S satisfies
`2 s ≤ 100 + c`, where `c` is the credence in S and P. -/
theorem credence_cap (σ : State) (h : ViaArg σ) :
    2 * crS σ ≤ 100 + crSP σ := by
  have h1 := transmission σ h
  have h2 := total_probability σ
  have h3 := crS_le σ
  omega

/-- Corollary 3.4. An argument-based credence of at least 90 in S requires a
credence of at least 80 in S and P. -/
theorem near_certainty_requires_prior (σ : State) (h : ViaArg σ)
    (h90 : 90 ≤ crS σ) : 80 ≤ crSP σ := by
  have := credence_cap σ h
  omega

/-- Prior credence, independent of our physical evidence, that base-level
physics permits ancestor-simulation on the required scale. -/
axiom prior : State → Nat

/-- Assumption 3.5 (silence). Under S our physical evidence is silent on P,
so the credence in S and P is at most the prior times the credence in S:
`100 c ≤ q s`. -/
axiom silence : ∀ σ, 100 * crSP σ ≤ prior σ * crS σ

/-- Proposition 3.6. Under silence, an argument-based credence `s` in S
satisfies `(200 - q) s ≤ 10000`, where `q` is the prior. -/
theorem silent_cap (σ : State) (h : ViaArg σ) :
    (200 - prior σ) * crS σ ≤ 10000 := by
  have h1 := credence_cap σ h
  have h2 := silence σ
  rw [Nat.mul_sub_right_distrib]
  generalize prior σ * crS σ = t at *
  omega

/-- Corollary 3.7. If the prior is at most 50, an argument-based credence in
S is at most 66; if the prior is 0, it is at most 50. -/
theorem silent_cap_values (σ : State) (h : ViaArg σ) :
    (prior σ ≤ 50 → crS σ ≤ 66) ∧ (prior σ = 0 → crS σ ≤ 50) := by
  have hc := silent_cap σ h
  constructor
  · intro hq
    have : 150 * crS σ ≤ (200 - prior σ) * crS σ :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · intro hq
    rw [hq] at hc
    omega

end Philosophy.MET_25

#print axioms Philosophy.MET_25.dilemma
#print axioms Philosophy.MET_25.no_confidence_via_argument
#print axioms Philosophy.MET_25.credence_cap
#print axioms Philosophy.MET_25.silent_cap
