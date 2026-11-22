/-
PHE-05 · The Thickness of the Living Present
Formalization of Lemmas 4.1 and 4.2, Theorem 4.3 and Proposition 5.1.

Phases of the experiential flow are indexed by natural numbers, earlier
phases by smaller numbers. `retains t s` says that the phase occurring at `t`
holds the phase `s` in retention (with `s = t` the limiting case of primal
impression). The retentional horizon is a fixed depth `K` (Definition 3.4).

What this file establishes. Given that retention reaches back exactly as far
as the retentional horizon (Principles P2 and P3), that the experience of
succession requires the retention of an earlier phase (Principle P1), and
that the horizon is not null (Assumption 3.6), the living present at any
phase past the start of the flow is the window of phases of retentional depth
at most `K`, which contains phases other than the present one, so it is not
an instant; and every phase is retained by its successor within the same
flow, so the self-manifestation of the flow needs no higher-order flow.
It does not establish the principles, which the manuscript defends, nor
anything about protention, which is not modelled, nor the value of `K`.
-/

namespace Philosophy.PHE_05

/-- Definition 3.4. The retentional horizon: the greatest depth at which a
past phase is still retained as differentiated. -/
axiom K : Nat

/-- Definitions 3.2 and 3.3. `retains t s`: the phase at `t` holds the phase
at `s` in retention (primal impression when `s = t`). -/
axiom retains : Nat → Nat → Prop

/-- Principle P3 (finite horizon). Retention reaches no further back than
the retentional horizon, and never forward. -/
axiom retention_bounded : ∀ t s, retains t s → s ≤ t ∧ t - s ≤ K

/-- Principle P2 (continuity of retentional modification). Every phase within
the horizon is retained. -/
axiom retention_continuous : ∀ t s, s ≤ t → t - s ≤ K → retains t s

/-- Experiencing a succession at phase `t`. -/
axiom ExperiencesSuccession : Nat → Prop

/-- Principle P1. The experience of a succession at `t` requires that an
earlier phase be retained at `t`. -/
axiom succession_requires_retention :
  ∀ t, ExperiencesSuccession t → ∃ s, s < t ∧ retains t s

/-- Assumption 3.6. The retentional horizon is not null. -/
axiom horizon_pos : K > 0

/-- Definition 3.5. The (retentional part of the) living present at `t`. -/
def LivingPresent (t s : Nat) : Prop := retains t s

/-- Lemma 4.1. If the living present were an instant, no succession could
be experienced. -/
theorem instant_excludes_succession (t : Nat)
    (hinst : ∀ s, LivingPresent t s → s = t) : ¬ ExperiencesSuccession t := by
  intro h
  obtain ⟨s, hlt, hr⟩ := succession_requires_retention t h
  have := hinst s hr
  omega

/-- Lemma 4.2. The living present at `t` is exactly the window of phases of
retentional depth at most `K`. -/
theorem window (t s : Nat) :
    LivingPresent t s ↔ (s ≤ t ∧ t - s ≤ K) :=
  ⟨retention_bounded t s, fun h => retention_continuous t s h.1 h.2⟩

/-- Theorem 4.3 (main result). For every phase `t` past the beginning of the
flow, the living present at `t` contains a phase other than `t`, so it is
not an instant, and its extent is fixed by the retentional horizon: it
contains the phase at depth `K` and no phase deeper than `K`. -/
theorem thickness (t : Nat) (ht : t ≥ 1) :
    (∃ s, s ≠ t ∧ LivingPresent t s) ∧
    (t ≥ K → LivingPresent t (t - K)) ∧
    (∀ s, s + K < t → ¬ LivingPresent t s) := by
  have hK := horizon_pos
  refine ⟨⟨t - 1, by omega, (window t (t - 1)).mpr ⟨by omega, by omega⟩⟩, ?_, ?_⟩
  · intro h
    exact (window t (t - K)).mpr ⟨by omega, by omega⟩
  · intro s hs hl
    have := (window t s).mp hl
    omega

/-- Proposition 5.1. Every phase of the flow is retained by its immediate
successor within the same flow: the flow is given to itself by the
longitudinal intentionality of its own retentions. -/
theorem self_manifestation (t : Nat) : LivingPresent (t + 1) t := by
  have hK := horizon_pos
  exact (window (t + 1) t).mpr ⟨by omega, by omega⟩

end Philosophy.PHE_05

#print axioms Philosophy.PHE_05.thickness
#print axioms Philosophy.PHE_05.self_manifestation
