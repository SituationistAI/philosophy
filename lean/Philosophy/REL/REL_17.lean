/-
REL-17 · The Rationality of Faith Under Underdetermination
Formalization of Lemma 3.1, Propositions 3.2 and 3.3, Theorem 3.4 and
Corollary 3.5.

The evidential status of a proposition `p` for an agent is one of three
values (Definition 2.1); doxastic attitudes are belief, disbelief and
suspension (Definition 2.2). An agent's state toward `p` is a doxastic
attitude together with a practical commitment, present or absent.
Evidentialism (Principle P1) permits exactly the attitude that fits the
evidence and says nothing about commitment. Faith (Definition 2.3) is
commitment without disbelief. A state is rational all things considered
(Definition 2.5) if its attitude is epistemically permitted and it contains a
commitment only when the practical stakes warrant one (Principle P2).

What this file establishes. Under underdetermination evidentialism permits a
state of faith (Proposition 3.2); for every evidential status it permits a
state without faith (Proposition 3.3); under underdetermination with stakes
that warrant commitment, faith is rational (Theorem 3.4); evidentialism
excludes faith only where the evidence supports not-p (Corollary 3.5).

What it does not establish. That faith is a commitment rather than a belief,
that evidentialism governs only doxastic attitudes, or when the stakes
warrant commitment (REL-06 gives one criterion). These are the content of
Definition 2.3 and Principles P1 and P2, argued in the manuscript.
-/

namespace Philosophy.REL_17

/-- Definition 2.1. Evidential status of `p`. -/
inductive Status
  | supports      -- the evidence supports p
  | against       -- the evidence supports not-p
  | under         -- the evidence underdetermines p
  deriving DecidableEq

/-- Definition 2.2. Doxastic attitudes toward `p`. -/
inductive Attitude
  | believe
  | disbelieve
  | suspend
  deriving DecidableEq

/-- Definition 2.2. The attitude that fits each evidential status. -/
def fits : Status → Attitude
  | .supports => .believe
  | .against => .disbelieve
  | .under => .suspend

/-- An agent's state toward `p`: an attitude and a commitment. -/
structure State where
  att : Attitude
  commit : Bool

/-- Principle P1 (evidentialism properly understood). A state is
epistemically permitted iff its attitude fits the evidence; commitment is
not assessed. -/
def EpPermitted (s : Status) (st : State) : Prop := st.att = fits s

/-- Definition 2.3. Faith that `p`: commitment to `p` without disbelief. -/
def Faith (st : State) : Prop := st.commit = true ∧ st.att ≠ .disbelieve

/-- Principle P2 and Definition 2.5. A state is rational all things
considered, given evidential status `s` and whether the practical stakes
warrant commitment (`w`), iff its attitude is epistemically permitted and it
commits only if commitment is warranted. -/
def Rational (s : Status) (w : Bool) (st : State) : Prop :=
  EpPermitted s st ∧ (st.commit = true → w = true)

/-- Lemma 3.1. Under underdetermination the fitting attitude is suspension. -/
theorem under_suspend : fits .under = .suspend := rfl

/-- Proposition 3.2 (not forbidden). Under underdetermination, evidentialism
permits a state of faith. -/
theorem not_forbidden : ∃ st, EpPermitted .under st ∧ Faith st :=
  ⟨⟨.suspend, true⟩, rfl, rfl, by decide⟩

/-- Proposition 3.3 (not required). For every evidential status,
evidentialism permits a state without faith. -/
theorem not_required : ∀ s, ∃ st, EpPermitted s st ∧ ¬ Faith st := by
  intro s
  refine ⟨⟨fits s, false⟩, rfl, ?_⟩
  intro h
  cases h.1

/-- Theorem 3.4 (rationality of faith). Under underdetermination, if the
stakes warrant commitment, faith is rational all things considered. -/
theorem faith_rational : ∃ st, Rational .under true st ∧ Faith st :=
  ⟨⟨.suspend, true⟩, ⟨rfl, fun _ => rfl⟩, rfl, by decide⟩

/-- Corollary 3.5. Evidentialism excludes faith only where the evidence
supports not-p. -/
theorem excludes_only_against (s : Status)
    (h : ∀ st, EpPermitted s st → ¬ Faith st) : s = .against := by
  cases s with
  | against => rfl
  | supports =>
    exact absurd ⟨rfl, by decide⟩ (h ⟨.believe, true⟩ rfl)
  | under =>
    exact absurd ⟨rfl, by decide⟩ (h ⟨.suspend, true⟩ rfl)

end Philosophy.REL_17

#print axioms Philosophy.REL_17.not_forbidden
#print axioms Philosophy.REL_17.not_required
#print axioms Philosophy.REL_17.faith_rational
#print axioms Philosophy.REL_17.excludes_only_against
