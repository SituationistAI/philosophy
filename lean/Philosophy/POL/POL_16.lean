/-
POL-16 · The Paradox of Tolerance
Formalization of Theorems 3.1 and 3.2, Corollary 3.3 and Proposition 3.4.

What this file establishes. Given that only active intolerance can threaten
the conditions of toleration (Assumption 2.4), that a policy which tolerates a
threatening view fails to preserve those conditions (Assumption 2.5), and that
restricting every threatening view suffices to preserve them (Assumption 2.6):
unlimited tolerance fails to preserve the conditions of toleration whenever
some view threatens them (Popper's paradox, Theorem 3.1); the policies that
preserve the conditions and restrict only what threatens them (Principles P1
and P2) are exactly those that tolerate a view if and only if it does not
threaten the conditions (Theorem 3.2); such a policy tolerates every view
that is not active intolerance (Corollary 3.3); and the policy of restricting
all intolerance violates P2 if some intolerance is harmless (Proposition 3.4).

What it does not establish. It does not establish the three assumptions, nor
does it say which actual views threaten the conditions of toleration; that is
a matter of judgment in particular circumstances.
-/

namespace Philosophy.POL_16

/-- Views, together with the conduct of those who hold them (Definition 2.1). -/
axiom View : Type

/-- Definition 2.1. A view is intolerant if it holds that some other views
ought to be suppressed. -/
axiom Intolerant : View → Prop

/-- Definition 2.1. A view is active if its holders act, or organize to act,
to bring about what it prescribes. -/
axiom Active : View → Prop

/-- Definition 2.3. A view threatens the conditions of toleration. -/
axiom Threatens : View → Prop

/-- Definition 2.2. A policy says which views are tolerated. -/
def Policy : Type := View → Prop

/-- Definition 2.3. A policy preserves the conditions of toleration. -/
axiom Preserves : Policy → Prop

/-- Assumption 2.4. Only active intolerance threatens the conditions of
toleration. -/
axiom assumption_2_4 : ∀ v, Threatens v → Active v ∧ Intolerant v

/-- Assumption 2.5. A policy that tolerates a threatening view does not
preserve the conditions of toleration. -/
axiom assumption_2_5 : ∀ (p : Policy) (v : View), Threatens v → p v → ¬ Preserves p

/-- Assumption 2.6. A policy that tolerates no threatening view preserves the
conditions of toleration. -/
axiom assumption_2_6 : ∀ (p : Policy), (∀ v, Threatens v → ¬ p v) → Preserves p

/-- Principle P2 (Necessity): a policy restricts only threatening views. -/
def Necessity (p : Policy) : Prop := ∀ v, ¬ p v → Threatens v

/-- Unlimited tolerance tolerates every view. -/
def unlimited : Policy := fun _ => True

/-- The resolution: tolerate exactly the views that do not threaten the
conditions of toleration. -/
def resolution : Policy := fun v => ¬ Threatens v

/-- The policy of restricting all intolerance. -/
def restrictIntolerance : Policy := fun v => ¬ Intolerant v

/-- Theorem 3.1 (Popper's paradox). If some view threatens the conditions of
toleration, unlimited tolerance does not preserve them. -/
theorem paradox (h : ∃ v, Threatens v) : ¬ Preserves unlimited := by
  obtain ⟨v, hv⟩ := h
  exact assumption_2_5 unlimited v hv trivial

/-- Theorem 3.2 (resolution). A policy satisfies P1 (it preserves the
conditions of toleration) and P2 if and only if it tolerates exactly the views
that do not threaten those conditions. -/
theorem resolution_unique (p : Policy) :
    (Preserves p ∧ Necessity p) ↔ ∀ v, p v ↔ resolution v := by
  constructor
  · intro ⟨hp, hn⟩ v
    constructor
    · intro hv ht
      exact assumption_2_5 p v ht hv hp
    · intro hr
      exact Classical.byContradiction fun hv => hr (hn v hv)
  · intro h
    constructor
    · exact assumption_2_6 p fun v ht hv => (h v).mp hv ht
    · intro v hv
      exact Classical.byContradiction fun ht => hv ((h v).mpr ht)

/-- Corollary 3.3. A policy satisfying P2 (in particular, one satisfying P1
and P2) tolerates every view that is not active intolerance, and restricts a
view only if it is intolerant and threatens the conditions of toleration. -/
theorem corollary_3_3 (p : Policy) (hn : Necessity p) :
    (∀ v, ¬ (Active v ∧ Intolerant v) → p v) ∧
    (∀ v, ¬ p v → Intolerant v ∧ Threatens v) := by
  constructor
  · intro v hv
    exact Classical.byContradiction fun hnp => hv (assumption_2_4 v (hn v hnp))
  · intro v hnp
    exact ⟨(assumption_2_4 v (hn v hnp)).2, hn v hnp⟩

/-- Proposition 3.4. If some intolerant view does not threaten the conditions
of toleration, the policy of restricting all intolerance violates P2. -/
theorem proposition_3_4 (h : ∃ v, Intolerant v ∧ ¬ Threatens v) :
    ¬ Necessity restrictIntolerance := by
  intro hn
  obtain ⟨v, hi, ht⟩ := h
  exact ht (hn v fun hr => hr hi)

end Philosophy.POL_16

#print axioms Philosophy.POL_16.paradox
#print axioms Philosophy.POL_16.resolution_unique
#print axioms Philosophy.POL_16.corollary_3_3
