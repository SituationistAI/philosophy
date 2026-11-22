/-
EPI-01 · The Analysis of Knowledge
Formalization of Definitions 2.2–2.4, Theorem 3.1, Corollary 3.2 and
Theorem 3.3.

What this file establishes. Given the centring of closeness (Assumption 2.1),
safety entails truth, so that knowledge as justified safe belief is factive;
and a justified true belief is safe exactly when it is not a Gettier case in
the sense of Definition 2.4. It does not establish that Definition 2.4
captures the cases in the literature, which is argued in Section 4.
-/

namespace Philosophy.EPI_01

/-- Possible worlds. -/
axiom World : Type
/-- Subjects. -/
axiom Subject : Type
/-- Bases on which beliefs are formed. -/
axiom Basis : Type

/-- Propositions, construed as sets of worlds. -/
abbrev Proposition := World → Prop

/-- `Close w v`: `v` is close to `w`. -/
axiom Close : World → World → Prop

/-- Assumption 2.1 (centring). Every world is close to itself. -/
axiom centring : ∀ w, Close w w

/-- `Believes S p m w`: at `w`, `S` believes `p` on basis `m`. -/
axiom Believes : Subject → Proposition → Basis → World → Prop

/-- `Justified S p m w`: at `w`, `S` is justified in believing `p` on basis `m`. -/
axiom Justified : Subject → Proposition → Basis → World → Prop

/-- Definition 2.2 (safety). -/
def Safe (S : Subject) (p : Proposition) (m : Basis) (w : World) : Prop :=
  ∀ v, Close w v → Believes S p m v → p v

/-- Definition 2.3 (knowledge). -/
def Knows (S : Subject) (p : Proposition) (w : World) : Prop :=
  ∃ m, Believes S p m w ∧ Justified S p m w ∧ Safe S p m w

/-- Definition 2.4 (Gettier case). -/
def GettierCase (S : Subject) (p : Proposition) (m : Basis) (w : World) : Prop :=
  Believes S p m w ∧ Justified S p m w ∧ p w ∧
  ∃ v, Close w v ∧ Believes S p m v ∧ ¬ p v

/-- Theorem 3.1. Safety entails truth. -/
theorem truth_redundant {S : Subject} {p : Proposition} {m : Basis} {w : World}
    (hb : Believes S p m w) (hs : Safe S p m w) : p w :=
  hs w (centring w) hb

/-- Corollary 3.2. Knowledge is factive. -/
theorem factive {S : Subject} {p : Proposition} {w : World}
    (hk : Knows S p w) : p w := by
  obtain ⟨m, hb, _, hs⟩ := hk
  exact truth_redundant hb hs

/-- Theorem 3.3 (characterization). A justified true belief is safe if and
only if it is not a Gettier case. -/
theorem characterization {S : Subject} {p : Proposition} {m : Basis} {w : World}
    (hb : Believes S p m w) (hj : Justified S p m w) (ht : p w) :
    Safe S p m w ↔ ¬ GettierCase S p m w := by
  constructor
  · intro hs ⟨_, _, _, v, hc, hbv, hnp⟩
    exact hnp (hs v hc hbv)
  · intro hng v hc hbv
    exact Classical.byContradiction fun hnp => hng ⟨hb, hj, ht, v, hc, hbv, hnp⟩

/-- Proposition 6.1 (closure). Safety is preserved under competent deduction:
if every belief in `q` on the deductive basis `m'` is accompanied by a belief in
`p` on basis `m`, and `p` entails `q`, then safety of the belief in `p`
yields safety of the belief in `q`. -/
theorem safety_closure {S : Subject} {p q : Proposition} {m m' : Basis} {w : World}
    (entails : ∀ v, p v → q v)
    (deduction : ∀ v, Believes S q m' v → Believes S p m v)
    (hs : Safe S p m w) : Safe S q m' w :=
  fun v hc hb => entails v (hs v hc (deduction v hb))

end Philosophy.EPI_01

#print axioms Philosophy.EPI_01.truth_redundant
#print axioms Philosophy.EPI_01.characterization
#print axioms Philosophy.EPI_01.safety_closure
