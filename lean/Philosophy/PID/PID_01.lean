/-
PID-01 · On Personal Identity
Formalization of the logical skeleton of the criterion (Sections 3–6).

A case structure (Definition 3.2) has person-stages, each at a time, with one
original stage at time 0 and edges between stages at consecutive times. An
edge may carry strong psychological connection (Definitions 3.3–3.4) and may
continue the life of the earlier stage's organism (Definition 3.5). A stage
may or may not be realized in a thing of the original's kind (Principle P2).
`Same y` says that y is a stage of the original person. The criterion of
PID-01 is stated by four axioms: the original stage is a stage of the
original person; uncontested continuity of the right kind preserves identity
(Principle P1); in a contested step identity follows the continuation of the
life (Principle P3); and nothing is a later stage of the original person
except by such a step from an earlier one (Principles P1 and P2, necessity).

What this file establishes. Theorem 4.6: the criterion never makes two
simultaneous stages stages of the original, so it respects the logic of
identity; Corollary 4.7, Theorem 5.3, Proposition 5.6 and Theorem 6.2 in their
abstract form. What it does not establish: that the criterion is true, that
any actual case has the structure assumed, or the facts about particular
cases, which Appendix A computes for every case up to its bound.
-/

namespace Philosophy.PID_01

/-- Definition 3.2. Person-stages of a case structure. -/
axiom Stage : Type

/-- Definition 3.2. The time of a stage. -/
axiom time : Stage → Nat

/-- Definition 3.2. The original stage. -/
axiom origin : Stage

/-- Definition 3.2. The original stage is at time 0. -/
axiom origin_time : time origin = 0

/-- Definition 3.2. Edges of the case structure. -/
axiom Edge : Stage → Stage → Prop

/-- Definition 3.2. Edges join stages at consecutive times. -/
axiom edge_time : ∀ x y, Edge x y → time y = time x + 1

/-- Definitions 3.3 and 3.4. The edge carries strong psychological
connection (degree at least 1). -/
axiom Strong : Stage → Stage → Prop

/-- Principle P2. The stage is realized in a thing of the original's kind. -/
axiom SameKind : Stage → Prop

/-- Principle P2. The original stage is realized in a thing of its own kind. -/
axiom origin_kind : SameKind origin

/-- Definition 3.5. The later stage continues the life of the organism that
realizes the earlier stage. -/
axiom Life : Stage → Stage → Prop

/-- Assumption 3.6. Human lives do not divide: a stage's life is continued by
at most one later stage. -/
axiom life_unique : ∀ x y z, Life x y → Life x z → y = z

/-- Definition 4.1. A candidate: a one-step continuation through a cause of
the right kind. -/
def Cand (x y : Stage) : Prop := Edge x y ∧ Strong x y ∧ SameKind x ∧ SameKind y

/-- Definition 4.2. A step is contested if the earlier stage has another
candidate (fission) or the later stage is a candidate of another stage
(fusion). -/
def Contested (x y : Stage) : Prop :=
  (∃ z, Cand x z ∧ z ≠ y) ∨ (∃ w, w ≠ x ∧ Cand w y)

/-- Definition 4.3. Being a stage of the original person (primitive; its
conditions are the axioms below). -/
axiom Same : Stage → Prop

/-- Definition 4.3, base clause. -/
axiom same_origin : Same origin

/-- Principle P1. Non-branching psychological continuity through a cause of
the right kind preserves identity. -/
axiom principle_P1 : ∀ x y, Same x → Cand x y → ¬ Contested x y → Same y

/-- Principle P3. Tie-breaker: in a contested step, the later stage is the
original exactly if it continues the life of the original's organism. -/
axiom principle_P3 : ∀ x y, Same x → Cand x y → Contested x y →
  (Same y ↔ Life x y)

/-- Principles P1 and P2, necessity: a stage of the original other than the
original stage is a candidate of an earlier stage of the original. -/
axiom necessity : ∀ y, Same y → y = origin ∨ ∃ x, Same x ∧ Cand x y

/-- Lemma 4.5. Every later stage of the original has an earlier stage of the
original as its parent, one time earlier. -/
theorem lemma_4_5 (y : Stage) (hy : Same y) (ht : time y ≠ 0) :
    ∃ x, Same x ∧ Cand x y ∧ time y = time x + 1 := by
  rcases necessity y hy with h | ⟨x, hx, hc⟩
  · subst h; exact absurd origin_time ht
  · exact ⟨x, hx, hc, edge_time x y hc.1⟩

/-- Theorem 4.6. The criterion never makes two simultaneous stages stages of
the original person. -/
theorem uniqueness : ∀ n (y y' : Stage), Same y → Same y' →
    time y = n → time y' = n → y = y' := by
  intro n
  induction n with
  | zero =>
    intro y y' hy hy' h h'
    have e1 : y = origin := by
      rcases necessity y hy with e | ⟨x, _, hc⟩
      · exact e
      · have := edge_time x y hc.1; omega
    have e2 : y' = origin := by
      rcases necessity y' hy' with e | ⟨x, _, hc⟩
      · exact e
      · have := edge_time x y' hc.1; omega
    rw [e1, e2]
  | succ n ih =>
    intro y y' hy hy' h h'
    obtain ⟨x, hx, hc, hxt⟩ := lemma_4_5 y hy (by omega)
    obtain ⟨x', hx', hc', hxt'⟩ := lemma_4_5 y' hy' (by omega)
    have hxx : x = x' := ih x x' hx hx' (by omega) (by omega)
    subst hxx
    apply Classical.byContradiction
    intro hne
    have c1 : Contested x y := Or.inl ⟨y', hc', fun e => hne e.symm⟩
    have c2 : Contested x y' := Or.inl ⟨y, hc, hne⟩
    have l1 : Life x y := (principle_P3 x y hx hc c1).mp hy
    have l2 : Life x y' := (principle_P3 x y' hx hc' c2).mp hy'
    exact hne (life_unique x y y' l1 l2)

/-- Corollary 4.7. Identity with the original is never shared by two
simultaneous stages: if y and y' are both the original at one time, they are
one stage. -/
theorem corollary_4_7 (y y' : Stage) (hy : Same y) (hy' : Same y')
    (h : time y = time y') : y = y' :=
  uniqueness (time y) y y' hy hy' rfl h.symm

/-- Theorem 5.3 (i). In a contested step from the original, a candidate that
continues the life is the original. -/
theorem theorem_5_3_i (x y : Stage) (hx : Same x) (hc : Cand x y)
    (hct : Contested x y) (hl : Life x y) : Same y :=
  (principle_P3 x y hx hc hct).mpr hl

/-- Theorem 5.3 (ii). In fission from the original, a branch that does not
continue the life is not the original; if no branch continues it, neither is. -/
theorem theorem_5_3_ii (x y z : Stage) (hx : Same x) (hy : Cand x y)
    (hz : Cand x z) (hne : z ≠ y) (hl : ¬ Life x y) : ¬ Same y :=
  fun h => hl ((principle_P3 x y hx hy (Or.inl ⟨z, hz, hne⟩)).mp h)

/-- Proposition 5.6. Every stage of the original is realized in a thing of the
original's kind. -/
theorem proposition_5_6 (y : Stage) (hy : Same y) : SameKind y := by
  rcases necessity y hy with h | ⟨_, _, hc⟩
  · subst h; exact origin_kind
  · exact hc.2.2.2

/-- Definition 6.1. Ordinary stages: reached from the original stage by
uncontested candidate steps that continue the life. -/
inductive Ordinary : Stage → Prop
  | root : Ordinary origin
  | step : ∀ x y, Ordinary x → Cand x y → Life x y → ¬ Contested x y → Ordinary y

/-- The biological criterion (PID-05-a, Assumption 2.7): stages of the
original organism are reached from the original stage by life continuation. -/
inductive Bio : Stage → Prop
  | root : Bio origin
  | step : ∀ x y, Bio x → Life x y → Bio y

/-- Theorem 6.2. At an ordinary stage the criterion and the biological
criterion both give identity with the original. -/
theorem theorem_6_2 (y : Stage) (h : Ordinary y) : Same y ∧ Bio y := by
  induction h with
  | root => exact ⟨same_origin, Bio.root⟩
  | step x y _ hc hl hn ih =>
    exact ⟨principle_P1 x y ih.1 hc hn, Bio.step x y ih.2 hl⟩

end Philosophy.PID_01

#print axioms Philosophy.PID_01.uniqueness
#print axioms Philosophy.PID_01.theorem_6_2
