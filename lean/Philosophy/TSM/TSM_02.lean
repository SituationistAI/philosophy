/-
TSM-02 · Against Temporal Passage
Formalization of Lemma 3.1, Theorem 3.2 and Theorem 3.3.

Worlds, passage, the impression of passage and the relation of B-duplication
are primitives. The premises are axioms: passage requires a changing A-series
(Assumption 2.4); the A-series is incoherent, so no world has one
(Assumption 2.5, the conclusion of TSM-01); the impression of passage is
fixed by the B-facts about experience (Assumption 2.6); and passage, if
there were such a thing, would not be fixed by the B-facts (Assumption 2.7).

What this file establishes. No world has passage (Lemma 3.1). Independently
of Assumption 2.5, every world with the impression of passage has a
B-duplicate with the impression and without passage (Theorem 3.2). Wherever
the impression occurs, it occurs without passage and in every B-duplicate
(Theorem 3.3).

What it does not establish. It does not establish any of the four
assumptions, and it does not formalize the psychological explanation of the
impression given in Section 4 of the manuscript.
-/

namespace Philosophy.TSM_02

/-- Worlds. -/
axiom World : Type

/-- Definition 2.1. Passage: events change their A-properties, the present
moving from earlier to later times. -/
axiom Passage : World → Prop

/-- Definition 2.1. The world contains a changing A-series. -/
axiom ChangingASeries : World → Prop

/-- Definition 2.2. The impression of passage is had in the world. -/
axiom Impression : World → Prop

/-- Definition 2.3. `BDup w v`: `v` matches `w` in every B-fact, that is, in
what occurs at each time and in the relations of earlier, later and
simultaneous. -/
axiom BDup : World → World → Prop

/-- Assumption 2.4. Passage requires a changing A-series. -/
axiom passage_requires_A : ∀ w, Passage w → ChangingASeries w

/-- Assumption 2.5 (TSM-01). The A-series is incoherent: no world contains a
changing A-series. -/
axiom A_series_incoherent : ∀ w, ¬ ChangingASeries w

/-- Assumption 2.6. The impression of passage is fixed by the B-facts. -/
axiom impression_B_fixed : ∀ w v, BDup w v → Impression w → Impression v

/-- Assumption 2.7. Passage is not fixed by the B-facts: every world has a
B-duplicate without passage. -/
axiom static_duplicate : ∀ w, ∃ v, BDup w v ∧ ¬ Passage v

/-- Lemma 3.1. No world has passage. -/
theorem no_passage (w : World) : ¬ Passage w :=
  fun hp => A_series_incoherent w (passage_requires_A w hp)

/-- Theorem 3.2 (the impression does not depend on passage). Every world in
which the impression is had has a B-duplicate in which it is had and in
which there is no passage. -/
theorem impression_without_passage (w : World) (hi : Impression w) :
    ∃ v, BDup w v ∧ Impression v ∧ ¬ Passage v :=
  match static_duplicate w with
  | ⟨v, hd, hn⟩ => ⟨v, hd, impression_B_fixed w v hd hi, hn⟩

/-- Theorem 3.3 (main result). Wherever the impression of passage occurs, it
occurs without passage, and it occurs in every B-duplicate of that world. -/
theorem feature_of_experience (w : World) (hi : Impression w) :
    ¬ Passage w ∧ ∀ v, BDup w v → Impression v :=
  ⟨no_passage w, fun v hd => impression_B_fixed w v hd hi⟩

end Philosophy.TSM_02

#print axioms Philosophy.TSM_02.impression_without_passage
#print axioms Philosophy.TSM_02.feature_of_experience
