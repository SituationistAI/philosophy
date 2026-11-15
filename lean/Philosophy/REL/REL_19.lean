/-
REL-19 · Timeless Omniscience and Indexical Knowledge
Formalization of Theorem 3.3, Proposition 3.6, Corollary 4.2, Theorem 4.3
and Propositions 4.4 and 4.5.

Tenseless propositions are sets of worlds; centered propositions are sets
of centers, triples of a world, a subject and a time (Definition 2.1).
Knowledge of a tenseless proposition (`K`) is not indexed to a time;
knowledge of a centered proposition (`Kc x t p`) is knowledge, had by x at
t, that p holds of x's own situation, de se and de nunc (Definition 2.3).
Knowing a centered proposition requires being located at the time of the
knowing and the truth of the proposition at one's center (Assumption 2.5).

What this file establishes. Given that a temporal God's present would be
an objective now and that there is no objective now (Assumptions 3.1 and
3.2, the latter from TSM-16), God is timeless (Theorem 3.3); the same
conclusion follows from REL-05-a's result that no one knows a free choice
at a time before it (Proposition 3.6). A timeless God knows no centered
proposition, and so does not know what time it is now (Corollary 4.2), but
is omniscient in the sense of Definition 2.6 (Theorem 4.3); everything any
temporal subject knows de nunc corresponds to a tenseless truth God knows
(Proposition 4.4); and no being whatever knows every centered truth
(Proposition 4.5). It does not establish the premises, and it does not
model a timeless being's non-temporal self-knowledge.
-/

namespace Philosophy.REL_19

/-- Definition 2.1. Worlds, subjects and times. -/
axiom World : Type
axiom Being : Type
axiom Time : Type

/-- The actual world. -/
axiom actual : World

/-- Definition 2.1. Tenseless and centered propositions. -/
abbrev Tenseless := World → Prop
abbrev Centered := World → Being → Time → Prop

/-- Definition 2.2. `Located x t`: x exists at time t (in the actual
world). -/
axiom Located : Being → Time → Prop

/-- Definition 2.2. A being is timeless if it is located at no time. -/
def Timeless (x : Being) : Prop := ∀ t, ¬ Located x t

/-- Definition 2.3. `K x p`: x knows the tenseless proposition p. -/
axiom K : Being → Tenseless → Prop

/-- Definition 2.3. `Kc x t p`: x knows at t, de se and de nunc, that p
holds of x's own center. -/
axiom Kc : Being → Time → Centered → Prop

/-- Definition 2.3. `KnowsAt x p t`: x's knowledge of the tenseless
proposition p is held at time t. -/
axiom KnowsAt : Being → Tenseless → Time → Prop

/-- God. -/
axiom god : Being

/-- Assumption 2.4 (factivity). -/
axiom factive : ∀ x p, K x p → p actual

/-- Assumption 2.5 (centered factivity). Knowing a centered proposition at
t requires being located at t and the truth of the proposition at one's
center. -/
axiom centered_factive : ∀ x t p, Kc x t p → Located x t ∧ p actual x t

/-- Definition 2.6. Omniscience properly defined: knowing every true
tenseless proposition, and, at each time at which one is located, every
centered proposition true at one's own center. -/
def Omniscient (x : Being) : Prop :=
  (∀ p : Tenseless, p actual → K x p) ∧
  (∀ t (p : Centered), Located x t → p actual x t → Kc x t p)

/-! ### God is timeless -/

/-- `ObjectiveNow t`: the present at t is a privileged, frame-independent
present. -/
axiom ObjectiveNow : Time → Prop

/-- Assumption 3.1 (omnipresence). If God were located at a time, God's
present, which embraces all of space, would be an objective now. -/
axiom omnipresent_now : ∀ t, Located god t → ObjectiveNow t

/-- Assumption 3.2 (TSM-16). There is no objective now. -/
axiom no_objective_now : ∀ t, ¬ ObjectiveNow t

/-- Theorem 3.3. God is timeless. -/
theorem god_timeless : Timeless god :=
  fun t h => no_objective_now t (omnipresent_now t h)

/-- Assumption 3.4 (a temporal God). If God is located at some time, God
is located at every time and knows at each time every true tenseless
proposition. -/
axiom everlasting : ∀ t, Located god t →
  ∀ s, Located god s ∧ ∀ p : Tenseless, p actual → KnowsAt god p s

/-- `Before s t`: s is earlier than t. -/
axiom Before : Time → Time → Prop

/-- Assumption 3.5 (REL-05-a). There is a true tenseless proposition c
about a free choice made at tc, there is a time t0 before tc, and no one
knows c at a time before tc. -/
axiom free_choice : ∃ (c : Tenseless) (tc t0 : Time), c actual ∧ Before t0 tc ∧
  ∀ x s, Before s tc → ¬ KnowsAt x c s

/-- Proposition 3.6. The second route: God is timeless. -/
theorem god_timeless' : Timeless god := by
  intro t ht
  have ⟨c, tc, t0, hc, hb, hno⟩ := free_choice
  exact hno god t0 hb ((everlasting t ht t0).2 c hc)

/-! ### Timeless omniscience -/

/-- Assumption 4.1 (tenseless omniscience). God knows every true tenseless
proposition. -/
axiom knows_tenseless : ∀ p : Tenseless, p actual → K god p

/-- Corollary 4.2. God knows no centered proposition; in particular, at no
time t does God know that it is now t'. -/
theorem no_indexical : (∀ t p, ¬ Kc god t p) ∧
    ¬ ∃ t t', Kc god t (fun _ _ s => s = t') := by
  have h : ∀ t p, ¬ Kc god t p := fun t p hk =>
    god_timeless t (centered_factive god t p hk).1
  exact ⟨h, fun ⟨t, t', hk⟩ => h t _ hk⟩

/-- Theorem 4.3. God is omniscient in the sense of Definition 2.6. -/
theorem god_omniscient : Omniscient god :=
  ⟨knows_tenseless, fun t _ hl _ => absurd hl (god_timeless t)⟩

/-- Proposition 4.4. Whatever a temporal subject knows de nunc, God knows
the corresponding tenseless truth: that p holds of that subject at that
time. -/
theorem no_information_gap (y : Being) (t : Time) (p : Centered)
    (h : Kc y t p) : K god (fun w => p w y t) :=
  knows_tenseless _ (centered_factive y t p h).2

/-- Proposition 4.5. No being knows every centered truth: if some other
being is located at some time, there is a centered proposition true at
that being's center that x knows at no time. -/
theorem strong_omniscience_impossible (x y : Being) (hxy : x ≠ y)
    (t : Time) (_hy : Located y t) :
    ∃ p : Centered, p actual y t ∧ ∀ s, ¬ Kc x s p := by
  refine ⟨fun _ z _ => z = y, rfl, fun s hk => hxy ?_⟩
  exact (centered_factive x s _ hk).2

end Philosophy.REL_19

#print axioms Philosophy.REL_19.god_timeless
#print axioms Philosophy.REL_19.no_indexical
#print axioms Philosophy.REL_19.god_omniscient
#print axioms Philosophy.REL_19.strong_omniscience_impossible
