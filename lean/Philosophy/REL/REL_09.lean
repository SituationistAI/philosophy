/-
REL-09 · Escaping Euthyphro via Joint Grounding
Formalization of Lemma 3.1, Theorem 3.2, Proposition 3.3 and
Corollary 3.4.

Framework. Facts stand in a relation of (partial) grounding, assumed to be
a strict partial order (Assumption 2.4). For each act-type `a` there are
five facts: that `a` is good, that God commands `a`, that God endorses `a`,
that the natures of creatures endorse `a` (call this creaturely
endorsement), and that `a` is co-endorsed (Definition 2.1). The two horns
of the Euthyphro dilemma are grounding claims (Definitions 2.2 and 2.3).

What this file establishes. Given the assumptions of Section 2, neither
horn holds (Theorem 3.2); goodness is grounded both in a divine and in a
non-divine fact, and obtains only if God endorses and only if creaturely
natures endorse (Proposition 3.3); and divine commands guarantee goodness
without grounding it (Corollary 3.4). It does not establish that
co-endorsement is the full and immediate ground of goodness and of command
(Assumptions 2.6 and 2.7); the manuscript defends this in Sections 2 and 4.
-/

namespace Philosophy.REL_09

/-- Facts. -/
axiom Fact : Type

/-- `Ground f g`: `f` is a (partial) ground of `g`. -/
axiom Ground : Fact → Fact → Prop

/-- `Obtains f`: the fact `f` obtains. -/
axiom Obtains : Fact → Prop

/-- `Divine f`: `f` is a fact about God. -/
axiom Divine : Fact → Prop

/-- Act-types. -/
axiom Act : Type

/-- The five facts associated with an act-type. -/
axiom good : Act → Fact
axiom cmd : Act → Fact
axiom divEnd : Act → Fact
axiom natEnd : Act → Fact
axiom coend : Act → Fact

/-- Definition 2.2. The first horn (voluntarism): God's command grounds
goodness. -/
def FirstHorn (a : Act) : Prop := Ground (cmd a) (good a)

/-- Definition 2.3. The second horn (independence): goodness grounds God's
command. -/
def SecondHorn (a : Act) : Prop := Ground (good a) (cmd a)

/-- Assumption 2.4. Grounding is irreflexive and transitive. -/
axiom ground_irrefl : ∀ f, ¬ Ground f f
axiom ground_trans : ∀ f g h, Ground f g → Ground g h → Ground f h

/-- Assumption 2.5 (Definition 2.1 made explicit). Co-endorsement is
grounded in divine and in creaturely endorsement, and obtains just in case
both do. -/
axiom coend_grounds : ∀ a, Ground (divEnd a) (coend a) ∧ Ground (natEnd a) (coend a)
axiom coend_obtains : ∀ a, Obtains (coend a) ↔ Obtains (divEnd a) ∧ Obtains (natEnd a)

/-- Assumption 2.6 (joint grounding). Co-endorsement grounds both goodness
and command. -/
axiom joint : ∀ a, Ground (coend a) (good a) ∧ Ground (coend a) (cmd a)

/-- Assumption 2.7 (exhaustion). Every ground of goodness, and every ground
of command, is co-endorsement or a ground of co-endorsement. -/
axiom exhaust_good : ∀ a f, Ground f (good a) → f = coend a ∨ Ground f (coend a)
axiom exhaust_cmd : ∀ a f, Ground f (cmd a) → f = coend a ∨ Ground f (coend a)

/-- Assumption 2.8. Divine endorsement is a divine fact; creaturely
endorsement is not. -/
axiom divEnd_divine : ∀ a, Divine (divEnd a)
axiom natEnd_not_divine : ∀ a, ¬ Divine (natEnd a)

/-- Assumption 2.9. Goodness and command obtain only if co-endorsement does;
when co-endorsement obtains, so do goodness and command. -/
axiom good_iff : ∀ a, Obtains (good a) ↔ Obtains (coend a)
axiom cmd_only : ∀ a, Obtains (cmd a) → Obtains (coend a)

/-- Lemma 3.1. Grounding is asymmetric. -/
theorem ground_asymm (f g : Fact) (h : Ground f g) : ¬ Ground g f :=
  fun h' => ground_irrefl f (ground_trans f g f h h')

/-- Auxiliary to Theorem 3.2. A fact grounded in `coend a` is neither
`coend a` nor a ground of it. -/
theorem no_back (a : Act) (f : Fact) (hf : Ground (coend a) f) :
    ¬ (f = coend a ∨ Ground f (coend a)) := by
  intro h
  cases h with
  | inl e => rw [e] at hf; exact ground_irrefl _ hf
  | inr g => exact ground_asymm _ _ hf g

/-- Theorem 3.2 (main result). Neither horn of the dilemma holds. -/
theorem neither_horn (a : Act) : ¬ FirstHorn a ∧ ¬ SecondHorn a :=
  ⟨fun h => no_back a (cmd a) (joint a).2 (exhaust_good a (cmd a) h),
   fun h => no_back a (good a) (joint a).1 (exhaust_cmd a (good a) h)⟩

/-- Proposition 3.3 (joint grounding in divine and non-divine facts).
Goodness is grounded in a divine fact and in a non-divine fact, and it
obtains only if both obtain. -/
theorem joint_grounding (a : Act) :
    (∃ f, Divine f ∧ Ground f (good a)) ∧ (∃ f, ¬ Divine f ∧ Ground f (good a)) ∧
    (Obtains (good a) → Obtains (divEnd a) ∧ Obtains (natEnd a)) :=
  ⟨⟨divEnd a, divEnd_divine a, ground_trans _ _ _ (coend_grounds a).1 (joint a).1⟩,
   ⟨natEnd a, natEnd_not_divine a, ground_trans _ _ _ (coend_grounds a).2 (joint a).1⟩,
   fun h => (coend_obtains a).1 ((good_iff a).1 h)⟩

/-- Corollary 3.4 (commands confirm). If God commands `a`, then `a` is good;
yet the command is not a ground of the goodness. -/
theorem commands_confirm (a : Act) :
    (Obtains (cmd a) → Obtains (good a)) ∧ ¬ Ground (cmd a) (good a) :=
  ⟨fun h => (good_iff a).2 (cmd_only a h), (neither_horn a).1⟩

end Philosophy.REL_09

#print axioms Philosophy.REL_09.neither_horn
#print axioms Philosophy.REL_09.joint_grounding
#print axioms Philosophy.REL_09.commands_confirm
