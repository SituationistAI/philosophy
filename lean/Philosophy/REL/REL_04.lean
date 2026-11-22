/-
REL-04 · The Paradox of the Stone and Stratified Ability
Formalization of Theorem 3.4, Theorem 3.5, Proposition 3.6 and
Proposition 3.7.

Framework. Abilities are relativized to worlds. A task has a description,
and a description may or may not quantify over the powers of a given agent
(Definition 2.2). Unrestricted omnipotence is the ability to perform every
possible task; stratified omnipotence is the ability to perform every
possible task whose description does not quantify over the agent's own
powers (Definition 2.3).

What this file establishes. (i) The paradox of the stone is valid against
unrestricted omnipotence: no being has it at every world (Theorem 3.4).
(ii) A being that has stratified omnipotence at every world cannot make a
stone it cannot lift, and this inability is no counterexample to its
omnipotence (Theorem 3.5). (iii) Every task such a being cannot perform is
either impossible or quantifies over its own powers (Proposition 3.6).
(iv) Essential stratified omnipotence is consistent with the assumptions
that generate the paradox: they have a model (Proposition 3.7).

What it does not establish. It does not establish that anything is
omnipotent, nor that the classification of descriptions in Assumption 3.3
is correct; the latter is defended in Section 2 of the manuscript.
-/

namespace Philosophy.REL_04

/-- Possible worlds. -/
axiom World : Type

/-- The actual world. -/
axiom actual : World

/-- Agents. -/
axiom Being : Type

/-- Tasks, individuated by their descriptions. -/
axiom Task : Type

/-- Stones. -/
axiom Stone : Type

/-- `CanDo x t w`: at `w`, `x` has the ability to perform `t`
(Definition 2.1). -/
axiom CanDo : Being → Task → World → Prop

/-- `Possible t`: the description of `t` is consistently satisfiable by
some agent (Definition 2.1). -/
axiom Possible : Task → Prop

/-- `SelfRef x t`: the description of `t` quantifies over the powers of `x`
(Definition 2.2). -/
axiom SelfRef : Being → Task → Prop

/-- The task of lifting the stone `s`. -/
axiom lift : Stone → Task

/-- The task, for `x`, of making a stone that `x` cannot lift. -/
axiom stone : Being → Task

/-- Definition 2.3 (i). Unrestricted omnipotence. -/
def UOmni (x : Being) (w : World) : Prop :=
  ∀ t, Possible t → CanDo x t w

/-- Definition 2.3 (ii). Stratified omnipotence. -/
def Omni (x : Being) (w : World) : Prop :=
  ∀ t, Possible t → ¬ SelfRef x t → CanDo x t w

/-- Assumption 3.1. Both tasks are possible: some agent could make a stone
it cannot lift, and any stone could be lifted by some agent. -/
axiom stone_possible : ∀ x, Possible (stone x)
axiom lift_possible : ∀ s, Possible (lift s)

/-- Assumption 3.2 (what the stone task requires). If `x` is able at `w` to
make a stone it cannot lift, then at some world there is a stone that `x`
is unable to lift. -/
axiom stone_outcome :
  ∀ x w, CanDo x (stone x) w → ∃ w' s, ¬ CanDo x (lift s) w'

/-- Assumption 3.3 (classification). The stone task quantifies over the
powers of the agent for whom it is set; lifting a given stone does not. -/
axiom stone_selfref : ∀ x, SelfRef x (stone x)
axiom lift_not_selfref : ∀ x s, ¬ SelfRef x (lift s)

/-- Theorem 3.4 (the paradox is valid). No being is unrestrictedly
omnipotent at every world. -/
theorem paradox : ¬ ∃ x, ∀ w, UOmni x w := by
  intro ⟨x, hx⟩
  obtain ⟨w', s, hs⟩ := stone_outcome x actual (hx actual (stone x) (stone_possible x))
  exact hs (hx w' (lift s) (lift_possible s))

/-- Theorem 3.5. A being that is omnipotent in the stratified sense at every
world is unable, at every world, to make a stone it cannot lift; yet it
remains omnipotent in that sense, since the task quantifies over its own
powers. -/
theorem stone_no_limitation (x : Being) (hx : ∀ w, Omni x w) (w : World) :
    ¬ CanDo x (stone x) w ∧ Omni x w ∧ SelfRef x (stone x) := by
  refine ⟨fun h => ?_, hx w, stone_selfref x⟩
  obtain ⟨w', s, hs⟩ := stone_outcome x w h
  exact hs (hx w' (lift s) (lift_possible s) (lift_not_selfref x s))

/-- Proposition 3.6 (no genuine limitation). Every task that a stratified
omnipotent being cannot perform is impossible or quantifies over its own
powers. -/
theorem no_genuine_limitation (x : Being) (w : World) (hx : Omni x w)
    (t : Task) (ht : ¬ CanDo x t w) : ¬ Possible t ∨ SelfRef x t := by
  apply Classical.byContradiction
  intro h
  apply ht
  apply hx t
  · exact Classical.byContradiction fun hp => h (Or.inl hp)
  · exact fun hs => h (Or.inr hs)

/-! ## Consistency

Proposition 3.7. The assumptions that generate the paradox are jointly
satisfiable together with essential stratified omnipotence. The model has
one world, one being, one stone and two tasks; the being can lift the stone
and cannot make a stone it cannot lift. -/

namespace Model

inductive T where
  | stoneTask
  | liftTask

def canDo (_ : Unit) (t : T) (_ : Unit) : Prop := t = T.liftTask
def possible (_ : T) : Prop := True
def selfRef (_ : Unit) (t : T) : Prop := t = T.stoneTask

/-- Proposition 3.7. In the model, Assumptions 3.1 to 3.3 hold, and the
being is omnipotent in the stratified sense at every world. -/
theorem consistent :
    (possible T.stoneTask ∧ possible T.liftTask) ∧
    (∀ w : Unit, canDo () T.stoneTask w → ∃ w' : Unit, ¬ canDo () T.liftTask w') ∧
    selfRef () T.stoneTask ∧ ¬ selfRef () T.liftTask ∧
    (∀ w : Unit, ∀ t, possible t → ¬ selfRef () t → canDo () t w) := by
  refine ⟨⟨trivial, trivial⟩, ?_, rfl, ?_, ?_⟩
  · intro _ h; cases h
  · intro h; cases h
  · intro _ t _ hs
    cases t
    · exact absurd rfl hs
    · rfl

end Model

end Philosophy.REL_04

#print axioms Philosophy.REL_04.paradox
#print axioms Philosophy.REL_04.stone_no_limitation
#print axioms Philosophy.REL_04.Model.consistent
