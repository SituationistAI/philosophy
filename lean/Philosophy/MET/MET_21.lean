/-
MET-21 · Parmenides and the Two Senses of "Is"
Formalization of Lemmas 3.1 and 3.2, Proposition 3.3, Theorem 3.4,
Corollary 3.5 and Proposition 3.6.

Objects and times are primitive types, and existence is a primitive
first-order predicate of objects that holds of everything (Assumption 2.3,
the conclusion of MET-24). A predicative "is F" is a predicate of objects at
times (Definition 2.1). An object changes with respect to F if it is F at one
time and not F at another (Definition 2.2). The collapse principle
(Definition 2.4) is the bridge that takes "x is not F" to "x is not", that
is, to "x does not exist".

What this file establishes. On the predicative reading, the first premise of
Parmenides' argument is true (Lemma 3.1); on the existential reading, the
second premise is true (Lemma 3.2), and the first premise is false if
anything changes (Proposition 3.6). The argument is valid if the collapse
principle holds (Proposition 3.3), but the collapse principle entails that
nothing exists (Theorem 3.4) and is therefore false (Corollary 3.5). A model
in which everything exists and something changes is exhibited (Proposition
3.6). It does not establish that anything actually changes, nor that the
reconstruction of Parmenides' argument is historically correct.
-/

namespace Philosophy.MET_21

/-- Objects. -/
axiom Obj : Type

/-- Times. -/
axiom Time : Type

/-- There is at least one time. -/
axiom t0 : Time

/-- Assumption 2.3 (MET-24). Existence is a first-order property. -/
axiom Exists : Obj → Prop

/-- Assumption 2.3 (MET-24). Existence is had by everything. -/
axiom existence_universal : ∀ x, Exists x

/-- Definition 2.1. Predicative "is F": a predicate of objects at times. -/
abbrev Pred := Obj → Time → Prop

/-- Definition 2.2. `x` changes with respect to `F`. -/
def Changes (F : Pred) (x : Obj) : Prop := ∃ t t', F x t ∧ ¬ F x t'

/-- Definition 2.2. Change occurs. -/
def ChangeOccurs : Prop := ∃ (F : Pred) (x : Obj), Changes F x

/-- Definition 2.4. The collapse principle: whatever is not F, at any time,
is not (does not exist). -/
def Collapse : Prop := ∀ (F : Pred) x t, ¬ F x t → ¬ Exists x

/-- Lemma 3.1. First premise, predicative reading: whatever changes is, at
some time, not F. -/
theorem first_premise_predicative (F : Pred) (x : Obj) (h : Changes F x) :
    ∃ t, ¬ F x t := by
  obtain ⟨_, t', _, h'⟩ := h
  exact ⟨t', h'⟩

/-- Lemma 3.2. Second premise, existential reading: nothing is not (every
object exists). -/
theorem second_premise_existential : ¬ ∃ x, ¬ Exists x :=
  fun ⟨x, hx⟩ => hx (existence_universal x)

/-- Proposition 3.3. With the collapse principle, the argument is valid:
nothing changes. -/
theorem parmenides_valid (hC : Collapse) : ¬ ChangeOccurs := by
  intro ⟨F, x, _, t', _, h'⟩
  exact hC F x t' h' (existence_universal x)

/-- Theorem 3.4. The collapse principle entails that nothing exists: every
object fails to be a round square, so by collapse it is not. -/
theorem collapse_annihilates (hC : Collapse) : ∀ x, ¬ Exists x :=
  fun x => hC (fun _ _ => False) x t0 id

/-- Corollary 3.5. Given Assumption 2.3 and any object, the collapse
principle is false. -/
theorem collapse_false (x : Obj) : ¬ Collapse :=
  fun hC => collapse_annihilates hC x (existence_universal x)

/-- Proposition 3.6 (first part). If change occurs, the first premise on its
existential reading (whatever changes comes from something that does not
exist) is false. -/
theorem first_premise_existential_false (hc : ChangeOccurs) :
    ¬ (∀ (F : Pred) x, Changes F x → ∃ y, ¬ Exists y) := by
  intro h
  obtain ⟨F, x, hx⟩ := hc
  exact second_premise_existential (h F x hx)

/-- Proposition 3.6 (second part). Change is consistent with universal
existence: a model with one object and two times in which everything exists
and the object changes. -/
theorem change_consistent :
    ∃ (O T : Type) (E : O → Prop) (F : O → T → Prop),
      (∀ x, E x) ∧ ∃ x t t', F x t ∧ ¬ F x t' :=
  ⟨Unit, Bool, fun _ => True, fun _ t => t = true,
    fun _ => trivial, (), true, false, rfl, by decide⟩

end Philosophy.MET_21

#print axioms Philosophy.MET_21.parmenides_valid
#print axioms Philosophy.MET_21.collapse_false
#print axioms Philosophy.MET_21.change_consistent
