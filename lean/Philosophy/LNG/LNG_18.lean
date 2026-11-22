/-
LNG-18 · Self-Reference Without Paradox
Formalization of Propositions 3.1 to 3.4 and Theorem 3.5.

A self-referential sentence is represented by its content: the function
that gives its truth value from the value that the language's truth
predicate assigns to the sentence itself (Definition 2.1). A sentence whose
content does not depend on that value says something non-semantic about
itself. A classical assignment is acceptable for the sentence if, by the
transparency of truth, the sentence has the value its content gives it
(Definition 2.2); the sentence is paradoxical if no assignment is acceptable.

What this file establishes. A self-referential sentence that applies no
semantic predicate to itself always has an acceptable classical value
(Proposition 3.1). The truth-teller has two (Proposition 3.2). With the
truth predicate and classical values, the liar has none (Proposition 3.3).
With three values and the strong Kleene negation, the liar has one
(Proposition 3.4). Among all contents a classical sentence can have about its
own truth value, exactly one is paradoxical: the negation of its own truth
(Theorem 3.5). Paradox therefore requires self-reference, a semantic
predicate and classical logic together.

What it does not establish. It covers single sentences that refer to
themselves directly; sets of sentences that refer to each other and infinite
sequences such as Yablo's are discussed in the manuscript but not formalized.
-/

namespace Philosophy.LNG_18

/-- Definition 2.1. The content of a self-referential sentence: its truth
value as a function of the value the truth predicate assigns to it. -/
abbrev Content := Bool → Bool

/-- Definition 2.2. An acceptable value satisfies transparency: the value
attributed to the sentence is the value of what it says. -/
def Acceptable (c : Content) (v : Bool) : Prop := c v = v

/-- Definition 2.2. A sentence is paradoxical if no value is acceptable. -/
def Paradoxical (c : Content) : Prop := ∀ v, ¬ Acceptable c v

/-- Proposition 3.1. A self-referential sentence whose content does not
depend on its own truth value (it ascribes a non-semantic property to
itself) has an acceptable classical value. -/
theorem nonsemantic_harmless (b : Bool) : ∃ v, Acceptable (fun _ => b) v :=
  ⟨b, rfl⟩

/-- Proposition 3.2. The truth-teller, which says of itself that it is true,
has two acceptable values. -/
theorem truth_teller : Acceptable (fun v => v) true ∧ Acceptable (fun v => v) false :=
  ⟨rfl, rfl⟩

/-- Proposition 3.3. With classical values, the liar is paradoxical. -/
theorem liar_classical : Paradoxical (fun v => !v) := by
  intro v h
  cases v <;> simp [Acceptable] at h

/-- Strong Kleene values: false, neither, true, as 0, 1, 2. -/
def kneg (x : Nat) : Nat := 2 - x

/-- Proposition 3.4. With three values and strong Kleene negation, the liar
has an acceptable value, the middle one. -/
theorem liar_kleene : kneg 1 = 1 ∧ ∀ x, x ≤ 2 → kneg x = x → x = 1 := by
  refine ⟨rfl, fun x hx h => ?_⟩
  unfold kneg at h
  omega

/-- Theorem 3.5. A classical self-referential sentence is paradoxical if and
only if its content is the negation of its own truth. -/
theorem paradox_iff_liar (c : Content) : Paradoxical c ↔ c = (fun v => !v) := by
  constructor
  · intro h
    funext v
    have hv := h v
    cases v <;> cases hc : c true <;> cases hc' : c false <;>
      simp_all [Acceptable]
  · intro h
    rw [h]
    exact liar_classical

end Philosophy.LNG_18

#print axioms Philosophy.LNG_18.paradox_iff_liar
#print axioms Philosophy.LNG_18.nonsemantic_harmless
