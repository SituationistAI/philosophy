/-
ETH-01 · On the Good
Formalization of Volume I, Chapter 5: Theorem 5.2 and Corollaries 5.3–5.4.

An outcome is described by a profile assigning a level to each of the seven
components of the good (Chapter 5): well-being, knowledge, achievement,
relationships, fairness, beauty and autonomy. The value of an outcome is
what idealized reflective endorsement assigns to it (Definition 3.2); it is
a primitive here.

What this file establishes. Given the isolation results of Chapter 4
(Assumption 5.1: for each component there are two outcomes that differ only
in that component and differ in value), the value of an outcome does not
supervene on any proper subset of the seven components. In particular it is
not a function of any single component, so every monism, hedonism included,
is false. It does not establish the isolation results themselves, which rest
on the cases of Chapter 4, nor that the list is complete, which is the
subject of Volume VI.
-/

namespace Philosophy.ETH_01

/-- The seven components: 0 well-being, 1 knowledge, 2 achievement,
3 relationships, 4 fairness, 5 beauty, 6 autonomy. -/
abbrev Component := Fin 7

/-- An outcome profile (Chapter 5): a level for each component. -/
abbrev Profile := Component → Nat

/-- Definition 3.2. Value, as fixed by idealized reflective endorsement. -/
axiom value : Profile → Int

/-- Two profiles agree on every component except possibly `i`. -/
def AgreeExcept (i : Component) (x y : Profile) : Prop := ∀ j, j ≠ i → x j = y j

/-- Assumption 5.1 (isolation). For each component there are two outcomes
that differ only in that component and differ in value. -/
axiom isolation : ∀ i : Component, ∃ x y, AgreeExcept i x y ∧ value x ≠ value y

/-- Value supervenes on the components in `S`. -/
def Supervenes (S : Component → Bool) : Prop :=
  ∀ x y : Profile, (∀ j, S j = true → x j = y j) → value x = value y

/-- Theorem 5.2 (plurality). Value does not supervene on any set of
components that omits at least one of the seven. -/
theorem plurality (S : Component → Bool) (i : Component) (hi : S i = false) :
    ¬ Supervenes S := by
  intro h
  obtain ⟨x, y, hxy, hne⟩ := isolation i
  apply hne
  apply h
  intro j hj
  apply hxy
  intro e
  rw [e, hi] at hj
  exact Bool.noConfusion hj

/-- Corollary 5.3 (against monism). Value is not a function of any single
component. -/
theorem no_monism (i : Component) : ¬ ∃ f : Nat → Int, ∀ x, value x = f (x i) := by
  intro ⟨f, hf⟩
  have := plurality (fun j => decide (j = i))
  have j0 : ∃ j : Component, j ≠ i := by
    by_cases h : i = 0
    · exact ⟨1, by rw [h]; decide⟩
    · exact ⟨0, fun e => h e.symm⟩
  obtain ⟨j, hj⟩ := j0
  apply this j (by simp [hj])
  intro x y hxy
  rw [hf x, hf y, hxy i (by simp)]

/-- Corollary 5.4 (against hedonism). Value is not a function of well-being. -/
theorem no_hedonism : ¬ ∃ f : Nat → Int, ∀ x, value x = f (x 0) := no_monism 0

end Philosophy.ETH_01

#print axioms Philosophy.ETH_01.plurality
#print axioms Philosophy.ETH_01.no_hedonism
