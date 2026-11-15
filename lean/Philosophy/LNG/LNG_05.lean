/-
LNG-05 · Meaning Facts as Primitive
Formalization of Lemma 3.1, Theorems 3.2 and 3.3 and Proposition 3.4.

A candidate meaning for "plus" is a binary function on the natural
numbers. A speaker's base is the finite record of her non-defective past
computations (Definition 2.1); a function fits the base if it agrees with
every recorded answer (Definition 2.2). The sceptic's premise, Reduction
(Definition 2.6), says that a meaning fact, if there is one, is fixed by
the base: whatever fits the base equally is meant equally.

What this file establishes. Every function that fits a finite base has a
distinct rival that fits it too (Lemma 3.1); Kripke's quus is one such
rival for any base whose arguments are below 57. Given Fit and Determinacy,
Reduction entails that no speaker means anything (Theorem 3.2: the
sceptic's argument is valid). Given in addition the datum that a speaker
means addition (Assumption 2.7), Reduction is false (Theorem 3.3).
Proposition 3.4 exhibits a model in which underdetermination, Fit and
Determinacy hold together with a meaning fact, so that underdetermination
alone does not yield the sceptical conclusion.

What it does not establish. It does not establish the datum; the
manuscript defends it in Sections 4 and 5. Nor does it model how a
speaker knows what she means.
-/

namespace Philosophy.LNG_05

/-- Candidate meanings: binary functions on the natural numbers. -/
abbrev Fn := Nat → Nat → Nat

/-- Definition 2.1. A base: finitely many recorded computations (x, y, answer). -/
abbrev Base := List (Nat × Nat × Nat)

/-- Definition 2.2. A function fits a base if it agrees with every recorded answer. -/
def Fits (f : Fn) (b : Base) : Prop := ∀ e ∈ b, f e.1 e.2.1 = e.2.2

def plus : Fn := fun x y => x + y

/-- Kripke's quus. -/
def quus : Fn := fun x y => if x < 57 ∧ y < 57 then x + y else 5

/-- A bound exceeding every argument recorded in a base. -/
def bound : Base → Nat
  | [] => 0
  | e :: r => e.1 + e.2.1 + 1 + bound r

theorem lt_bound (b : Base) : ∀ e ∈ b, e.1 < bound b ∧ e.2.1 < bound b := by
  induction b with
  | nil => intro e h; cases h
  | cons d r ih =>
    intro e h
    cases h with
    | head => simp only [bound]; omega
    | tail _ h' =>
      have := ih e h'
      simp only [bound]; omega

/-- The bent variant of a function: it agrees with `f` below `k` and differs
from it elsewhere. -/
def bend (f : Fn) (k : Nat) : Fn := fun x y => if x < k ∧ y < k then f x y else f x y + 1

/-- Lemma 3.1 (underdetermination). Every function that fits a finite base
has a distinct rival that fits it too. -/
theorem underdetermination (f : Fn) (b : Base) (h : Fits f b) :
    ∃ g, g ≠ f ∧ Fits g b := by
  refine ⟨bend f (bound b), fun heq => ?_, fun e he => ?_⟩
  · have := congrFun (congrFun heq (bound b)) (bound b)
    simp [bend] at this
  · have ⟨h1, h2⟩ := lt_bound b e he
    simp [bend, h1, h2, h e he]

/-- Quus fits every base that plus fits, if the recorded arguments are below 57;
and quus is not plus. -/
theorem quus_rival (b : Base) (hb : ∀ e ∈ b, e.1 < 57 ∧ e.2.1 < 57)
    (h : Fits plus b) : Fits quus b ∧ quus ≠ plus := by
  refine ⟨fun e he => ?_, fun heq => ?_⟩
  · have ⟨h1, h2⟩ := hb e he
    have := h e he
    simp only [quus, plus] at *
    simp [h1, h2, this]
  · have := congrFun (congrFun heq 57) 57
    simp [quus, plus] at this

/-! The axiomatic layer. -/

/-- Speakers. -/
axiom Speaker : Type

/-- Each speaker's base of non-defective past computations (Definition 2.1). -/
axiom base : Speaker → Base

/-- Definition 2.3. `Means s f`: speaker `s` means `f` by "plus" (primitive). -/
axiom Means : Speaker → Fn → Prop

/-- Assumption 2.4 (Fit). What a speaker means fits her non-defective past answers. -/
axiom fit : ∀ s f, Means s f → Fits f (base s)

/-- Assumption 2.5 (Determinacy). A speaker means at most one function by "plus". -/
axiom determinacy : ∀ s f g, Means s f → Means s g → f = g

/-- Definition 2.6 (Reduction, the sceptic's premise). Meaning facts are fixed by the
base: if a speaker means a function, she means every function that fits her base. -/
def Reduction : Prop := ∀ s f g, Means s f → Fits g (base s) → Means s g

/-- Theorem 3.2 (the sceptic's argument is valid). Given Fit and Determinacy,
Reduction entails that no speaker means anything by "plus". -/
theorem sceptic_valid (hr : Reduction) : ∀ s f, ¬ Means s f := by
  intro s f hm
  obtain ⟨g, hne, hg⟩ := underdetermination f (base s) (fit s f hm)
  exact hne (determinacy s g f (hr s f g hm hg) hm)

/-- A speaker (Kripke's interlocutor). -/
axiom kripke : Speaker

/-- Assumption 2.7 (the datum). The speaker means addition. -/
axiom datum : Means kripke plus

/-- Theorem 3.3 (main result). Given the datum, Fit and Determinacy, the
sceptic's Reduction premise is false. -/
theorem reduction_false : ¬ Reduction := fun hr => sceptic_valid hr kripke plus datum

/-- A model of the framework, with its own speakers, bases and meaning relation. -/
structure Model where
  S : Type
  base : S → Base
  means : S → Fn → Prop

/-- Proposition 3.4 (consistency). There is a model in which Fit and Determinacy
hold, some speaker means addition, and Reduction fails; underdetermination
(Lemma 3.1) holds in every model. -/
theorem consistency : ∃ M : Model,
    (∀ s f, M.means s f → Fits f (M.base s)) ∧
    (∀ s f g, M.means s f → M.means s g → f = g) ∧
    (∃ s, M.means s plus) ∧
    ¬ (∀ s f g, M.means s f → Fits g (M.base s) → M.means s g) := by
  refine ⟨⟨Unit, fun _ => [(68, 57, 125)], fun _ f => f = plus⟩, ?_, ?_, ⟨(), rfl⟩, ?_⟩
  · intro s f hf e he
    subst hf
    simp at he
    subst he
    rfl
  · intro s f g hf hg
    exact hf.trans hg.symm
  · intro hr
    have hfit : Fits (bend plus 69) [(68, 57, 125)] := by
      intro e he
      simp at he
      subst he
      decide
    have h := hr () plus (bend plus 69) rfl hfit
    have := congrFun (congrFun h 69) 69
    simp [bend, plus] at this

end Philosophy.LNG_05

#print axioms Philosophy.LNG_05.sceptic_valid
#print axioms Philosophy.LNG_05.reduction_false
#print axioms Philosophy.LNG_05.consistency
