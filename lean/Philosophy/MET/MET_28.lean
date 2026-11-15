/-
MET-28 · Black's Spheres Vindicated
Formalization of Theorems 3.1 and 3.2 and Proposition 4.1 (revised version of
7 October 2026).

Black's world is modelled by the two values of `Bool`, with the symmetry that
exchanges them given by negation. A property or relation is qualitative if it
is invariant under the symmetry (Definition 2.2).

What this file establishes. No qualitative property or relation discerns the
spheres absolutely or relatively, while the qualitative irreflexive relation
of distinctness discerns them weakly. The module uses no axioms. It does not
establish that Definition 2.2 is the right account of qualitativeness, nor that
Black's world is possible.
-/

namespace Philosophy.MET_28

/-- The two spheres. -/
abbrev Sphere := Bool

def a : Sphere := true
def b : Sphere := false

/-- The symmetry of Black's world (Definition 2.1). -/
def σ (x : Sphere) : Sphere := !x

/-- Definition 2.2, for properties. -/
def Qualitative1 (P : Sphere → Prop) : Prop := ∀ x, P x ↔ P (σ x)

/-- Definition 2.2, for relations. -/
def Qualitative2 (R : Sphere → Sphere → Prop) : Prop := ∀ x y, R x y ↔ R (σ x) (σ y)

/-- Theorem 3.1. No qualitative property discerns the spheres. -/
theorem absolutely_indiscernible (P : Sphere → Prop) (h : Qualitative1 P) :
    P a ↔ P b :=
  h a

/-- Theorem 3.2. No qualitative relation discerns the spheres relatively. -/
theorem relatively_indiscernible (R : Sphere → Sphere → Prop) (h : Qualitative2 R) :
    R a b ↔ R b a :=
  h a b

/-- Proposition 4.1. The spheres are weakly discernible. The relation used is
distinctness, standing in for "being two miles apart", which the symmetry
preserves. -/
theorem weakly_discernible :
    ∃ R : Sphere → Sphere → Prop, Qualitative2 R ∧ R a b ∧ ∀ x, ¬ R x x := by
  refine ⟨fun x y => x ≠ y, ?_, ?_, ?_⟩
  · intro x y
    cases x <;> cases y <;> simp [σ]
  · simp [a, b]
  · intro x h; exact h rfl

end Philosophy.MET_28

#print axioms Philosophy.MET_28.weakly_discernible
