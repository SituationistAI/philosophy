/-
LOG-09 · Second-Order Logic Is Logic
Formalization of Theorems 3.1 and 3.6, Corollary 3.2 and Propositions 3.3
and 3.5.

Individuals form a type `D` (Definition 2.1). Second-order variables range
over all conditions on individuals, `D → Prop` (the standard semantics,
Definition 2.1). A permutation of individuals acts on conditions, and on
second-order conditions, by composition (Definition 2.2). The invariance
criterion of LOG-16 (Principle P1) is stated as an axiom about a primitive
predicate "is a logical constant" for operations on second-order
conditions. The thesis that second-order quantification is set theory in
disguise is stated as Definition 2.4: some objects of the domain (the sets)
and a membership relation provide, for every condition, an object whose
members are exactly the things satisfying it.

What this file establishes. The second-order quantifiers are invariant
under all permutations, and so, given P1, logical constants. Identity is
second-order definable: a = b iff b has every property that a has. Frege's
ancestral is second-order definable and provably contains its relation and
is transitive. The disguise thesis fails over every domain: the conditions
on a domain cannot all be coded by objects of that domain, so a reduction
of second-order quantification to first-order quantification over sets
requires sets outside the domain, and is unavailable when the domain is
absolutely everything (LOG-08).

What it does not establish. It does not establish P1, which is argued in
LOG-16, nor that the standard rather than the Henkin semantics gives the
meaning of the second-order quantifiers (Section 4 of the manuscript).
-/

namespace Philosophy.LOG_09

/-- Definition 2.1. The domain of individuals. -/
axiom D : Type

/-- Definition 2.2. A permutation of the individuals. -/
structure Perm where
  f : D → D
  inv : D → D
  left : ∀ x, inv (f x) = x
  right : ∀ y, f (inv y) = y

/-- Definition 2.2. Invariance of an operation on second-order conditions:
a permutation `p` sends a condition `X` to `X ∘ p.inv`, and a second-order
condition `Φ` to `fun X => Φ (X ∘ p.f)`. -/
def Inv2 (Q : ((D → Prop) → Prop) → Prop) : Prop :=
  ∀ (p : Perm) (Φ : (D → Prop) → Prop), Q Φ ↔ Q (fun X => Φ (fun x => X (p.f x)))

/-- The second-order universal quantifier (standard semantics). -/
def forall2 (Φ : (D → Prop) → Prop) : Prop := ∀ X : D → Prop, Φ X

/-- The second-order existential quantifier (standard semantics). -/
def exists2 (Φ : (D → Prop) → Prop) : Prop := ∃ X : D → Prop, Φ X

/-- Primitive: being a logical constant, for operations on second-order
conditions. -/
axiom LogicalConstant2 : (((D → Prop) → Prop) → Prop) → Prop

/-- Principle P1 (the invariance criterion of LOG-16). An operation is a
logical constant if it is invariant under all permutations. -/
axiom criterion : ∀ Q, Inv2 Q → LogicalConstant2 Q

/-- Theorem 3.1. The second-order quantifiers are permutation invariant. -/
theorem quantifiers2_invariant : Inv2 forall2 ∧ Inv2 exists2 := by
  constructor
  · intro p Φ
    constructor
    · intro h X; exact h _
    · intro h X
      have e : (fun x => X (p.inv (p.f x))) = X := by
        funext x; rw [p.left]
      have : Φ (fun x => X (p.inv (p.f x))) := h (fun y => X (p.inv y))
      rw [e] at this
      exact this
  · intro p Φ
    constructor
    · intro ⟨X, hX⟩
      refine ⟨fun y => X (p.inv y), ?_⟩
      have e : (fun x => X (p.inv (p.f x))) = X := by
        funext x; rw [p.left]
      show Φ (fun x => X (p.inv (p.f x)))
      rw [e]; exact hX
    · intro ⟨X, hX⟩; exact ⟨_, hX⟩

/-- Corollary 3.2 (main result). Given P1, the second-order quantifiers are
logical constants. -/
theorem second_order_logical :
    LogicalConstant2 forall2 ∧ LogicalConstant2 exists2 :=
  ⟨criterion _ quantifiers2_invariant.1, criterion _ quantifiers2_invariant.2⟩

/-- Proposition 3.3 (Leibniz). Identity is second-order definable: `a = b`
iff `b` has every property that `a` has. -/
theorem identity_definable (a b : D) : a = b ↔ ∀ X : D → Prop, X a → X b := by
  constructor
  · intro h X hx; rw [← h]; exact hx
  · intro h; exact h (fun z => a = z) rfl

/-- Definition 3.4 (Frege). The ancestral of `R`: `b` has every property
that is hereditary under `R` and belongs to every `R`-successor of `a`. -/
def ancestral (R : D → D → Prop) (a b : D) : Prop :=
  ∀ X : D → Prop, (∀ z, R a z → X z) → (∀ y z, X y → R y z → X z) → X b

/-- Proposition 3.5 (Frege, Begriffsschrift). The ancestral contains its
relation and is transitive. -/
theorem ancestral_props (R : D → D → Prop) :
    (∀ a b, R a b → ancestral R a b) ∧
    (∀ a b c, ancestral R a b → ancestral R b c → ancestral R a c) := by
  constructor
  · intro a b h X hX _; exact hX b h
  · intro a b c hab hbc X hX hher
    have hb : X b := hab X hX hher
    exact hbc X (fun z hz => hher b z hb hz) hher

/-- Definition 2.4. The disguise thesis over a domain `E`: some objects `S`
(the sets) and a membership relation code every condition, so that
second-order quantification is first-order quantification over sets. -/
def Disguise (E : Type) : Prop :=
  ∃ (S : E → Prop) (mem : E → E → Prop),
    ∀ P : E → Prop, ∃ y, S y ∧ ∀ x, mem x y ↔ P x

/-- Theorem 3.6. The disguise thesis fails over every domain: the sets that
would code all conditions on a domain cannot all belong to it. -/
theorem no_disguise (E : Type) : ¬ Disguise E := by
  intro ⟨_, mem, h⟩
  obtain ⟨y, _, hy⟩ := h (fun x => ¬ mem x x)
  have h1 := hy y
  have n : ¬ mem y y := fun hr => h1.mp hr hr
  exact n (h1.mpr n)

end Philosophy.LOG_09

#print axioms Philosophy.LOG_09.second_order_logical
#print axioms Philosophy.LOG_09.identity_definable
#print axioms Philosophy.LOG_09.no_disguise
