/-
LOG-12 · Identity Is Absolute
Formalization of Theorems 3.1 and 3.2, Corollary 3.3 and Proposition 3.4.

Objects, sortals, the relation "a is the same F as b" and the relation
"a is an F" are primitives (Definition 2.1). An identity relation is one
that is reflexive on its field and substitutive for every predicate
(Definition 2.2, Principle P1). Relativity of identity is Geach's thesis:
for some sortals F and G and some Gs a and b, a is the same F as b but not
the same G as b (Definition 2.3). Sortal relations are assumed reflexive on
the things that fall under the sortal (Assumption 2.4), as Geach accepts.

What this file establishes. Every identity relation coincides with absolute
identity (Lean's `=`) on the pairs it relates; any two identity relations
agree; if Geach's thesis holds, the relation "same F" in it fails
substitutivity. A two-element model shows that restricted substitutivity is
consistent with relativity. It does not establish that "is the same God as"
is an identity relation in this sense; the theological case is discussed in
Section 5 of the manuscript (see REL-13).
-/

namespace Philosophy.LOG_12

/-- Definition 2.1. Objects. -/
axiom Obj : Type
/-- Definition 2.1. Sortals. -/
axiom Sortal : Type
/-- Definition 2.1. `same F a b`: a is the same F as b. -/
axiom same : Sortal → Obj → Obj → Prop
/-- Definition 2.1. `isA F a`: a is an F. -/
axiom isA : Sortal → Obj → Prop

/-- Principle P1 (Substitutivity, Leibniz's Law). -/
def Substitutive (R : Obj → Obj → Prop) : Prop :=
  ∀ (P : Obj → Prop) (x y : Obj), R x y → P x → P y

/-- Definition 2.2. The relation `same F` is an identity relation: reflexive
on Fs and substitutive. -/
def IsIdentity (F : Sortal) : Prop :=
  (∀ x, isA F x → same F x x) ∧ Substitutive (same F)

/-- Definition 2.3. Geach's thesis of the relativity of identity. -/
def Relativity : Prop :=
  ∃ (F G : Sortal) (a b : Obj), isA G a ∧ isA G b ∧ same F a b ∧ ¬ same G a b

/-- Assumption 2.4. Sortal relations are reflexive on their sortal. -/
axiom sortal_reflexive : ∀ (G : Sortal) (x : Obj), isA G x → same G x x

/-- Theorem 3.1. A substitutive relation relates only what is absolutely
identical. -/
theorem substitutive_absolute (R : Obj → Obj → Prop) (h : Substitutive R)
    (x y : Obj) (hxy : R x y) : x = y :=
  h (fun z => x = z) x y hxy rfl

/-- Theorem 3.2. Two identity relations agree on the things that fall under
both sortals. -/
theorem identities_agree (F G : Sortal) (hF : IsIdentity F) (hG : IsIdentity G)
    (a b : Obj) (ha : isA F a) (hb : isA G a) : same F a b ↔ same G a b := by
  constructor
  · intro h
    have e := substitutive_absolute _ hF.2 a b h
    subst e; exact hG.1 a hb
  · intro h
    have e := substitutive_absolute _ hG.2 a b h
    subst e; exact hF.1 a ha

/-- Corollary 3.3. If Geach's thesis holds, the relation "same F" in it is
not substitutive, and so is not an identity relation. -/
theorem relativity_fails_substitutivity :
    Relativity → ∃ F : Sortal, ¬ Substitutive (same F) := by
  intro ⟨F, G, a, b, ha, _, hF, hG⟩
  refine ⟨F, fun hs => hG ?_⟩
  have e := substitutive_absolute _ hs a b hF
  subst e
  exact sortal_reflexive G a ha

/-- Proposition 3.4. Restricted substitutivity is consistent with relativity:
on two objects, a relation that holds universally is substitutive for every
predicate that does not discriminate between them, and relates two distinct
objects that equality does not relate. -/
theorem restricted_model :
    let R1 : Bool → Bool → Prop := fun _ _ => True
    let R2 : Bool → Bool → Prop := fun x y => x = y
    (∀ P : Bool → Prop, (P true ↔ P false) → ∀ x y, R1 x y → P x → P y) ∧
    R1 true false ∧ ¬ R2 true false ∧
    ¬ (∀ P : Bool → Prop, ∀ x y, R1 x y → P x → P y) := by
  refine ⟨?_, trivial, by decide, ?_⟩
  · intro P hP x y _ hx
    cases x <;> cases y
    all_goals first | exact hx | exact hP.mp hx | exact hP.mpr hx
  · intro h
    have := h (fun z => z = true) true false trivial rfl
    exact absurd this (by decide)

end Philosophy.LOG_12

#print axioms Philosophy.LOG_12.substitutive_absolute
#print axioms Philosophy.LOG_12.relativity_fails_substitutivity
