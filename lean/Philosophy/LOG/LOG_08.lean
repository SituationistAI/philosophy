/-
LOG-08 · Absolute Generality Defended
Formalization of Lemmas 4.1 and 4.3, Theorems 4.2, 4.4, 4.6 and 4.7, and
Propositions 4.5, 5.1 and 5.2.

An object `y` codes a condition `P` with respect to a binary relation `R` if
the things that bear `R` to `y` are exactly the things satisfying `P`
(Definition 3.2). Collapse, or the all-in-one principle, says that every
condition on a domain is coded by an object of the domain (Definition 3.3).
The extensibility premise says that for every subdomain there is an object
coding the Russell condition restricted to it (Definition 3.4). The
absolutely general domain and the membership relation are primitives
(Definition 3.1), and Separation is an assumption about membership
(Assumption 3.5).

What this file establishes. Russell's lemma holds over every domain and for
every relation; Collapse fails over every domain, restricted or not; an
object coding the Russell condition of a subdomain lies outside it; the
extensibility premise fails over every domain; no map from objects onto
conditions is surjective (Cantor). Over the absolutely general domain,
given Separation, there is no universal set and no Russell set, while every
condition determines a plurality: Russell's argument refutes Collapse and
the existence of a universal set, not absolutely general quantification.
Two small models show the assumptions satisfiable together with
quantification over the whole of the model's domain, and show that every
bounded domain can be extended while the whole domain cannot.

What it does not establish. It does not establish that the quantifiers of
English reach absolutely everything, which is argued in Sections 6 and 8 of
the manuscript, nor that plural quantification is free of ontological
commitment (see LOG-09). Plural quantification is represented by
quantification over predicates of type `Obj → Prop`.
-/

namespace Philosophy.LOG_08

/-- Definition 3.2. `y` codes the condition `P` with respect to `R`. -/
def Codes {D : Type} (R : D → D → Prop) (y : D) (P : D → Prop) : Prop :=
  ∀ x, R x y ↔ P x

/-- Definition 3.3. Collapse (the all-in-one principle) over a domain. -/
def Collapse (D : Type) (R : D → D → Prop) : Prop :=
  ∀ P : D → Prop, ∃ y, Codes R y P

/-- Definition 3.4. The extensibility premise: every subdomain `S` has an
object coding the Russell condition restricted to `S`. -/
def Extensibility (D : Type) (R : D → D → Prop) : Prop :=
  ∀ S : D → Prop, ∃ y, ∀ x, S x → (R x y ↔ ¬ R x x)

/-- Lemma 4.1 (Russell's lemma). Over any domain and for any relation, no
object codes the Russell condition. -/
theorem russell (D : Type) (R : D → D → Prop) :
    ¬ ∃ y, Codes R y (fun x => ¬ R x x) := by
  intro ⟨y, hy⟩
  have h := hy y
  have n : ¬ R y y := fun hr => h.mp hr hr
  exact n (h.mpr n)

/-- Theorem 4.2 (neutrality). Collapse fails over every domain, whether or
not the domain is absolutely general. -/
theorem collapse_fails (D : Type) (R : D → D → Prop) : ¬ Collapse D R :=
  fun h => russell D R (h (fun x => ¬ R x x))

/-- Lemma 4.3 (escape). An object coding the Russell condition restricted to
a subdomain `S` lies outside `S`. -/
theorem escape {D : Type} (R : D → D → Prop) (S : D → Prop) (y : D)
    (hy : ∀ x, S x → (R x y ↔ ¬ R x x)) : ¬ S y := by
  intro hs
  have h := hy y hs
  have n : ¬ R y y := fun hr => h.mp hr hr
  exact n (h.mpr n)

/-- Theorem 4.4. The extensibility premise fails over every domain: applied
to the subdomain of everything in the domain, it yields a Russell object. -/
theorem extensibility_fails (D : Type) (R : D → D → Prop) :
    ¬ Extensibility D R := by
  intro h
  obtain ⟨y, hy⟩ := h (fun _ => True)
  exact escape R (fun _ => True) y (fun x _ => hy x trivial) trivial

/-- Proposition 4.5 (Cantor). No map from objects to conditions on objects is
onto: some condition is the value of no object. -/
theorem cantor (D : Type) (f : D → D → Prop) : ∃ P : D → Prop, ∀ y, f y ≠ P := by
  refine ⟨fun x => ¬ f x x, fun y hy => ?_⟩
  have h : f y y ↔ ¬ f y y := by
    constructor
    · intro hf; rw [hy] at hf; exact hf
    · intro hf; rw [hy]; exact hf
  have n : ¬ f y y := fun hr => h.mp hr hr
  exact n (h.mpr n)

/-- Definition 3.1. The domain of absolutely general quantification:
everything there is. -/
axiom Obj : Type

/-- Definition 3.1. Membership, a relation between objects. -/
axiom mem : Obj → Obj → Prop

/-- Assumption 3.5 (Separation). For any object `a` and any condition `P`,
some object has as members exactly the members of `a` that satisfy `P`. -/
axiom separation : ∀ (a : Obj) (P : Obj → Prop), ∃ b, ∀ x, mem x b ↔ (mem x a ∧ P x)

/-- Theorem 4.6. Given Separation, nothing has every object as a member. -/
theorem no_universal_set : ¬ ∃ u : Obj, ∀ x, mem x u := by
  intro ⟨u, hu⟩
  obtain ⟨r, hr⟩ := separation u (fun x => ¬ mem x x)
  exact russell Obj mem ⟨r, fun x =>
    (hr x).trans ⟨fun h => h.2, fun h => ⟨hu x, h⟩⟩⟩

/-- Theorem 4.7 (main result). Over the absolutely general domain: every
condition determines a plurality (plural comprehension, P1); there is no
Russell set; Collapse fails; and, given Separation, there is no universal
set. None of these is a contradiction. -/
theorem russell_no_threat :
    (∀ P : Obj → Prop, ∃ X : Obj → Prop, ∀ x, X x ↔ P x) ∧
    (¬ ∃ r, Codes mem r (fun x => ¬ mem x x)) ∧
    ¬ Collapse Obj mem ∧
    ¬ ∃ u : Obj, ∀ x, mem x u :=
  ⟨fun P => ⟨P, fun _ => Iff.rfl⟩, russell Obj mem, collapse_fails Obj mem,
    no_universal_set⟩

/-- Proposition 5.1. A model of the assumptions: on the two objects `false`
(the empty set) and `true` (its singleton), with membership `x = false ∧
y = true`, Separation holds and no object has every object as a member. -/
theorem two_element_model :
    let m : Bool → Bool → Prop := fun x y => x = false ∧ y = true
    (∀ (a : Bool) (P : Bool → Prop), ∃ b, ∀ x, m x b ↔ (m x a ∧ P x)) ∧
    ¬ ∃ u, ∀ x, m x u := by
  intro m
  constructor
  · intro a P
    cases a
    · exact ⟨false, fun x => by simp [m]⟩
    · by_cases hp : P false
      · refine ⟨true, fun x => ?_⟩
        cases x <;> simp [m, hp]
      · refine ⟨false, fun x => ?_⟩
        cases x <;> simp [m, hp]
  · intro ⟨u, hu⟩
    have := (hu true).1
    exact absurd this (by decide)

/-- Proposition 5.2. In the domain of natural numbers with membership `<`:
every bounded subdomain is extended by an object outside it that codes the
Russell condition restricted to it, but the whole domain is not. -/
theorem bounded_extend :
    (∀ S : Nat → Prop, (∃ n, ∀ x, S x → x < n) →
      ∃ y, ¬ S y ∧ ∀ x, S x → (x < y ↔ ¬ x < x)) ∧
    ¬ ∃ y : Nat, ∀ x, (x < y ↔ ¬ x < x) := by
  constructor
  · intro S ⟨n, hn⟩
    refine ⟨n, fun hs => absurd (hn n hs) (Nat.lt_irrefl n), fun x hx => ?_⟩
    have := hn x hx
    constructor
    · intro _; exact Nat.lt_irrefl x
    · intro _; exact this
  · intro ⟨y, hy⟩
    exact Nat.lt_irrefl y ((hy y).mpr (Nat.lt_irrefl y))

end Philosophy.LOG_08

#print axioms Philosophy.LOG_08.russell_no_threat
#print axioms Philosophy.LOG_08.extensibility_fails
#print axioms Philosophy.LOG_08.bounded_extend
