/-
LOG-16 · The Logical Constants and Permutation Invariance
Formalization of Propositions 4.1 and 4.2, Lemma 4.3, Theorem 4.4,
Corollaries 4.5 and 4.6, Theorem 4.7 and Propositions 4.8 and 4.9.

A domain is an arbitrary type. A permutation is a function with a two-sided
inverse, and more generally a bijection between two domains (Definition 3.1).
Operations of type <1> (quantifiers over one predicate) and of type <1,1>
(binary quantifiers, determiners) act on predicates; a permutation acts on
them by composition, and an operation is permutation invariant if its value
is unchanged by every permutation (Definitions 3.2 and 3.3). Cardinal
comparison and equinumerosity are defined by injections and bijections
between predicates (Definition 3.4), and "most A are B" means that there are
more As that are Bs than As that are not Bs (Definition 3.5). The invariance
criterion (Principle P1) is stated as an axiom about a primitive predicate of
operations, "is a logical constant".

What this file establishes. Identity, the connectives and the first-order
quantifiers are invariant, and invariance is closed under Boolean
combination; cardinal comparison is preserved by bijections; "most" depends
only on the cardinalities of A ∩ B and A \ B, across domains; it is
invariant under all permutations of any domain, finite or infinite, and
hence, given P1, a logical constant. A type <1> operation is invariant iff
its value depends only on the cardinalities of its argument and of the
argument's complement. An operation that mentions a particular object is not
invariant. The operation McGee uses against the criterion is invariant and
definable from first-order logical constants.

What it does not establish. It does not establish Principle P1, which is
defended in Sections 5 and 7 of the manuscript. It does not prove that
"most" is not first-order definable (Barwise and Cooper), which the
manuscript cites but does not formalize.
-/

namespace Philosophy.LOG_16

/-! ## Framework -/

/-- Definition 3.1. A bijection between domains `D` and `E`: a function with a
two-sided inverse. -/
structure Bij (D E : Type) where
  f : D → E
  inv : E → D
  left : ∀ x, inv (f x) = x
  right : ∀ y, f (inv y) = y

/-- Definition 3.1. A permutation of `D` is a bijection from `D` to itself. -/
abbrev Perm (D : Type) := Bij D D

/-- Definition 3.3. Invariance of a binary relation on individuals. -/
def InvRel {D : Type} (R : D → D → Prop) : Prop :=
  ∀ (p : Perm D) (x y : D), R x y ↔ R (p.f x) (p.f y)

/-- Definition 3.3. Invariance of an operation of type <1>. Definition 3.2:
a permutation `p` acts on a predicate `A` by `A ∘ p.f`. -/
def Inv1 {D : Type} (Q : (D → Prop) → Prop) : Prop :=
  ∀ (p : Perm D) (A : D → Prop), Q A ↔ Q (fun x => A (p.f x))

/-- Definition 3.3. Invariance of an operation of type <1,1>. -/
def Inv11 {D : Type} (Q : (D → Prop) → (D → Prop) → Prop) : Prop :=
  ∀ (p : Perm D) (A B : D → Prop),
    Q A B ↔ Q (fun x => A (p.f x)) (fun x => B (p.f x))

/-- Definition 3.4. `CardLe X Y`: there are at most as many `X`s as `Y`s,
witnessed by a function that maps `X` into `Y` injectively. -/
def CardLe {D E : Type} (X : D → Prop) (Y : E → Prop) : Prop :=
  ∃ h : D → E, (∀ x, X x → Y (h x)) ∧
    (∀ x y, X x → X y → h x = h y → x = y)

/-- Definition 3.4. `Equinum X Y`: the `X`s and the `Y`s are equinumerous,
witnessed by mutually inverse maps between them. -/
def Equinum {D E : Type} (X : D → Prop) (Y : E → Prop) : Prop :=
  ∃ (h : D → E) (k : E → D), (∀ x, X x → Y (h x)) ∧ (∀ y, Y y → X (k y)) ∧
    (∀ x, X x → k (h x) = x) ∧ (∀ y, Y y → h (k y) = y)

/-- Definition 3.5. "Most As are Bs": there are at most as many As that are
not Bs as As that are Bs, and not conversely. -/
def most {D : Type} (A B : D → Prop) : Prop :=
  CardLe (fun x => A x ∧ ¬ B x) (fun x => A x ∧ B x) ∧
  ¬ CardLe (fun x => A x ∧ B x) (fun x => A x ∧ ¬ B x)

/-- The universal quantifier as an operation of type <1>. -/
def every {D : Type} (A : D → Prop) : Prop := ∀ x, A x

/-- The existential quantifier as an operation of type <1>. -/
def some {D : Type} (A : D → Prop) : Prop := ∃ x, A x

/-- Primitive: being a logical constant, for operations of type <1>. -/
axiom LogicalConstant1 : {D : Type} → ((D → Prop) → Prop) → Prop

/-- Primitive: being a logical constant, for operations of type <1,1>. -/
axiom LogicalConstant11 : {D : Type} → ((D → Prop) → (D → Prop) → Prop) → Prop

/-- Principle P1 (the invariance criterion), for operations of type <1>. -/
axiom criterion1 : ∀ {D : Type} (Q : (D → Prop) → Prop),
  LogicalConstant1 Q ↔ Inv1 Q

/-- Principle P1 (the invariance criterion), for operations of type <1,1>. -/
axiom criterion11 : ∀ {D : Type} (Q : (D → Prop) → (D → Prop) → Prop),
  LogicalConstant11 Q ↔ Inv11 Q

/-! ## Results -/

/-- Proposition 4.1 (i). Identity is invariant. -/
theorem identity_invariant (D : Type) : InvRel (fun x y : D => x = y) := by
  intro p x y
  constructor
  · intro h; rw [h]
  · intro h
    have := congrArg p.inv h
    rw [p.left, p.left] at this
    exact this

/-- Proposition 4.1 (ii). The universal and existential quantifiers are
invariant. -/
theorem quantifiers_invariant (D : Type) :
    Inv1 (@every D) ∧ Inv1 (@some D) := by
  constructor
  · intro p A
    constructor
    · intro h x; exact h (p.f x)
    · intro h y
      have : A (p.f (p.inv y)) := h (p.inv y)
      rw [p.right] at this
      exact this
  · intro p A
    constructor
    · intro ⟨y, hy⟩
      refine ⟨p.inv y, ?_⟩
      show A (p.f (p.inv y))
      rw [p.right]; exact hy
    · intro ⟨x, hx⟩; exact ⟨p.f x, hx⟩

/-- Proposition 4.1 (iii). Invariance is closed under the connectives, and
every operation with a constant value is invariant. -/
theorem boolean_closure {D : Type} (Q R : (D → Prop) → Prop)
    (hQ : Inv1 Q) (hR : Inv1 R) (C : Prop) :
    Inv1 (fun A => Q A ∧ R A) ∧ Inv1 (fun A => Q A ∨ R A) ∧
    Inv1 (fun A => ¬ Q A) ∧ Inv1 (fun _ : D → Prop => C) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p A; exact and_congr (hQ p A) (hR p A)
  · intro p A; exact or_congr (hQ p A) (hR p A)
  · intro p A; exact not_congr (hQ p A)
  · intro _ _; exact Iff.rfl

/-- Equinumerosity yields cardinal comparison in both directions. -/
theorem equinum_le {D E : Type} {X : D → Prop} {Y : E → Prop}
    (h : Equinum X Y) : CardLe X Y ∧ CardLe Y X := by
  obtain ⟨h, k, hXY, hYX, hkh, hhk⟩ := h
  constructor
  · refine ⟨h, hXY, ?_⟩
    intro x y hx hy he
    rw [← hkh x hx, ← hkh y hy, he]
  · refine ⟨k, hYX, ?_⟩
    intro x y hx hy he
    rw [← hhk x hx, ← hhk y hy, he]

/-- Cardinal comparison is transitive (composition of injections). -/
theorem cardLe_trans {D E F : Type} {X : D → Prop} {Y : E → Prop}
    {Z : F → Prop} (h1 : CardLe X Y) (h2 : CardLe Y Z) : CardLe X Z := by
  obtain ⟨g, gm, gi⟩ := h1
  obtain ⟨h, hm, hi⟩ := h2
  refine ⟨fun x => h (g x), fun x hx => hm _ (gm x hx), ?_⟩
  intro x y hx hy he
  exact gi x y hx hy (hi _ _ (gm x hx) (gm y hy) he)

/-- Proposition 4.2. Cardinal comparison depends only on the cardinalities
compared: it is preserved when each side is replaced by an equinumerous
predicate, on the same domain or another. -/
theorem cardLe_transport {D D' E E' : Type} {X : D → Prop} {X' : D' → Prop}
    {Y : E → Prop} {Y' : E' → Prop}
    (hX : Equinum X X') (hY : Equinum Y Y') : CardLe X Y ↔ CardLe X' Y' := by
  constructor
  · intro h
    exact cardLe_trans (cardLe_trans (equinum_le hX).2 h) (equinum_le hY).1
  · intro h
    exact cardLe_trans (cardLe_trans (equinum_le hX).1 h) (equinum_le hY).2

/-- Lemma 4.3. Every predicate is equinumerous with its image under a
bijection, in either direction. -/
theorem equinum_bij {D E : Type} (X : D → Prop) (b : Bij D E) :
    Equinum X (fun y => X (b.inv y)) ∧ Equinum (fun y => X (b.inv y)) X := by
  constructor
  · refine ⟨b.f, b.inv, ?_, fun y hy => hy, fun x _ => b.left x,
      fun y _ => b.right y⟩
    intro x hx; show X (b.inv (b.f x)); rw [b.left]; exact hx
  · refine ⟨b.inv, b.f, fun y hy => hy, ?_, fun y _ => b.right y,
      fun x _ => b.left x⟩
    intro x hx; show X (b.inv (b.f x)); rw [b.left]; exact hx

/-- The inverse of a bijection. -/
def Bij.symm {D E : Type} (b : Bij D E) : Bij E D :=
  ⟨b.inv, b.f, b.right, b.left⟩

/-- Theorem 4.4. "Most" depends only on the cardinalities of `A ∩ B` and
`A \ B`: if these are equinumerous with `A' ∩ B'` and `A' \ B'`, on any
domains, then most As are Bs iff most A's are B's. -/
theorem most_cardinal {D E : Type} (A B : D → Prop) (A' B' : E → Prop)
    (hin : Equinum (fun x => A x ∧ B x) (fun y => A' y ∧ B' y))
    (hout : Equinum (fun x => A x ∧ ¬ B x) (fun y => A' y ∧ ¬ B' y)) :
    most A B ↔ most A' B' := by
  unfold most
  rw [cardLe_transport hout hin, cardLe_transport hin hout]

/-- Corollary 4.5. "Most" is isomorphism invariant: transporting `A` and
`B` along any bijection between domains leaves its value unchanged. -/
theorem most_iso {D E : Type} (b : Bij D E) (A B : D → Prop) :
    most A B ↔ most (fun y => A (b.inv y)) (fun y => B (b.inv y)) :=
  most_cardinal A B _ _ (equinum_bij (fun x => A x ∧ B x) b).1
    (equinum_bij (fun x => A x ∧ ¬ B x) b).1

/-- Corollary 4.5. "Most" is invariant under every permutation of every
domain. -/
theorem most_invariant (D : Type) : Inv11 (@most D) := by
  intro p A B
  exact most_iso p.symm A B

/-- Corollary 4.6 (main result). Given Principle P1, "most" is a logical
constant on every domain. -/
theorem most_is_logical (D : Type) : LogicalConstant11 (@most D) :=
  (criterion11 _).mpr (most_invariant D)

/-- Theorem 4.7. An operation of type <1> is permutation invariant iff its
value depends only on the cardinality of its argument and of the argument's
complement. -/
theorem inv1_iff_cardinal {D : Type} (Q : (D → Prop) → Prop) :
    Inv1 Q ↔ ∀ A A' : D → Prop, Equinum A A' →
      Equinum (fun x => ¬ A x) (fun x => ¬ A' x) → (Q A ↔ Q A') := by
  constructor
  · intro hQ A A' ⟨h, k, hm, km, kh, hk⟩ ⟨h2, k2, hm2, km2, kh2, hk2⟩
    have dA := Classical.propDecidable
    let g : D → D := fun y => if A' y then k y else k2 y
    let g' : D → D := fun x => if A x then h x else h2 x
    have left : ∀ y, g' (g y) = y := by
      intro y
      by_cases hy : A' y
      · have hA : A (k y) := km y hy
        simp only [g, g', hy, hA, if_true]
        exact hk y hy
      · have hA : ¬ A (k2 y) := km2 y hy
        simp only [g, g', hy, hA, if_false]
        exact hk2 y hy
    have right : ∀ x, g (g' x) = x := by
      intro x
      by_cases hx : A x
      · have hA : A' (h x) := hm x hx
        simp only [g, g', hx, hA, if_true]
        exact kh x hx
      · have hA : ¬ A' (h2 x) := hm2 x hx
        simp only [g, g', hx, hA, if_false]
        exact kh2 x hx
    let p : Perm D := ⟨g, g', left, right⟩
    have e : (fun y => A (p.f y)) = A' := by
      funext y
      apply propext
      by_cases hy : A' y
      · have hA : A (k y) := km y hy
        show A (if A' y then k y else k2 y) ↔ A' y
        rw [if_pos hy]
        exact ⟨fun _ => hy, fun _ => hA⟩
      · have hA : ¬ A (k2 y) := km2 y hy
        show A (if A' y then k y else k2 y) ↔ A' y
        rw [if_neg hy]
        exact ⟨fun h => absurd h hA, fun h => absurd h hy⟩
    rw [hQ p A, e]
  · intro hC p A
    let q : Bij D D := p.symm
    exact hC A _ (equinum_bij A q).1 (equinum_bij (fun x => ¬ A x) q).1

/-- The transposition of two objects. -/
noncomputable def swap {D : Type} (a b : D) : D → D := by
  classical
  exact fun x => if x = a then b else if x = b then a else x

theorem swap_swap {D : Type} (a b : D) (x : D) : swap a b (swap a b x) = x := by
  classical
  unfold swap
  by_cases ha : x = a
  · subst ha
    by_cases hb : b = x
    · simp [hb]
    · simp [hb]
  · by_cases hb : x = b
    · subst hb; simp [ha]
    · simp [ha, hb]

/-- Proposition 4.8. On any domain with two distinct objects, the operation
"A holds of a", which mentions the particular object `a`, is not invariant,
and so, given P1, is not a logical constant. -/
theorem name_not_invariant {D : Type} (a b : D) (hab : a ≠ b) :
    ¬ Inv1 (fun A : D → Prop => A a) ∧
    ¬ LogicalConstant1 (fun A : D → Prop => A a) := by
  have hn : ¬ Inv1 (fun A : D → Prop => A a) := by
    intro h
    let p : Perm D := ⟨swap a b, swap a b, swap_swap a b, swap_swap a b⟩
    have := (h p (fun x => x = a)).mp rfl
    have hs : swap a b a = b := by
      classical
      unfold swap; simp
    exact hab (by
      have h2 : swap a b a = a := this
      rw [hs] at h2
      exact h2.symm)
  exact ⟨hn, fun hl => hn ((criterion1 _).mp hl)⟩

/-- The condition that the domain has at least two objects. -/
def TwoOrMore (D : Type) : Prop := ∃ x y : D, x ≠ y

/-- McGee's operation: the universal quantifier on domains with at least two
objects, the existential quantifier on smaller domains. -/
def mcgee {D : Type} (A : D → Prop) : Prop :=
  (TwoOrMore D ∧ every A) ∨ (¬ TwoOrMore D ∧ some A)

/-- Proposition 4.9. McGee's operation is invariant, and so, given P1, a
logical constant; it is defined from identity, the quantifiers and the
connectives. -/
theorem mcgee_invariant (D : Type) :
    Inv1 (@mcgee D) ∧ LogicalConstant1 (@mcgee D) := by
  have ⟨he, hs⟩ := quantifiers_invariant D
  have h : Inv1 (@mcgee D) := fun p A =>
    or_congr (and_congr Iff.rfl (he p A)) (and_congr Iff.rfl (hs p A))
  exact ⟨h, (criterion1 _).mpr h⟩

end Philosophy.LOG_16

#print axioms Philosophy.LOG_16.most_invariant
#print axioms Philosophy.LOG_16.most_is_logical
#print axioms Philosophy.LOG_16.inv1_iff_cardinal
#print axioms Philosophy.LOG_16.mcgee_invariant
