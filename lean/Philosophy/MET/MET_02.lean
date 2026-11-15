/-
MET-02 · The Sparse Universals Theorem
Formalization of Theorems 4.1, 4.3, 4.4, 5.1, 5.5 and 5.6, Lemmas 4.2 and
5.3, Corollaries 4.5 and 5.2 and Proposition 5.4.

Objects are a primitive type. A property is any function from objects to
propositions (the abundant conception); some properties are genuine
(Definition 3.1), and some binary relations are genuine. Resemblance is a
primitive binary relation between objects.

A permutation of the objects is a pair of mutually inverse functions
(Definition 3.2). A reshuffle is a permutation that maps the genuine
properties onto genuine properties (Definition 3.2). A symmetry is a
permutation that preserves every genuine property and every genuine
relation; a monadic symmetry preserves every genuine property
(Definition 3.3). Constructions (Definition 3.4) are built from genuine
properties by negation, arbitrary conjunction, arbitrary disjunction and
relational projection along a genuine relation.

What this file establishes. Given Principles P1 to P4 (axioms below):
universals exist (Theorem 4.1); if every property were genuine, resemblance
could not discriminate between any two pairs of distinct objects
(Theorem 4.3); hence some pairs of distinct objects are related by no
reshuffle (Theorem 4.4) and not every property is genuine (Corollary 4.5);
every constructed property is preserved by every symmetry (Theorem 5.1);
a property supervenes on the genuine properties exactly when it is
preserved by every monadic symmetry (Proposition 5.4); every property that
supervenes on the genuine properties is constructed from them
(Theorem 5.5); and the three results combine into Theorem 5.6.

What it does not establish. It does not establish the principles, which
are defended in Sections 3 and 8 of the manuscript. It does not establish
that the genuine properties are few in number in any numerical sense, nor
that every extrinsic qualitative property is constructed (Remark 5.7).
-/

namespace Philosophy.MET_02

open Classical

/-- Objects. -/
axiom Obj : Type

/-- Definition 3.1. Genuine (sparse) properties. -/
axiom Genuine : (Obj → Prop) → Prop

/-- Definition 3.1. Genuine (sparse) binary relations. -/
axiom GenuineRel : (Obj → Obj → Prop) → Prop

/-- Objective resemblance between objects (Section 3). -/
axiom Res : Obj → Obj → Prop

/-- Definition 3.1. A universal is a genuine property instantiated by two
distinct objects. -/
def IsUniversal (U : Obj → Prop) : Prop :=
  Genuine U ∧ ∃ x y, x ≠ y ∧ U x ∧ U y

/-- Definition 3.2. A permutation of the objects, given with its inverse. -/
def Perm (f g : Obj → Obj) : Prop :=
  (∀ x, g (f x) = x) ∧ (∀ x, f (g x) = x)

/-- Definition 3.2. A reshuffle: a permutation mapping genuine properties
onto genuine properties. -/
def Reshuffle (f g : Obj → Obj) : Prop :=
  Perm f g ∧ (∀ U, Genuine U → Genuine (fun x => U (g x))) ∧
    (∀ U, Genuine U → Genuine (fun x => U (f x)))

/-- Definition 3.3. A symmetry preserves every genuine property and
relation. -/
def Symmetry (f g : Obj → Obj) : Prop :=
  Perm f g ∧ (∀ U, Genuine U → ∀ x, U x ↔ U (f x)) ∧
    (∀ R, GenuineRel R → ∀ x y, R x y ↔ R (f x) (f y))

/-- Definition 3.3. A monadic symmetry preserves every genuine property. -/
def MonoSymmetry (f g : Obj → Obj) : Prop :=
  Perm f g ∧ (∀ U, Genuine U → ∀ x, U x ↔ U (f x))

/-- Definition 3.4. Constructions from the genuine properties and
relations. -/
inductive Con : Type 1 where
  | atom (U : Obj → Prop) (h : Genuine U) : Con
  | neg (c : Con) : Con
  | conj (ι : Type) (k : ι → Con) : Con
  | disj (ι : Type) (k : ι → Con) : Con
  | proj (R : Obj → Obj → Prop) (h : GenuineRel R) (c : Con) : Con

/-- Definition 3.4. The property a construction expresses. -/
def eval : Con → Obj → Prop
  | .atom U _, x => U x
  | .neg c, x => ¬ eval c x
  | .conj _ k, x => ∀ i, eval (k i) x
  | .disj _ k, x => ∃ i, eval (k i) x
  | .proj R _ c, x => ∃ y, R x y ∧ eval c y

/-- Definition 3.4. A property is constructed if some construction
expresses it. -/
def Constructed (P : Obj → Prop) : Prop := ∃ c : Con, ∀ x, eval c x ↔ P x

/-- Definition 3.5. Two objects agree on the genuine properties. -/
def Agree (x y : Obj) : Prop := ∀ U, Genuine U → (U x ↔ U y)

/-- Definition 3.5. Supervenience on the genuine properties. -/
def Supervenes (P : Obj → Prop) : Prop := ∀ x y, Agree x y → P x → P y

/-- Local qualitative properties: intrinsic qualitative properties that do
not consist in an arrangement of proper parts (Principle P4). -/
axiom LocalQual : (Obj → Prop) → Prop

/-- Principle P1 (Discrimination). Some distinct objects resemble each
other and some do not. -/
axiom p1_discrimination :
  ∃ x y x' y', x ≠ y ∧ x' ≠ y' ∧ Res x y ∧ ¬ Res x' y'

/-- Principle P2 (Structural grounding). Every reshuffle preserves
resemblance. -/
axiom p2_structural :
  ∀ f g, Reshuffle f g → ∀ x y, Res x y ↔ Res (f x) (f y)

/-- Principle P3 (Shared constituent). Objects that resemble each other
share a genuine property. -/
axiom p3_shared : ∀ x y, Res x y → ∃ U, Genuine U ∧ U x ∧ U y

/-- Principle P4 (Completeness). Every local qualitative property
supervenes on the genuine properties. -/
axiom p4_complete : ∀ P, LocalQual P → Supervenes P

/-- Theorem 4.1. There are universals. -/
theorem universals_exist : ∃ U, IsUniversal U := by
  obtain ⟨x, y, _, _, hxy, _, hr, _⟩ := p1_discrimination
  obtain ⟨U, hU, hx, hy⟩ := p3_shared x y hr
  exact ⟨U, hU, x, y, hxy, hx, hy⟩

/-- The transposition of two objects. -/
noncomputable def swap (a b : Obj) (x : Obj) : Obj :=
  if x = a then b else if x = b then a else x

theorem swap_left (a b : Obj) : swap a b a = b := by simp [swap]

theorem swap_right (a b : Obj) : swap a b b = a := by
  unfold swap
  by_cases h : b = a
  · simp [h]
  · simp [h]

theorem swap_other (a b x : Obj) (ha : x ≠ a) (hb : x ≠ b) : swap a b x = x := by
  simp [swap, ha, hb]

theorem swap_invol (a b x : Obj) : swap a b (swap a b x) = x := by
  by_cases ha : x = a
  · subst ha; rw [swap_left, swap_right]
  · by_cases hb : x = b
    · subst hb; rw [swap_right, swap_left]
    · rw [swap_other a b x ha hb, swap_other a b x ha hb]

theorem swap_perm (a b : Obj) : Perm (swap a b) (swap a b) :=
  ⟨swap_invol a b, swap_invol a b⟩

theorem perm_comp (f g f' g' : Obj → Obj) (h : Perm f g) (h' : Perm f' g') :
    Perm (fun x => f' (f x)) (fun x => g (g' x)) := by
  constructor
  · intro x; simp [h'.1, h.1]
  · intro x; simp [h.2, h'.2]

/-- Lemma 4.2 (Two-point homogeneity). Any pair of distinct objects can be
mapped onto any other pair of distinct objects by a permutation. -/
theorem two_point (x y x' y' : Obj) (hxy : x ≠ y) (hxy' : x' ≠ y') :
    ∃ f g, Perm f g ∧ f x = x' ∧ f y = y' := by
  let y1 := swap x x' y
  have hy1 : x' ≠ y1 := by
    intro h
    by_cases hyx' : y = x'
    · have : y1 = x := by
        show swap x x' y = x
        rw [hyx']; exact swap_right x x'
      exact hxy ((this.symm.trans h.symm).trans hyx'.symm)
    · have : y1 = y := swap_other x x' y (Ne.symm hxy) hyx'
      exact hyx' (by rw [h, this])
  refine ⟨fun z => swap y1 y' (swap x x' z), fun z => swap x x' (swap y1 y' z),
    perm_comp _ _ _ _ (swap_perm x x') (swap_perm y1 y'), ?_, ?_⟩
  · show swap y1 y' (swap x x' x) = x'
    rw [swap_left]; exact swap_other y1 y' x' hy1 hxy'
  · show swap y1 y' y1 = y'
    exact swap_left y1 y'

/-- Theorem 4.3 (Ugly duckling, structural form). If every property were
genuine, any two pairs of distinct objects would be alike in respect of
resemblance. -/
theorem ugly_duckling (hall : ∀ U, Genuine U) :
    ∀ x y x' y', x ≠ y → x' ≠ y' → (Res x y ↔ Res x' y') := by
  intro x y x' y' hxy hxy'
  obtain ⟨f, g, hp, hfx, hfy⟩ := two_point x y x' y' hxy hxy'
  have hr : Reshuffle f g := ⟨hp, fun U _ => hall _, fun U _ => hall _⟩
  have := p2_structural f g hr x y
  rw [hfx, hfy] at this
  exact this

/-- Theorem 4.4 (Sparseness). Some pairs of distinct objects are related
by no reshuffle. -/
theorem sparseness :
    ∃ x y x' y', x ≠ y ∧ x' ≠ y' ∧
      ∀ f g, Reshuffle f g → ¬ (f x = x' ∧ f y = y') := by
  obtain ⟨x, y, x', y', hxy, hxy', hr, hnr⟩ := p1_discrimination
  refine ⟨x, y, x', y', hxy, hxy', fun f g hf ⟨hfx, hfy⟩ => hnr ?_⟩
  have := (p2_structural f g hf x y).mp hr
  rw [hfx, hfy] at this
  exact this

/-- Corollary 4.5. Not every property is genuine. -/
theorem not_all_genuine : ∃ U, ¬ Genuine U := by
  apply Classical.byContradiction
  intro h
  have hall : ∀ U, Genuine U := fun U =>
    Classical.byContradiction fun hU => h ⟨U, hU⟩
  obtain ⟨x, y, x', y', hxy, hxy', hr, hnr⟩ := p1_discrimination
  exact hnr ((ugly_duckling hall x y x' y' hxy hxy').mp hr)

/-- Theorem 5.1 (Qualitativeness). Every symmetry preserves every
constructed property. -/
theorem constructions_qualitative (f g : Obj → Obj) (hs : Symmetry f g) :
    ∀ c x, eval c x ↔ eval c (f x) := by
  intro c
  induction c with
  | atom U hU => intro x; exact hs.2.1 U hU x
  | neg c ih => intro x; simp only [eval]; rw [ih x]
  | conj ι k ih => intro x; simp only [eval]; exact forall_congr' fun i => ih i x
  | disj ι k ih => intro x; simp only [eval]; exact exists_congr fun i => ih i x
  | proj R hR c ih =>
    intro x
    simp only [eval]
    constructor
    · intro ⟨y, hxy, hy⟩
      exact ⟨f y, (hs.2.2 R hR x y).mp hxy, (ih y).mp hy⟩
    · intro ⟨y, hxy, hy⟩
      refine ⟨g y, ?_, ?_⟩
      · rw [hs.2.2 R hR x (g y), hs.1.2 y]; exact hxy
      · rw [ih (g y), hs.1.2 y]; exact hy

/-- Corollary 5.2 (Black's world). If a symmetry exchanges two objects, no
constructed property distinguishes them. -/
theorem black_world (a b : Obj) (f g : Obj → Obj) (hs : Symmetry f g)
    (hab : f a = b) : ∀ c, eval c a ↔ eval c b := by
  intro c
  have := constructions_qualitative f g hs c a
  rw [hab] at this
  exact this

/-- Lemma 5.3. Exchanging two objects that agree on the genuine properties
is a monadic symmetry. -/
theorem swap_mono (a b : Obj) (h : Agree a b) : MonoSymmetry (swap a b) (swap a b) := by
  refine ⟨swap_perm a b, fun U hU x => ?_⟩
  by_cases ha : x = a
  · subst ha; rw [swap_left]; exact h U hU
  · by_cases hb : x = b
    · subst hb; rw [swap_right]; exact (h U hU).symm
    · rw [swap_other a b x ha hb]

/-- Proposition 5.4. A property supervenes on the genuine properties if
and only if every monadic symmetry preserves it. -/
theorem supervenes_iff (P : Obj → Prop) :
    Supervenes P ↔ ∀ f g, MonoSymmetry f g → ∀ x, P x ↔ P (f x) := by
  constructor
  · intro hP f g hs x
    have hag : Agree x (f x) := fun U hU => hs.2 U hU x
    have hag' : Agree (f x) x := fun U hU => (hag U hU).symm
    exact ⟨hP x (f x) hag, hP (f x) x hag'⟩
  · intro h x y hag hx
    have := (h (swap x y) (swap x y) (swap_mono x y hag) x).mp hx
    rw [swap_left] at this
    exact this

/-- The literal for a genuine property, chosen to agree with a given
object. -/
noncomputable def literal (y : Obj) (U : {U : Obj → Prop // Genuine U}) : Con :=
  if U.1 y then .atom U.1 U.2 else .neg (.atom U.1 U.2)

theorem eval_literal (y x : Obj) (U : {U : Obj → Prop // Genuine U}) :
    eval (literal y U) x ↔ (U.1 x ↔ U.1 y) := by
  unfold literal
  by_cases h : U.1 y
  · simp [h, eval]
  · simp [h, eval]

/-- Theorem 5.5 (Construction). Every property that supervenes on the
genuine properties is constructed from them, without relational
projection. -/
theorem construction (P : Obj → Prop) (hP : Supervenes P) : Constructed P := by
  refine ⟨.disj {y : Obj // P y}
    (fun y => .conj {U : Obj → Prop // Genuine U} (fun U => literal y.1 U)), ?_⟩
  intro x
  simp only [eval]
  constructor
  · intro ⟨⟨y, hy⟩, hlit⟩
    apply hP y x _ hy
    intro U hU
    exact ((eval_literal y x ⟨U, hU⟩).mp (hlit ⟨U, hU⟩)).symm
  · intro hx
    exact ⟨⟨x, hx⟩, fun U => (eval_literal x x U).mpr Iff.rfl⟩

/-- Theorem 5.6 (The sparse universals theorem). There are universals; not
every property is genuine, and some pairs of distinct objects are related
by no reshuffle; and every local qualitative property is constructed from
the genuine properties. -/
theorem sparse_universals_theorem :
    (∃ U, IsUniversal U) ∧
    (∃ U, ¬ Genuine U) ∧
    (∃ x y x' y', x ≠ y ∧ x' ≠ y' ∧
      ∀ f g, Reshuffle f g → ¬ (f x = x' ∧ f y = y')) ∧
    (∀ P, LocalQual P → Constructed P) :=
  ⟨universals_exist, not_all_genuine, sparseness,
    fun P hP => construction P (p4_complete P hP)⟩

end Philosophy.MET_02

#print axioms Philosophy.MET_02.sparse_universals_theorem
#print axioms Philosophy.MET_02.constructions_qualitative
#print axioms Philosophy.MET_02.supervenes_iff
