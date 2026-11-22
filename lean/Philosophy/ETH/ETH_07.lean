/-
ETH-07 · Moral Status and the Capacity for Welfare
Formalization of Lemma 3.1, Theorem 3.2, Proposition 3.3, Theorem 3.4,
Proposition 3.5, Corollary 3.6 and Proposition 5.2.

Beings form a primitive type. Sentience (Definition 2.2) and being a
subject of welfare (Definition 2.3) are primitive predicates. The capacity
for welfare (Definition 2.4) and the degree of moral status (Definition 2.1)
are primitive functions to the natural numbers; a being has moral status
when its degree is positive. Capacities are thereby assumed to be totally
ordered, a simplification discussed in Section 9 of the manuscript.

What this file establishes. Given the interest principle (Principle P1), the
experiential requirement (Assumption 2.5) and the sufficiency of valence
(Assumption 2.6), sentience is necessary and sufficient for moral status
(Theorem 3.2). Given supervenience and monotonicity (Principles P2 and P3),
status varies with capacity (Proposition 3.3). Any two admissible
assignments of degrees (Definition 2.7) order beings identically
(Theorem 3.4); this uses no substantive axiom. The capacity assignment is
admissible (Proposition 3.5), and so is the hierarchical assignment
capacity squared (Proposition 5.2), so the principles fix the order of
status but not its cardinal shape.

What it does not establish. It does not establish the premises, which are
argued for in Sections 2 and 4. It does not formalize the argument of
Section 5 that hierarchical assignments double-count capacity, nor any claim
about which beings are sentient.
-/

namespace Philosophy.ETH_07

/-- Beings. -/
axiom Being : Type

/-- Definition 2.2. Sentience: the capacity for valenced experience. -/
axiom Sentient : Being → Prop

/-- Definition 2.3. Being a subject of welfare. -/
axiom WelfareSubject : Being → Prop

/-- Definition 2.4. Capacity for welfare, represented ordinally. -/
axiom capacity : Being → Nat

/-- Definition 2.4 (second clause). Capacity is positive exactly for
subjects of welfare. -/
axiom capacity_pos : ∀ x, capacity x > 0 ↔ WelfareSubject x

/-- Definition 2.1. Degree of moral status; `status x > 0` means that `x`
has moral status. -/
axiom status : Being → Nat

/-- Principle P1 (interest principle). A being has moral status if and only
if it is a subject of welfare. -/
axiom interest_principle : ∀ x, status x > 0 ↔ WelfareSubject x

/-- Assumption 2.5 (experiential requirement). Every subject of welfare is
sentient. -/
axiom experiential : ∀ x, WelfareSubject x → Sentient x

/-- Assumption 2.6 (sufficiency of valence). Every sentient being is a
subject of welfare. -/
axiom valence_suffices : ∀ x, Sentient x → WelfareSubject x

/-- Principle P2 (supervenience). Equal capacity, equal status. -/
axiom supervenience : ∀ x y, capacity x = capacity y → status x = status y

/-- Principle P3 (monotonicity). Greater capacity, greater status. -/
axiom monotonicity : ∀ x y, capacity x < capacity y → status x < status y

/-- Definition 2.7. An admissible assignment of degrees of status. -/
def Admissible (s : Being → Nat) : Prop :=
  (∀ x, s x > 0 ↔ WelfareSubject x) ∧
  (∀ x y, capacity x = capacity y → s x = s y) ∧
  (∀ x y, capacity x < capacity y → s x < s y)

/-- Lemma 3.1. A being is a subject of welfare iff it is sentient. -/
theorem welfare_iff_sentient (x : Being) : WelfareSubject x ↔ Sentient x :=
  ⟨experiential x, valence_suffices x⟩

/-- Theorem 3.2 (threshold). Sentience is necessary and sufficient for
moral status. -/
theorem threshold (x : Being) : status x > 0 ↔ Sentient x :=
  (interest_principle x).trans (welfare_iff_sentient x)

/-- Proposition 3.3 (variation). Status varies with capacity; a sentient
being has more status than a non-sentient one. -/
theorem variation (x y : Being) :
    (capacity x < capacity y → status x < status y) ∧
    (capacity x = capacity y → status x = status y) ∧
    (Sentient x → ¬ Sentient y → status y < status x) := by
  refine ⟨monotonicity x y, supervenience x y, fun hx hy => ?_⟩
  have h1 := (threshold x).mpr hx
  have h2 : ¬ status y > 0 := fun h => hy ((threshold y).mp h)
  omega

/-- The actual degrees of status form an admissible assignment
(Principles P1 to P3). -/
theorem status_admissible : Admissible status :=
  ⟨interest_principle, supervenience, monotonicity⟩

/-- Theorem 3.4 (ordinal uniqueness). Any two admissible assignments order
beings identically. -/
theorem ordinal_uniqueness (s t : Being → Nat)
    (hs : Admissible s) (ht : Admissible t) (x y : Being) :
    s x ≤ s y ↔ t x ≤ t y := by
  obtain ⟨_, hs2, hs3⟩ := hs
  obtain ⟨_, ht2, ht3⟩ := ht
  rcases Nat.lt_trichotomy (capacity x) (capacity y) with h | h | h
  · have a := hs3 x y h
    have b := ht3 x y h
    omega
  · have a := hs2 x y h
    have b := ht2 x y h
    omega
  · have a := hs3 y x h
    have b := ht3 y x h
    omega

/-- Proposition 3.5 (consistency). The capacity assignment is admissible. -/
theorem capacity_admissible : Admissible capacity :=
  ⟨capacity_pos, fun _ _ h => h, fun _ _ h => h⟩

/-- Species, as labels. -/
axiom species : Being → Nat

/-- Corollary 3.6 (irrelevance of species). Beings of different species
with the same capacity have the same status on every admissible
assignment. -/
theorem species_irrelevant (s : Being → Nat) (hs : Admissible s)
    (x y : Being) (_ : species x ≠ species y)
    (h : capacity x = capacity y) : s x = s y :=
  hs.2.1 x y h

/-- Proposition 5.2 (hierarchy is admissible). The assignment capacity
squared satisfies Principles P1 to P3. -/
theorem hierarchy_admissible :
    Admissible (fun x => capacity x * capacity x) := by
  refine ⟨fun x => ?_, fun x y h => by simp [h], fun x y h => ?_⟩
  · constructor
    · intro h
      apply (capacity_pos x).mp
      exact Nat.pos_of_ne_zero (fun h0 => by simp [h0] at h)
    · intro h
      have hc := (capacity_pos x).mpr h
      exact Nat.mul_pos hc hc
  · show capacity x * capacity x < capacity y * capacity y
    have h1 : capacity x * capacity x ≤ capacity x * capacity y :=
      Nat.mul_le_mul_left _ (Nat.le_of_lt h)
    have h2 : capacity x * capacity y < capacity y * capacity y :=
      Nat.mul_lt_mul_of_pos_right h (by omega)
    omega

end Philosophy.ETH_07

#print axioms Philosophy.ETH_07.threshold
#print axioms Philosophy.ETH_07.variation
#print axioms Philosophy.ETH_07.ordinal_uniqueness
#print axioms Philosophy.ETH_07.capacity_admissible
#print axioms Philosophy.ETH_07.species_irrelevant
#print axioms Philosophy.ETH_07.hierarchy_admissible
