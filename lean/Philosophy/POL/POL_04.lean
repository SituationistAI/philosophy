/-
POL-04 · Democracy, Doubly Justified
Formalization of Definitions 3.1 and 3.2, Proposition 4.1, Proposition 4.2
and Theorem 4.4.

Part 1 (arithmetical). The Condorcet jury theorem for three voters. Each
voter is independently correct with probability p = a / (a + c), where the
natural numbers a and c are the weights of a correct and an incorrect vote.
The weight of a voting profile is the product of the weights of its votes,
and the total weight of all eight profiles is (a + c)^3. Majority accuracy
is the total weight of the profiles in which a majority is correct, divided
by (a + c)^3; individual accuracy, rescaled to the same denominator, is
a * (a + c)^2. Clearing the common denominator turns the comparison of
probabilities into an inequality between natural numbers.

Part 2 (logical skeleton). The main theorem: neither the intrinsic nor the
instrumental justification suffices alone, and democracy is justified by the
two together. The philosophical premises are axioms.

What this file establishes. For three independent voters of equal
competence, majority rule is more accurate than a single voter when
competence exceeds one half, and less accurate when it falls below one half
(Proposition 4.1 and Proposition 4.2). Given Assumptions 3.3 to 3.6, the
main theorem follows. It does not establish the jury theorem for larger
electorates, the independence of voters, or any of the assumptions of
Part 2.
-/

namespace Philosophy.POL_04

/-! ## Part 1: the jury theorem for three voters -/

/-- Definition 3.1. Weight of one vote: `a` if correct, `c` if not. -/
def w (a c : Nat) (v : Bool) : Nat := if v then a else c

/-- Definition 3.1. Simple majority of three votes. -/
def maj (x y z : Bool) : Bool := (x && y) || (x && z) || (y && z)

/-- Definition 3.1. Weight of a profile in which the majority is correct
(zero otherwise). -/
def majW (a c : Nat) (x y z : Bool) : Nat :=
  if maj x y z then w a c x * w a c y * w a c z else 0

/-- Definition 3.2. Majority accuracy, scaled by (a + c)^3: the summed
weight of the eight profiles with a correct majority. -/
def majorityAccuracy (a c : Nat) : Nat :=
  majW a c true true true + majW a c true true false +
  majW a c true false true + majW a c false true true +
  majW a c true false false + majW a c false true false +
  majW a c false false true + majW a c false false false

/-- Definition 3.2. Individual accuracy, scaled by (a + c)^3. -/
def individualAccuracy (a c : Nat) : Nat := a * (a + c) * (a + c)

/-- Majority accuracy in closed form: a^3 + 3 a^2 c. -/
theorem majorityAccuracy_eq (a c : Nat) :
    majorityAccuracy a c = a * a * a + 3 * (a * a * c) := by
  simp [majorityAccuracy, majW, maj, w]
  have e1 : a * c * a = a * a * c := Nat.mul_right_comm a c a
  have e2 : c * a * a = a * a * c := by
    rw [Nat.mul_comm c a, Nat.mul_right_comm a c a]
  omega

/-- Individual accuracy expanded: a^3 + 2 a^2 c + a c^2. -/
theorem individualAccuracy_eq (a c : Nat) :
    individualAccuracy a c = a * a * a + 2 * (a * a * c) + a * c * c := by
  simp only [individualAccuracy, Nat.mul_add, Nat.add_mul]
  have e1 : a * c * a = a * a * c := Nat.mul_right_comm a c a
  omega

/-- Proposition 4.1 (Condorcet, n = 3). If competence exceeds one half
(c < a) and is less than one (0 < c), the majority of three is more
accurate than a single voter. -/
theorem condorcet_three (a c : Nat) (hc : 0 < c) (hca : c < a) :
    individualAccuracy a c < majorityAccuracy a c := by
  rw [majorityAccuracy_eq, individualAccuracy_eq]
  have hac : 0 < a * c := Nat.mul_pos (Nat.lt_trans hc hca) hc
  have h : a * c * c < a * c * a := Nat.mul_lt_mul_of_pos_left hca hac
  have e : a * c * a = a * a * c := by rw [Nat.mul_right_comm]
  omega

/-- Proposition 4.2 (the reverse jury theorem, n = 3). If competence is
below one half (a < c) and positive (0 < a), the majority of three is less
accurate than a single voter. -/
theorem condorcet_three_reverse (a c : Nat) (ha : 0 < a) (hac : a < c) :
    majorityAccuracy a c < individualAccuracy a c := by
  rw [majorityAccuracy_eq, individualAccuracy_eq]
  have hpos : 0 < a * c := Nat.mul_pos ha (Nat.lt_trans ha hac)
  have h : a * c * a < a * c * c := Nat.mul_lt_mul_of_pos_left hac hpos
  have e : a * c * a = a * a * c := Nat.mul_right_comm a c a
  omega

/-! ## Part 2: the logical skeleton of the main theorem -/

/-- Decision procedures. -/
axiom Procedure : Type

/-- The procedure realizes equal standing (the intrinsic consideration). -/
axiom Egalitarian : Procedure → Prop

/-- The procedure reliably tends to good outcomes (the instrumental
consideration). -/
axiom Reliable : Procedure → Prop

/-- The procedure is justified. -/
axiom Justified : Procedure → Prop

/-- Democracy, the fair lottery, and benevolent epistocracy. -/
axiom democracy : Procedure
axiom lottery : Procedure
axiom epistocracy : Procedure

/-- Assumption 3.3. The fair lottery among proposals realizes equal
standing but is not justified. -/
axiom assumption_3_3 : Egalitarian lottery ∧ ¬ Justified lottery

/-- Assumption 3.4. A reliable epistocracy is possible and is not
justified. -/
axiom assumption_3_4 : Reliable epistocracy ∧ ¬ Justified epistocracy

/-- Assumption 3.5. Under the competence conditions of Proposition 4.1,
democracy is both egalitarian and reliable. -/
axiom assumption_3_5 : Egalitarian democracy ∧ Reliable democracy

/-- Assumption 3.6. A procedure that is both egalitarian and reliable is
justified. -/
axiom assumption_3_6 : ∀ p, Egalitarian p → Reliable p → Justified p

/-- Theorem 4.4 (main result). Neither consideration suffices alone, and
democracy is justified by the two together. -/
theorem doubly_justified :
    ¬ (∀ p, Egalitarian p → Justified p) ∧
    ¬ (∀ p, Reliable p → Justified p) ∧
    Justified democracy :=
  ⟨fun h => assumption_3_3.2 (h lottery assumption_3_3.1),
   fun h => assumption_3_4.2 (h epistocracy assumption_3_4.1),
   assumption_3_6 democracy assumption_3_5.1 assumption_3_5.2⟩

end Philosophy.POL_04

#print axioms Philosophy.POL_04.condorcet_three
#print axioms Philosophy.POL_04.condorcet_three_reverse
#print axioms Philosophy.POL_04.doubly_justified
