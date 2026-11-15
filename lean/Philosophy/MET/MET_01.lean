/-
MET-01 · Why There Is Something Rather Than Nothing
Formalization of Volume I, Chapter 4: Proposition 4.2, Proposition 4.3,
Theorem 4.4 and Corollary 4.5.

A combinatorial space of worlds over n potential concrete objects is the
list of all assignments of existence or non-existence to each object
(Definition 4.1). The empty world is the assignment on which no object
exists. Under the indifference measure (Principle P2), each world has
measure 1/2^n.

What this file establishes. The space has 2^n worlds, of which exactly one
is empty, and for every k ≥ 1 the measure of the empty world is below 1/k
once n ≥ k: as the number of potential objects grows without bound, the
measure of the empty world tends to zero. It does not establish the
principles of plenitude and indifference (P1, P2), which are defended in
Chapters 3 and 6, nor that a world of measure zero is not actual, which is
the subject of Chapter 7.
-/

namespace Philosophy.MET_01

/-- A world over n potential objects: which of them exist. -/
abbrev World := List Bool

/-- Definition 4.1. The combinatorial space of worlds over n potential objects. -/
def worlds : Nat → List World
  | 0 => [[]]
  | n + 1 => (worlds n).map (true :: ·) ++ (worlds n).map (false :: ·)

/-- The empty world: no potential object exists. -/
def empty (w : World) : Bool := w.all (fun b => !b)

/-- Proposition 4.2. There are 2^n worlds over n potential objects. -/
theorem card (n : Nat) : (worlds n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [worlds, ih, Nat.pow_succ, Nat.mul_two]

/-- Number of empty worlds in a list of worlds. -/
def countEmpty : List World → Nat
  | [] => 0
  | w :: ws => (if empty w then 1 else 0) + countEmpty ws

theorem countEmpty_append (xs ys : List World) :
    countEmpty (xs ++ ys) = countEmpty xs + countEmpty ys := by
  induction xs with
  | nil => simp [countEmpty]
  | cons x xs ih => simp [countEmpty, ih, Nat.add_assoc]

theorem countEmpty_true (xs : List World) : countEmpty (xs.map (true :: ·)) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [countEmpty, empty, ih] at *

theorem countEmpty_false (xs : List World) :
    countEmpty (xs.map (false :: ·)) = countEmpty xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [countEmpty, empty, ih] at *

/-- Proposition 4.3. Exactly one world over n potential objects is empty. -/
theorem unique_empty (n : Nat) : countEmpty (worlds n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [worlds, countEmpty_append, countEmpty_true, countEmpty_false, ih]

theorem lt_two_pow_self (k : Nat) : k < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

/-- Theorem 4.4. For every k ≥ 1, once there are at least k potential objects,
the measure of the empty world, 1/2^n, is less than 1/k. -/
theorem vanishing (k n : Nat) (hn : k ≤ n) : k < 2 ^ n :=
  Nat.lt_of_lt_of_le (lt_two_pow_self k) (Nat.pow_le_pow_right (by decide) hn)

/-- Corollary 4.5. Under the same condition, the measure of the worlds in which
something exists, (2^n - 1)/2^n, exceeds (k - 1)/k. -/
theorem something (k n : Nat) (hk : 1 ≤ k) (hn : k ≤ n) :
    (k - 1) * 2 ^ n < k * (2 ^ n - 1) := by
  have h := vanishing k n hn
  have e1 : (k - 1) * 2 ^ n = k * 2 ^ n - 2 ^ n := by
    rw [Nat.mul_sub_right_distrib, Nat.one_mul]
  have e2 : k * (2 ^ n - 1) = k * 2 ^ n - k := by
    rw [Nat.mul_sub_one]
  rw [e1, e2]
  have : 2 ^ n ≤ k * 2 ^ n := Nat.le_mul_of_pos_left _ hk
  omega

end Philosophy.MET_01

#print axioms Philosophy.MET_01.unique_empty
#print axioms Philosophy.MET_01.vanishing
#print axioms Philosophy.MET_01.something
