/-
ETH-09 · The Repugnant Conclusion Is Not Repugnant
Formalization of the arithmetic of Sections 3 and 4.

A population is represented by a list of groups, each a pair (number of
people, welfare level), with levels measured on a ratio scale whose zero is
a life neither worth living nor not worth living (Definition 2.1). Only
populations of lives worth living (positive levels) are at issue. The value
of a population on the total view is the sum over groups of number times
level (Definition 2.3).

What this file establishes.
(1) On the total view, a uniform population of m lives at level z is better
    than one of n lives at level a iff m * z > n * a (Proposition 3.1), and
    for every n, a and every z > 0 there is such an m (Theorem 3.2).
(2) Mere addition and benign addition increase total value (Lemma 3.3).
(3) From three premises about an abstract relation "at least as good as",
    stated as axioms (transitivity, Assumption 2.4; the mere addition
    principle, Assumption 2.5; non-anti-egalitarianism, Assumption 2.6),
    the repugnant conclusion follows in a single mere-addition step
    (Theorem 4.2, using Lemma 4.1), without assuming the total view.
(4) The total view satisfies the three premises, so they are jointly
    consistent (Proposition 4.3).

What it does not establish. It does not establish any of the three
premises, nor that the total view is correct, nor the manuscript's main
claim that a life barely worth living, correctly characterized, is a life
whose multiplication in large numbers is not repugnant (Section 6). Nor
does it represent the plural components of the value of a life (ETH-01):
a level is the net contribution of a life across components.
-/

namespace Philosophy.ETH_09

/-- Definition 2.1. A population: a list of groups (number of people, level). -/
abbrev Pop := List (Nat × Nat)

/-- Definition 2.2. The uniform population of `n` lives at level `a`. -/
def uniform (n a : Nat) : Pop := [(n, a)]

/-- The number of people in a population. -/
def size : Pop → Nat
  | [] => 0
  | g :: p => g.1 + size p

/-- Definition 2.3. Total value: the sum over groups of number times level. -/
def total : Pop → Nat
  | [] => 0
  | g :: p => g.1 * g.2 + total p

theorem total_append (p q : Pop) : total (p ++ q) = total p + total q := by
  induction p with
  | nil => simp [total]
  | cons g p ih => simp [total, ih]; omega

theorem size_append (p q : Pop) : size (p ++ q) = size p + size q := by
  induction p with
  | nil => simp [size]
  | cons g p ih => simp [size, ih]; omega

/-- The total view's ordering (Definition 2.3). -/
def TotalBetter (p q : Pop) : Prop := total q < total p

/-- Proposition 3.1. On the total view, Z (m lives at z) is better than
A (n lives at a) iff m * z > n * a. -/
theorem total_comparison (n a m z : Nat) :
    TotalBetter (uniform m z) (uniform n a) ↔ n * a < m * z := by
  simp [TotalBetter, uniform, total]

/-- Theorem 3.2 (the repugnant conclusion on the total view). For every
population of n lives at level a and every positive level z, some
population of lives at level z is better. -/
theorem repugnant_total (n a z : Nat) (hz : 0 < z) :
    ∃ m, TotalBetter (uniform m z) (uniform n a) := by
  refine ⟨n * a + 1, ?_⟩
  rw [total_comparison]
  have h : (n * a + 1) * 1 ≤ (n * a + 1) * z := Nat.mul_le_mul_left _ hz
  omega

/-- Lemma 3.3 (i), mere addition. Adding k lives at a positive level w
does not lower, and if k > 0 raises, total value. -/
theorem mere_addition_total (p : Pop) (k w : Nat) (hk : 0 < k) (hw : 0 < w) :
    TotalBetter (p ++ [(k, w)]) p := by
  unfold TotalBetter
  rw [total_append]
  have h : 1 * 1 ≤ k * w := Nat.mul_le_mul hk hw
  simp [total]
  omega

/-- Lemma 3.3 (ii), benign addition. Raising n lives from a to a' ≥ a and
adding k > 0 lives at a positive level w raises total value. -/
theorem benign_addition_total (n a a' k w : Nat) (ha : a ≤ a')
    (hk : 0 < k) (hw : 0 < w) :
    TotalBetter (uniform n a' ++ [(k, w)]) (uniform n a) := by
  unfold TotalBetter
  rw [total_append]
  have h1 : n * a ≤ n * a' := Nat.mul_le_mul_left _ ha
  have h2 : 1 * 1 ≤ k * w := Nat.mul_le_mul hk hw
  simp [uniform, total]
  omega

/-! ## The mere addition argument from abstract premises (Section 4) -/

/-- Primitive. `Geq p q`: population p is at least as good as population q. -/
axiom Geq : Pop → Pop → Prop

/-- Strict betterness, defined from `Geq` (Section 2, before Assumption 2.4). -/
def Better (p q : Pop) : Prop := Geq p q ∧ ¬ Geq q p

/-- Assumption 2.4 (transitivity). -/
axiom geq_trans : ∀ p q r, Geq p q → Geq q r → Geq p r

/-- Assumption 2.5 (mere addition principle). Adding lives worth living,
without affecting anyone else, does not make a population worse. -/
axiom mere_addition : ∀ p k w, 0 < w → Geq (p ++ [(k, w)]) p

/-- Assumption 2.6 (non-anti-egalitarianism). A perfectly equal population
of the same size with greater total value is better. -/
axiom non_anti_egalitarianism :
    ∀ p c, total p < size p * c → Better (uniform (size p) c) p

/-- Lemma 4.1. Better then at-least-as-good gives better (uses Assumption 2.4). -/
theorem better_of_better_geq (p q r : Pop) (h1 : Better p q) (h2 : Geq q r) :
    Better p r := by
  refine ⟨geq_trans p q r h1.1 h2, fun h => h1.2 (geq_trans q r p h2 h)⟩

/-- Theorem 4.2 (the repugnant conclusion from Assumptions 2.4–2.6). For
every n and a and every level z ≥ 2, some population of lives at level z
is better than n lives at level a. The witness adds k = n * a + 1 lives at
level z - 1 to A and then equalizes at level z. -/
theorem repugnant_conclusion (n a z : Nat) (hz : 2 ≤ z) :
    ∃ m, Better (uniform m z) (uniform n a) := by
  let k := n * a + 1
  let aplus : Pop := uniform n a ++ [(k, z - 1)]
  have hsize : size aplus = n + k := by
    simp [aplus, size_append, uniform, size]
  have htot : total aplus < size aplus * z := by
    rw [hsize, Nat.add_mul]
    simp only [aplus, total_append, uniform, total]
    have e : k * z = k * (z - 1) + k := by
      have : z = (z - 1) + 1 := by omega
      conv => lhs; rw [this]
      rw [Nat.mul_add, Nat.mul_one]
    have hnz : 0 ≤ n * z := Nat.zero_le _
    omega
  have hb := non_anti_egalitarianism aplus z htot
  rw [hsize] at hb
  have hm : Geq aplus (uniform n a) := mere_addition (uniform n a) k (z - 1) (by omega)
  exact ⟨n + k, better_of_better_geq _ _ _ hb hm⟩

/-- Proposition 4.3. The total view's weak ordering satisfies the three
premises, which are therefore jointly consistent. -/
theorem total_satisfies_premises :
    (∀ p q r : Pop, total q ≤ total p → total r ≤ total q → total r ≤ total p) ∧
    (∀ (p : Pop) k w, 0 < w → total p ≤ total (p ++ [(k, w)])) ∧
    (∀ (p : Pop) c, total p < size p * c →
        total p ≤ total (uniform (size p) c) ∧ ¬ total (uniform (size p) c) ≤ total p) := by
  refine ⟨fun _ _ _ h1 h2 => Nat.le_trans h2 h1, ?_, ?_⟩
  · intro p k w _
    rw [total_append]; omega
  · intro p c h
    simp [uniform, total]
    omega

end Philosophy.ETH_09

#print axioms Philosophy.ETH_09.repugnant_total
#print axioms Philosophy.ETH_09.repugnant_conclusion
#print axioms Philosophy.ETH_09.total_satisfies_premises
