/-
LNG-12 · The Sorites and Sharp Boundaries
Formalization of Lemma 3.1, Theorems 3.2 and 3.3, Corollary 3.4 and
Theorem 3.5.

A pattern of use of the word "heap" determines a classical extension: under
each pattern, each number of grains is a heap or is not (Definition 2.1,
Assumption 2.2). Under every pattern that could be ours, one grain is not a
heap and ten thousand grains are (Assumption 2.3), and adding a grain to a
heap leaves a heap (Assumption 2.4). Patterns of use are related by
closeness (Definition 2.6). Metalinguistic knowledge is safe belief: a
speaker whose use is `u` knows a claim about the extension of "heap" only if
the claim holds under every pattern close to `u` (Definition 2.7). Semantic
plasticity says that a boundary is never robust under close patterns of use
(Assumption 2.8).

What this file establishes. Under every pattern of use there is exactly one
number of grains that is not a heap while one more grain is (Lemma 3.1,
Theorem 3.2); the tolerance premise of the sorites is false
(Theorem 3.3). The speaker knows that "heap" has a sharp boundary
(Corollary 3.4), and of no number does she know that the boundary lies
there (Theorem 3.5).

What it does not establish. It does not establish that use determines a
classical extension, nor semantic plasticity, nor that knowledge is safe
belief; these are the assumptions defended in the manuscript and in MET-18,
whose module treats knowledge of first-order cases by a margin for error.
-/

namespace Philosophy.LNG_12

/-- Definition 2.1. Patterns of use of "heap". -/
axiom Use : Type

/-- Definition 2.1 and Assumption 2.2. The classical extension of "heap"
under a pattern of use: `Heap u n` says that `n` grains form a heap. -/
axiom Heap : Use → Nat → Prop

/-- Assumption 2.3 (clear cases). One grain is not a heap. -/
axiom one_not_heap : ∀ u, ¬ Heap u 1

/-- Assumption 2.3 (clear cases). Ten thousand grains are a heap. -/
axiom ten_thousand_heap : ∀ u, Heap u 10000

/-- Assumption 2.4 (monotonicity). Adding a grain to a heap leaves a heap. -/
axiom monotone : ∀ u n, Heap u n → Heap u (n + 1)

/-- Definition 2.5. `n` is the boundary under `u`: `n` grains are not a heap
and `n + 1` grains are. -/
def Boundary (u : Use) (n : Nat) : Prop := ¬ Heap u n ∧ Heap u (n + 1)

/-- Definition 2.6. Closeness of patterns of use. -/
axiom Close : Use → Use → Prop

/-- Definition 2.6. Every pattern is close to itself. -/
axiom close_refl : ∀ u, Close u u

/-- Definition 2.7. Metalinguistic knowledge as safe belief. -/
def Knows (u : Use) (φ : Use → Prop) : Prop := ∀ v, Close u v → φ v

/-- Assumption 2.8 (semantic plasticity). For every pattern of use and every
number at which it draws the boundary, some close pattern does not draw it
there. -/
axiom plasticity : ∀ u n, Boundary u n → ∃ v, Close u v ∧ ¬ Boundary v n

/-- Lemma 3.1. A predicate of numbers that fails at `a` and holds at a later
number has a last failure followed by a success. -/
theorem last_failure (P : Nat → Prop) (a : Nat) (ha : ¬ P a) :
    ∀ k, P (a + k) → ∃ n, ¬ P n ∧ P (n + 1)
  | 0, h => absurd h ha
  | k + 1, h => by
    by_cases hk : P (a + k)
    · exact last_failure P a ha k hk
    · exact ⟨a + k, hk, h⟩

theorem heap_le (u : Use) (n : Nat) (h : Heap u n) : ∀ k, Heap u (n + k)
  | 0 => h
  | k + 1 => monotone u (n + k) (heap_le u n h k)

/-- Theorem 3.2 (sharp boundary). Under every pattern of use there is
exactly one boundary. -/
theorem sharp (u : Use) :
    (∃ n, Boundary u n) ∧ ∀ n m, Boundary u n → Boundary u m → n = m := by
  refine ⟨last_failure (Heap u) 1 (one_not_heap u) 9999 (ten_thousand_heap u), ?_⟩
  intro n m ⟨hn, hn1⟩ ⟨hm, hm1⟩
  apply Classical.byContradiction
  intro hne
  cases Nat.lt_or_gt_of_ne hne with
  | inl hlt =>
    have := heap_le u (n + 1) hn1 (m - (n + 1))
    rw [Nat.add_sub_cancel' hlt] at this
    exact hm this
  | inr hgt =>
    have := heap_le u (m + 1) hm1 (n - (m + 1))
    rw [Nat.add_sub_cancel' hgt] at this
    exact hn this

/-- Theorem 3.3. The tolerance premise of the sorites is false under every
pattern of use: it is not the case that removing a grain from a heap always
leaves a heap. -/
theorem tolerance_false (u : Use) : ¬ ∀ n, Heap u (n + 1) → Heap u n := by
  intro htol
  have ⟨n, hn, hn1⟩ := (sharp u).1
  exact hn (htol n hn1)

/-- Corollary 3.4. The speaker knows that "heap" has a sharp boundary. -/
theorem knows_sharp (u : Use) : Knows u (fun v => ∃ n, Boundary v n) :=
  fun v _ => (sharp v).1

/-- Theorem 3.5 (unknowability). Of no number does the speaker know that the
boundary of "heap" lies there. -/
theorem unknowable (u : Use) (n : Nat) : ¬ Knows u (fun v => Boundary v n) := by
  intro hk
  have ⟨v, hv, hnot⟩ := plasticity u n (hk u (close_refl u))
  exact hnot (hk v hv)

end Philosophy.LNG_12

#print axioms Philosophy.LNG_12.sharp
#print axioms Philosophy.LNG_12.unknowable
