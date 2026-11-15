/-
REL-10 · Fine-Tuning and the Normalizability Problem
Formalization of Theorem 3.1 and Proposition 3.4 (discrete versions).

A discrete parameter space: the possible values of a constant are indexed
by the natural numbers (for instance, unit intervals of an unbounded range).
A weighting assigns to each value a weight, in units of `1/D` for an
arbitrary denominator `D`, so that natural-number weights represent all
rational weights. `psum f k` is the total weight of the first `k` values.

What this file establishes. (1) No uniform weighting is normalizable: if all
values receive the same weight `c`, the partial sums are all zero (`c = 0`)
or exceed every bound (`c > 0`), so the total is 0 or unbounded and never
equal to a positive normalizing constant (Theorem 3.1). (2) Normalizable
weightings exist that give a bounded region any probability whatever
(Proposition 3.4).

What it does not establish. The continuous case (Corollary 3.2), which
follows by partitioning the range into unit intervals; or that no physical
theory will supply a privileged measure (Section 6 of the manuscript).
-/

namespace Philosophy.REL_10

/-- Total weight of the first `k` values. -/
def psum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => psum f k + f k

/-- Partial sums of a constant weighting. -/
theorem psum_const (c k : Nat) : psum (fun _ => c) k = k * c := by
  induction k with
  | zero => simp [psum]
  | succ k ih => simp [psum, ih, Nat.succ_mul]

/-- Theorem 3.1 (no uniform probability on a countable space). A weighting
that gives every value the same weight has partial sums that are all zero
or that exceed every bound. -/
theorem no_uniform (f : Nat → Nat) (c : Nat) (hf : ∀ n, f n = c) :
    (∀ k, psum f k = 0) ∨ (∀ B, ∃ k, B < psum f k) := by
  have hfc : f = fun _ => c := funext hf
  subst hfc
  cases c with
  | zero => exact Or.inl fun k => by rw [psum_const]; simp
  | succ c =>
    refine Or.inr fun B => ⟨B + 1, ?_⟩
    rw [psum_const, Nat.mul_succ]
    omega

/-- Theorem 3.1, normalization form. For a positive normalizing constant
`N`, no uniform weighting has partial sums bounded by `N` that also reach
`N`. -/
theorem not_normalizable (f : Nat → Nat) (c N : Nat) (hf : ∀ n, f n = c)
    (hN : 0 < N) : ¬ ((∀ k, psum f k ≤ N) ∧ (∃ k, psum f k = N)) := by
  intro ⟨hb, k, hk⟩
  rcases no_uniform f c hf with h0 | hu
  · rw [h0 k] at hk; omega
  · obtain ⟨j, hj⟩ := hu N
    have := hb j
    omega

/-- A weighting concentrated on two points: weight `v` on value 0 and
`N - v` on value `r`. -/
def twoPoint (v N r : Nat) (n : Nat) : Nat :=
  if n = 0 then v else if n = r then N - v else 0

theorem twoPoint_prefix (v N r : Nat) (_hr : 0 < r) :
    ∀ k, 0 < k → k ≤ r → psum (twoPoint v N r) k = v := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro _ hk
    cases k with
    | zero => simp [psum, twoPoint]
    | succ k =>
      have h1 : psum (twoPoint v N r) (k + 1) = v := ih (by omega) (by omega)
      have hne0 : k + 1 ≠ 0 := by omega
      have hner : k + 1 ≠ r := by omega
      have h2 : twoPoint v N r (k + 1) = 0 := by
        simp [twoPoint, hne0, hner]
      show psum (twoPoint v N r) (k + 1) + twoPoint v N r (k + 1) = v
      rw [h1, h2, Nat.add_zero]

theorem twoPoint_tail (v N r : Nat) (hr : 0 < r) (hv : v ≤ N) :
    ∀ k, r < k → psum (twoPoint v N r) k = N := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hk
    by_cases hkr : k = r
    · subst hkr
      have h1 := twoPoint_prefix v N k hr k hr (Nat.le_refl k)
      have hne0 : k ≠ 0 := by omega
      have h2 : twoPoint v N k k = N - v := by
        simp [twoPoint, hne0]
      show psum (twoPoint v N k) k + twoPoint v N k k = N
      rw [h1, h2]; omega
    · have h1 := ih (by omega)
      have hne0 : k ≠ 0 := by omega
      have h2 : twoPoint v N r k = 0 := by
        simp [twoPoint, hne0, hkr]
      show psum (twoPoint v N r) k + twoPoint v N r k = N
      rw [h1, h2, Nat.add_zero]

/-- Proposition 3.4 (no privileged normalizable measure). For a bounded
region of `r ≥ 1` values and any target `v ≤ N`, there is a normalizable
weighting (total `N`) that gives the region weight exactly `v`. -/
theorem arbitrary_probability (r v N : Nat) (hr : 0 < r) (hv : v ≤ N) :
    ∃ f : Nat → Nat, psum f r = v ∧ ∀ k, r < k → psum f k = N :=
  ⟨twoPoint v N r, twoPoint_prefix v N r hr r hr (Nat.le_refl r),
    twoPoint_tail v N r hr hv⟩

end Philosophy.REL_10

#print axioms Philosophy.REL_10.no_uniform
#print axioms Philosophy.REL_10.not_normalizable
#print axioms Philosophy.REL_10.arbitrary_probability
