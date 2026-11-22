/-
EPI-10 · The Preface Paradox and the Present Collection
Formalization of Propositions 2.2 and 2.3.

A model of the preface: n claims and n + 1 equally weighted worlds,
numbered 0, …, n. Claim i (for i < n) is false in world i and true
elsewhere; in world n every claim is true. The preface proposition, "at
least one claim is false", is true exactly in the worlds below n.

What this file establishes. Each of the n claims, and the preface
proposition, is true in exactly n of the n + 1 worlds, so all n + 1
propositions reach the Lockean threshold n/(n + 1); yet no world makes all
of them true. With n = 722 the threshold is 722/723. It does not establish
that rational belief is Lockean, which the manuscript discusses.
-/

namespace Philosophy.EPI_10

/-- Number of worlds below N satisfying p. -/
def count (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | N + 1 => count p N + (if p N then 1 else 0)

/-- Claim i is true at world w iff w ≠ i. -/
def claim (i w : Nat) : Bool := w != i

/-- The preface proposition: some claim is false. -/
def preface (n w : Nat) : Bool := decide (w < n)

theorem count_claim_below (i : Nat) : ∀ N, N ≤ i → count (claim i) N = N := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro h
    have hne : N ≠ i := by omega
    simp [count, ih (by omega), claim, hne]

theorem count_claim (i : Nat) : ∀ N, i < N → count (claim i) N = N - 1 := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ N ih =>
    intro h
    by_cases e : N = i
    · subst e
      simp [count, count_claim_below N N (Nat.le_refl N), claim]
    · have h' : i < N := by omega
      simp [count, ih h', claim, e]
      omega

theorem count_preface (n : Nat) : ∀ N, N ≤ n → count (preface n) N = N := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro h
    have : N < n := by omega
    simp [count, ih (by omega), preface, this]

/-- Proposition 2.2. In the model with n claims, each claim and the preface
proposition hold in exactly n of the n + 1 worlds. -/
theorem threshold (n i : Nat) (hi : i < n) :
    count (claim i) (n + 1) = n ∧ count (preface n) (n + 1) = n := by
  refine ⟨by rw [count_claim i (n + 1) (by omega)]; rfl, ?_⟩
  simp [count, count_preface n n (Nat.le_refl n), preface]

/-- Proposition 2.3. No world makes every claim and the preface true. -/
theorem inconsistent (n : Nat) :
    ¬ ∃ w, w ≤ n ∧ (∀ i, i < n → claim i w = true) ∧ preface n w = true := by
  intro ⟨w, _, hc, hp⟩
  simp [preface] at hp
  have := hc w hp
  simp [claim] at this

/-- The present collection: 722 manuscripts. -/
example : count (preface 722) 723 = 722 := (threshold 722 0 (by decide)).2

end Philosophy.EPI_10

#print axioms Philosophy.EPI_10.threshold
#print axioms Philosophy.EPI_10.inconsistent
