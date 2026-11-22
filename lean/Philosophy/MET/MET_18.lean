/-
MET-18 · Epistemicism and the Sharpness of the World
Formalization of Lemmas 3.1 and 3.2, Proposition 3.3, Theorem 3.4,
Corollary 3.5, Proposition 3.6 and Theorem 4.4.

Part I (Sections 2 and 3) is a margin-for-error model of a sorites series.
Positions in the series are natural numbers. An interpretation of the vague
predicate F fixes a classical extension (Definition 2.1). Interpretations
that differ by a small shift in use are indiscriminable to the speaker
(Assumption 2.4, Assumption 2.6), and knowledge is truth throughout the
interpretations indiscriminable from the actual one (Definition 2.5).

Part II (Section 4) is Evans's argument against indeterminate identity,
with the determinacy operator taken as an operator on worldly states of
affairs.

What this file establishes. Under any interpretation, a series that begins
with an F and contains a non-F has a last F, and only one (Lemmas 3.1, 3.2).
Where the endpoints of the series are known, it is known that there is a
last F, there is one, and of no position is it known that it is the last F
(Theorem 3.4). Knowledge obeys a margin for error (Proposition 3.3), which
makes the knowledge version of the tolerance premise true at every point
(Corollary 3.5). In the concrete model with margin m the cases that are
neither known to be F nor known not to be F are exactly the 2m positions
around the boundary (Proposition 3.6), which also shows the assumptions of
Part I consistent. If indeterminacy were worldly, determinately determinate
indeterminacy of identity would be impossible (Theorem 4.4).

What it does not establish. It does not establish that the margin model is
the right account of our knowledge of the application of vague predicates,
nor that use determines a classical extension at all; those are Assumptions
2.2, 2.4 and 2.6 and Definition 2.5, defended in the manuscript. It does not
establish that every apparent vague object is a precise object picked out
vaguely, which the manuscript argues case by case in Section 4.
-/

namespace Philosophy.MET_18

/-! ## Part I. The margin model -/

/-- Definition 2.1. Interpretations of the vague predicate F, as fixed by
patterns of use. -/
axiom Interp : Type

/-- Definition 2.1. `Ext u i`: under interpretation `u`, position `i` of the
sorites series falls in the extension of F. Every interpretation assigns a
classical extension: for each position, F applies or it does not. -/
axiom Ext : Interp → Nat → Prop

/-- Assumption 2.2 (penumbral monotonicity). If a position is F, every
earlier position is F. -/
axiom monotone : ∀ u i, Ext u (i + 1) → Ext u i

/-- Definition 2.3. Position `i` is the last F (the boundary) under `u`. -/
def Last (u : Interp) (i : Nat) : Prop := Ext u i ∧ ¬ Ext u (i + 1)

/-- Assumption 2.4. `Close u v`: interpretation `v` is indiscriminable from
`u` by the speakers whose use fixes `u`. Indiscriminability is reflexive. -/
axiom Close : Interp → Interp → Prop

/-- Assumption 2.4 (reflexivity). -/
axiom close_refl : ∀ u, Close u u

/-- Definition 2.5. What is known about F at `u`: what holds under every
interpretation indiscriminable from `u`. -/
def Knows (u : Interp) (φ : Interp → Prop) : Prop := ∀ v, Close u v → φ v

/-- Assumption 2.6 (semantic plasticity), first half. A slight shift in use
would move the boundary one place later, and the shifted interpretation is
indiscriminable from the original. -/
axiom shift_up : ∀ u, ∃ v, Close u v ∧ ∀ i, Ext v (i + 1) ↔ Ext u i

/-- Assumption 2.6 (semantic plasticity), second half. A slight shift in
use would move the boundary one place earlier. -/
axiom shift_down : ∀ u, ∃ v, Close u v ∧ ∀ i, Ext v i ↔ Ext u (i + 1)

/-- Lemma 3.1 (sharpness). Under any interpretation, a series that begins
with an F and has a non-F at position n has a last F before n. -/
theorem sharp (u : Interp) (n : Nat) (h0 : Ext u 0) (hn : ¬ Ext u n) :
    ∃ i, i < n ∧ Last u i := by
  induction n with
  | zero => exact absurd h0 hn
  | succ k ih =>
    cases Classical.em (Ext u k) with
    | inl hk => exact ⟨k, Nat.lt_succ_self k, hk, hn⟩
    | inr hk =>
      obtain ⟨i, hi, hl⟩ := ih hk
      exact ⟨i, Nat.lt_succ_of_lt hi, hl⟩

theorem ext_le (u : Interp) (i : Nat) : ∀ j, j ≤ i → Ext u i → Ext u j := by
  induction i with
  | zero => intro j hj h; rw [Nat.le_zero.mp hj]; exact h
  | succ k ih =>
    intro j hj h
    cases Nat.lt_or_eq_of_le hj with
    | inl hlt => exact ih j (Nat.le_of_lt_succ hlt) (monotone u k h)
    | inr heq => rw [heq]; exact h

/-- Lemma 3.2 (uniqueness). Under any interpretation there is at most one
last F. -/
theorem last_unique (u : Interp) (i j : Nat) (hi : Last u i) (hj : Last u j) :
    i = j := by
  cases Nat.lt_trichotomy i j with
  | inl h => exact absurd (ext_le u j (i + 1) h hj.1) hi.2
  | inr h =>
    cases h with
    | inl h => exact h
    | inr h => exact absurd (ext_le u i (j + 1) h hi.1) hj.2

/-- Proposition 3.3 (margin for error). If position i is known to be F, then
position i + 1 is F; if position i + 1 is known not to be F, then position i
is not F. -/
theorem margin (u : Interp) (i : Nat) :
    (Knows u (fun v => Ext v i) → Ext u (i + 1)) ∧
    (Knows u (fun v => ¬ Ext v (i + 1)) → ¬ Ext u i) := by
  constructor
  · intro hk
    obtain ⟨v, hc, hv⟩ := shift_down u
    exact (hv i).mp (hk v hc)
  · intro hk h
    obtain ⟨v, hc, hv⟩ := shift_up u
    exact hk v hc ((hv i).mpr h)

/-- Knowledge is factive in the model. -/
theorem factive (u : Interp) (φ : Interp → Prop) (h : Knows u φ) : φ u :=
  h u (close_refl u)

/-- Theorem 3.4 (main result). Suppose it is known that position 0 is F and
that position n is not F. Then it is known that there is a last F before n;
there is a last F; and of no position is it known that it is the last F. -/
theorem epistemicism (u : Interp) (n : Nat)
    (h0 : Knows u (fun v => Ext v 0)) (hn : Knows u (fun v => ¬ Ext v n)) :
    Knows u (fun v => ∃ i, i < n ∧ Last v i) ∧
    (∃ i, Last u i) ∧
    ∀ i, ¬ Knows u (fun v => Last v i) := by
  refine ⟨fun v hc => sharp v n (h0 v hc) (hn v hc), ?_, ?_⟩
  · obtain ⟨i, _, hl⟩ := sharp u n (h0 u (close_refl u)) (hn u (close_refl u))
    exact ⟨i, hl⟩
  · intro i hk
    have hu := factive u _ hk
    obtain ⟨v, hc, hv⟩ := shift_up u
    have hlv := hk v hc
    exact hlv.2 ((hv i).mpr hu.1)

/-- Corollary 3.5 (the sorites diagnosed). The tolerance premise fails at
exactly one position, but its knowledge version holds at every position. -/
theorem sorites_diagnosis (u : Interp) (n : Nat)
    (h0 : Ext u 0) (hn : ¬ Ext u n) :
    (∃ i, Ext u i ∧ ¬ Ext u (i + 1) ∧ ∀ j, Ext u j ∧ ¬ Ext u (j + 1) → j = i) ∧
    (∀ i, Knows u (fun v => Ext v i) → Ext u (i + 1)) := by
  refine ⟨?_, fun i => (margin u i).1⟩
  obtain ⟨i, _, hl⟩ := sharp u n h0 hn
  exact ⟨i, hl.1, hl.2, fun j hj => last_unique u j i hj hl⟩

/-! ## The concrete model (Proposition 3.6)

Interpretations are boundary positions `c`: F applies to the positions below
`c`. Interpretations within `m` places of each other are indiscriminable. -/

namespace Model

def ExtM (c i : Nat) : Prop := i < c

def CloseM (m c d : Nat) : Prop := c ≤ d + m ∧ d ≤ c + m

def KnowsM (m c : Nat) (φ : Nat → Prop) : Prop := ∀ d, CloseM m c d → φ d

/-- Proposition 3.6, first part. With margin m ≥ 1, the concrete model
satisfies Assumptions 2.2, 2.4 and 2.6. -/
theorem satisfies (m : Nat) (hm : 1 ≤ m) :
    (∀ c i, ExtM c (i + 1) → ExtM c i) ∧
    (∀ c, CloseM m c c) ∧
    (∀ c, ∃ d, CloseM m c d ∧ ∀ i, ExtM d (i + 1) ↔ ExtM c i) ∧
    (∀ c, ∃ d, CloseM m c d ∧ ∀ i, ExtM d i ↔ ExtM c (i + 1)) := by
  refine ⟨fun c i h => ?_, fun c => ?_, fun c => ⟨c + 1, ?_, fun i => ?_⟩,
    fun c => ⟨c - 1, ?_, fun i => ?_⟩⟩
  · simp only [ExtM] at *; omega
  · simp only [CloseM]; omega
  · simp only [CloseM]; omega
  · simp only [ExtM]; omega
  · simp only [CloseM]; omega
  · simp only [ExtM]; omega

/-- Proposition 3.6, second part. With margin m, position i is known to be F
at boundary c exactly when i + m < c. -/
theorem known_F (m c i : Nat) : KnowsM m c (fun d => ExtM d i) ↔ i + m < c := by
  constructor
  · intro h
    have := h (c - m) (by simp only [CloseM]; omega)
    simp only [ExtM] at this; omega
  · intro h d hd
    simp only [CloseM] at hd; simp only [ExtM]; omega

/-- Proposition 3.6, third part. Position i is known not to be F at boundary
c exactly when c + m ≤ i. -/
theorem known_not_F (m c i : Nat) : KnowsM m c (fun d => ¬ ExtM d i) ↔ c + m ≤ i := by
  constructor
  · intro h
    have := h (c + m) (by simp only [CloseM]; omega)
    simp only [ExtM] at this; omega
  · intro h d hd
    simp only [CloseM] at hd; simp only [ExtM]; omega

/-- Proposition 3.6 (borderline cases). Position i is neither known to be F
nor known not to be F exactly when c ≤ i + m and i < c + m: the borderline
region consists of the 2m positions from c - m to c + m - 1. -/
theorem borderline (m c i : Nat) :
    (¬ KnowsM m c (fun d => ExtM d i) ∧ ¬ KnowsM m c (fun d => ¬ ExtM d i)) ↔
    (c ≤ i + m ∧ i < c + m) := by
  rw [known_F, known_not_F]; omega

end Model

/-! ## Part II. Evans's argument -/

/-- Objects. -/
axiom Obj : Type

/-- Definition 4.1. `Det p`: it is determinately the case that p, where the
operator applies to worldly states of affairs (so that, like every function
on propositions, it respects the identity of the objects they concern). -/
axiom Det : Prop → Prop

/-- Definition 4.1. Worldly indeterminacy. -/
def Ind (p : Prop) : Prop := ¬ Det p ∧ ¬ Det (¬ p)

/-- Assumption 4.2. Self-identity is determinate. -/
axiom det_refl : ∀ x : Obj, Det (x = x)

/-- Assumption 4.3. Determinacy is closed under entailment. -/
axiom det_mono : ∀ p q : Prop, (p → q) → Det p → Det q

/-- Theorem 4.4, first step (Evans). If it is indeterminate whether a = b,
then a ≠ b. -/
theorem evans_step (a b : Obj) (h : Ind (a = b)) : a ≠ b := by
  intro e
  subst e
  exact h.1 (det_refl a)

/-- Theorem 4.4 (Evans). If it is determinate that it is indeterminate
whether a = b, then it is not indeterminate whether a = b. -/
theorem evans (a b : Obj) (h : Det (Ind (a = b))) : ¬ Ind (a = b) := by
  intro hi
  exact hi.2 (det_mono _ _ (evans_step a b) h)

end Philosophy.MET_18

#print axioms Philosophy.MET_18.epistemicism
#print axioms Philosophy.MET_18.sorites_diagnosis
#print axioms Philosophy.MET_18.Model.borderline
#print axioms Philosophy.MET_18.evans
