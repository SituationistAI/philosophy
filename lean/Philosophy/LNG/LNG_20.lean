/-
LNG-20 · Conditionals Without Truth Values
Formalization of Lemmas 4.1 and 4.2, Theorem 4.3, Corollary 4.4 and
Propositions 5.2 and 5.3.

A finite probability model is a finite list of worlds with natural-number
weights (Definition 3.1); the probability of an event is its weight divided
by the total weight, so that every identity between probabilities is stated
here by cross-multiplication. Conditionalizing on an event sets the weight of
the worlds outside it to zero (Definition 3.2). An event is a Boolean
function on worlds. A class of weightings is closed under conditionalization
(Assumption 3.4) if conditionalizing a member on an event of positive weight
yields a member.

A proposition X satisfies the Thesis for the antecedent A and consequent C
over a class of weightings (Principle P1 together with Assumption 3.3) if,
for every member of the class that gives A positive weight, the probability
of X equals the conditional probability of C given A. The proposition X is
the same for every member of the class: that is what it is for the
conditional to have truth conditions that do not vary with the credence of
the person who considers it.

What this file establishes. If some proposition satisfies the Thesis over a
class closed under conditionalization, then A and C are probabilistically
independent under every member of the class that gives positive weight to
both A-and-C and A-and-not-C (Theorem 4.3, Lewis's first triviality result).
In the four-world model with weights 2, 1, 0, 1 no proposition satisfies the
Thesis (Corollary 4.4). The probability of the material conditional is never
lower than the conditional probability (Proposition 5.3), and in Adams's
probabilistic logic the uncertainty of the conclusion of modus ponens is at
most the sum of the uncertainties of its premises (Proposition 5.2).

What it does not establish. It does not establish the Thesis itself, which
is defended in the manuscript as an account of the probability of an
indicative conditional, nor that rational credences form a class closed
under conditionalization; nor does it establish that the denial of truth
values is the only response to triviality. Those are the subject of
Sections 2, 3 and 7 of the manuscript.
-/

namespace Philosophy.LNG_20

variable {W : Type}

/-- Definition 3.1. The weight of an event under a weighting, summed over a
finite list of worlds. -/
def mass (wt : W → Nat) (E : W → Bool) : List W → Nat
  | [] => 0
  | x :: xs => (if E x = true then wt x else 0) + mass wt E xs

/-- Conjunction and negation of events, and the necessary event. -/
def conj (E F : W → Bool) : W → Bool := fun x => E x && F x
def neg (E : W → Bool) : W → Bool := fun x => !E x
def top : W → Bool := fun _ => true

/-- Definition 3.2. Conditionalization of a weighting on an event. -/
def cond (wt : W → Nat) (B : W → Bool) : W → Nat :=
  fun x => if B x = true then wt x else 0

/-- Lemma 4.1. The weight of an event after conditionalizing on `B` is the
weight of its conjunction with `B`. -/
theorem mass_cond (wt : W → Nat) (B E : W → Bool) (l : List W) :
    mass (cond wt B) E l = mass wt (conj E B) l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [mass, cond, conj, ih]
    by_cases hE : E x <;> by_cases hB : B x <;> simp [hE, hB]

/-- Lemma 4.2. Additivity: the weight of an event is the sum of the weights
of its conjunctions with `F` and with the negation of `F`. -/
theorem mass_split (wt : W → Nat) (E F : W → Bool) (l : List W) :
    mass wt E l = mass wt (conj E F) l + mass wt (conj E (neg F)) l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [mass, conj, neg]
    rw [ih]
    by_cases hE : E x <;> by_cases hF : F x <;> simp [hE, hF] <;> omega

/-- Assumption 3.4. A class of weightings closed under conditionalization on
events of positive weight. -/
def Closed (ws : List W) (Cr : (W → Nat) → Prop) : Prop :=
  ∀ wt B, Cr wt → 0 < mass wt B ws → Cr (cond wt B)

/-- Principle P1 with Assumption 3.3. The proposition `X` has, under every
member of the class that gives `A` positive weight, the conditional
probability of `C` given `A` as its probability. -/
def Thesis (ws : List W) (Cr : (W → Nat) → Prop) (A C X : W → Bool) : Prop :=
  ∀ wt, Cr wt → 0 < mass wt A ws →
    mass wt X ws * mass wt A ws = mass wt (conj A C) ws * mass wt top ws

/-- Two events are independent under a weighting:
P(A and C) P(top) = P(A) P(C). -/
def Indep (ws : List W) (wt : W → Nat) (A C : W → Bool) : Prop :=
  mass wt (conj A C) ws * mass wt top ws = mass wt C ws * mass wt A ws

theorem conj_top (wt : W → Nat) (B : W → Bool) (l : List W) :
    mass wt (conj top B) l = mass wt B l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [mass, conj, top] at *; rw [ih]; simp

theorem mass_conj_comm (wt : W → Nat) (E F : W → Bool) (l : List W) :
    mass wt (conj E F) l = mass wt (conj F E) l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [mass, conj] at *; rw [ih]; by_cases hE : E x <;> by_cases hF : F x <;> simp [hE, hF]

theorem mass_conj_idem (wt : W → Nat) (A C : W → Bool) (l : List W) :
    mass wt (conj (conj A C) C) l = mass wt (conj A C) l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [mass, conj] at *; rw [ih]; by_cases hA : A x <;> by_cases hC : C x <;> simp [hA, hC]

theorem mass_conj_contra (wt : W → Nat) (A C : W → Bool) (l : List W) :
    mass wt (conj (conj A C) (neg C)) l = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [mass, conj, neg] at *; rw [ih]; by_cases hA : A x <;> by_cases hC : C x <;> simp [hA, hC]

/-- Theorem 4.3 (Lewis's first triviality result). If a proposition `X`
satisfies the Thesis for `A` and `C` over a class closed under
conditionalization, then under every member of the class that gives
positive weight to `A ∧ C` and to `A ∧ ¬C`, `A` and `C` are independent. -/
theorem lewis (ws : List W) (Cr : (W → Nat) → Prop) (A C X : W → Bool)
    (hcl : Closed ws Cr) (hth : Thesis ws Cr A C X)
    (wt : W → Nat) (hwt : Cr wt)
    (hAC : 0 < mass wt (conj A C) ws) (hAnC : 0 < mass wt (conj A (neg C)) ws) :
    Indep ws wt A C := by
  -- The three relevant weights are positive.
  have hA : 0 < mass wt A ws := by rw [mass_split wt A C ws]; omega
  have hC : 0 < mass wt C ws := by
    rw [mass_split wt C A ws, mass_conj_comm wt C A]; omega
  have hnC : 0 < mass wt (neg C) ws := by
    rw [mass_split wt (neg C) A ws, mass_conj_comm wt (neg C) A]; omega
  -- Conditionalizing on C.
  have h1 := hth (cond wt C) (hcl wt C hwt hC)
    (by rw [mass_cond]; exact hAC)
  rw [mass_cond, mass_cond, mass_cond, mass_cond, conj_top,
    mass_conj_idem] at h1
  have hXC : mass wt (conj X C) ws = mass wt C ws :=
    Nat.eq_of_mul_eq_mul_right hAC (by rw [h1, Nat.mul_comm])
  -- Conditionalizing on not-C.
  have h2 := hth (cond wt (neg C)) (hcl wt (neg C) hwt hnC)
    (by rw [mass_cond]; exact hAnC)
  rw [mass_cond, mass_cond, mass_cond, mass_conj_contra, Nat.zero_mul] at h2
  have hXnC : mass wt (conj X (neg C)) ws = 0 := by
    rcases Nat.mul_eq_zero.mp h2 with h | h
    · exact h
    · omega
  -- The original weighting.
  have h3 := hth wt hwt hA
  have hX : mass wt X ws = mass wt C ws := by
    rw [mass_split wt X C ws, hXC, hXnC]; rfl
  unfold Indep
  rw [← h3, hX]

/-! ## A concrete model -/

/-- Worlds of the concrete model: pairs recording the truth values of the
antecedent and the consequent. -/
abbrev World4 := Bool × Bool

def worlds4 : List World4 := [(true, true), (true, false), (false, true), (false, false)]

def antecedent : World4 → Bool := fun w => w.1
def consequent : World4 → Bool := fun w => w.2

/-- The weighting 2, 1, 0, 1 on the four worlds. Under it the probability of
the antecedent is 3/4, of the consequent 1/2, and of the consequent given the
antecedent 2/3. -/
def credence : World4 → Nat
  | (true, true) => 2
  | (true, false) => 1
  | (false, true) => 0
  | (false, false) => 1

/-- The class of all weightings, which is closed under conditionalization. -/
def AllWeightings : (World4 → Nat) → Prop := fun _ => True

/-- Corollary 4.4. In the four-world model, no proposition satisfies the
Thesis for the antecedent and the consequent over the class of all
weightings: the conditional cannot be given truth conditions on which its
probability is the conditional probability. -/
theorem no_conditional_proposition :
    ¬ ∃ X, Thesis worlds4 AllWeightings antecedent consequent X := by
  intro ⟨X, hX⟩
  have h := lewis worlds4 AllWeightings antecedent consequent X
    (fun _ _ _ _ => trivial) hX credence trivial (by decide) (by decide)
  unfold Indep at h
  exact absurd h (by decide)

/-! ## Adams's logic -/

theorem mass_le_top (wt : W → Nat) (E : W → Bool) (l : List W) :
    mass wt E l ≤ mass wt top l := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x xs ih => simp only [mass, top]; by_cases hE : E x <;> simp [hE] <;> omega

/-- Proposition 5.3. The probability of the material conditional
(not-A or C, whose weight is that of not-A plus that of A and C) is at least
the conditional probability of C given A. -/
theorem material_ge_conditional (ws : List W) (wt : W → Nat) (A C : W → Bool) :
    mass wt (conj A C) ws * mass wt top ws ≤
      (mass wt (neg A) ws + mass wt (conj A C) ws) * mass wt A ws := by
  have hT : mass wt top ws = mass wt A ws + mass wt (neg A) ws := by
    rw [mass_split wt top A ws, conj_top, conj_top]
  have hle : mass wt (conj A C) ws ≤ mass wt A ws := by
    rw [mass_split wt A C ws]; omega
  rw [hT, Nat.mul_add, Nat.add_mul, Nat.mul_comm (mass wt (conj A C) ws) (mass wt A ws)]
  have := Nat.mul_le_mul_right (mass wt (neg A) ws) hle
  have hc := Nat.mul_comm (mass wt A ws) (mass wt (neg A) ws)
  omega

/-- Proposition 5.2 (Adams). Uncertainty is one minus probability. The
uncertainty of the conclusion of modus ponens is at most the uncertainty of
the minor premise plus the uncertainty of the conditional premise:
u(C) ≤ u(A) + u(C given A), stated by multiplying through by P(top) P(A). -/
theorem modus_ponens_bound (ws : List W) (wt : W → Nat) (A C : W → Bool) :
    mass wt (neg C) ws * mass wt A ws ≤
      mass wt (neg A) ws * mass wt A ws + mass wt (conj A (neg C)) ws * mass wt top ws := by
  have h1 : mass wt (neg C) ws ≤ mass wt (conj A (neg C)) ws + mass wt (neg A) ws := by
    rw [mass_split wt (neg C) A ws, mass_conj_comm wt (neg C) A,
      mass_conj_comm wt (neg C) (neg A)]
    have := mass_le_top wt (conj (neg A) (neg C)) ws
    have h := mass_split wt (neg A) (neg C) ws
    omega
  have h2 : mass wt (conj A (neg C)) ws * mass wt A ws ≤
      mass wt (conj A (neg C)) ws * mass wt top ws :=
    Nat.mul_le_mul_left _ (mass_le_top wt A ws)
  have h3 := Nat.mul_le_mul_right (mass wt A ws) h1
  rw [Nat.add_mul] at h3
  omega

end Philosophy.LNG_20

#print axioms Philosophy.LNG_20.lewis
#print axioms Philosophy.LNG_20.no_conditional_proposition
#print axioms Philosophy.LNG_20.modus_ponens_bound
