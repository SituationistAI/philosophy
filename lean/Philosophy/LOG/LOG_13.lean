/-
LOG-13 · Distributivity Survives Quantum Mechanics
Formalization of Theorem 3.1, Propositions 3.3 and 3.4, Theorem 4.2 and
Corollary 4.3.

The results are mathematical, so the module uses no axioms beyond those of
Lean's logic. The philosophical premises of the manuscript (Assumptions 2.3
and 2.4 and Principle P1, on what the empirical content of quantum
mechanics is and on how a revision is located), and Theorem 4.4 which
rests on them, are argued in prose and are not formalized.

What this file establishes.
* Theorem 3.1: the distributive law holds for propositions.
* Proposition 3.3: in the six-element ortholattice MO2, the lattice of
  closed subspaces of a two-dimensional space restricted to two pairs of
  orthogonal rays, distributivity fails.
* Proposition 3.4: every Boolean block of MO2 (a context of compatible
  propositions) is distributive.
* Theorem 4.2: any classical joint distribution over three two-valued
  quantities gives total agreement probability at least 1 across the three
  pairs (Wigner's form of Bell's inequality).
* Corollary 4.3: no classical joint distribution reproduces pairwise
  agreement probabilities of 1/4, which quantum mechanics predicts for
  suitable spin measurements.
It does not establish that the quantum predictions are correct, or that
the failure of a joint distribution is the whole of what quantum mechanics
revises.
-/

namespace Philosophy.LOG_13

/-- Theorem 3.1. The distributive law. -/
theorem distributive (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  · intro ⟨hp, hqr⟩
    cases hqr with
    | inl hq => exact Or.inl ⟨hp, hq⟩
    | inr hr => exact Or.inr ⟨hp, hr⟩
  · intro h
    cases h with
    | inl h => exact ⟨h.1, Or.inl h.2⟩
    | inr h => exact ⟨h.1, Or.inr h.2⟩

/-- Definition 3.2. The ortholattice MO2: bottom, top, two rays a, b and
their orthocomplements a', b'. -/
inductive MO2 where
  | bot | a | a' | b | b' | top
  deriving DecidableEq

open MO2

/-- Definition 3.2. Meet in MO2 (intersection of subspaces). -/
def meet : MO2 → MO2 → MO2
  | top, x => x
  | x, top => x
  | bot, _ => bot
  | _, bot => bot
  | x, y => if x = y then x else bot

/-- Definition 3.2. Join in MO2 (span of subspaces). -/
def join : MO2 → MO2 → MO2
  | bot, x => x
  | x, bot => x
  | top, _ => top
  | _, top => top
  | x, y => if x = y then x else top

/-- Definition 3.2. Orthocomplement in MO2. -/
def perp : MO2 → MO2
  | bot => top
  | top => bot
  | a => a'
  | a' => a
  | b => b'
  | b' => b

/-- Proposition 3.3. Distributivity fails in MO2:
a ∧ (b ∨ b') = a, while (a ∧ b) ∨ (a ∧ b') = 0. -/
theorem mo2_not_distributive :
    meet a (join b b') = a ∧ join (meet a b) (meet a b') = bot ∧
    meet a (join b b') ≠ join (meet a b) (meet a b') := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- Membership in the Boolean block {0, a, a', 1}. -/
def blockA : MO2 → Prop
  | bot | a | a' | top => True
  | _ => False

/-- Membership in the Boolean block {0, b, b', 1}. -/
def blockB : MO2 → Prop
  | bot | b | b' | top => True
  | _ => False

/-- Proposition 3.4. Each Boolean block of MO2 is distributive. -/
theorem blocks_distributive :
    (∀ x y z, blockA x → blockA y → blockA z →
      meet x (join y z) = join (meet x y) (meet x z)) ∧
    (∀ x y z, blockB x → blockB y → blockB z →
      meet x (join y z) = join (meet x y) (meet x z)) := by
  constructor <;>
  · intro x y z hx hy hz
    cases x <;> cases y <;> cases z <;>
      first | rfl | (exfalso; assumption)

/-- Theorem 4.2. Let a classical joint distribution over three two-valued
quantities A, B, C be given by natural-number weights on the eight joint
value assignments (n_ijk for A = i, B = j, C = k), with total N. Then the
weights of the assignments on which A = B, B = C and A = C sum to at
least N: every assignment makes at least one pair agree. -/
theorem wigner (n000 n001 n010 n011 n100 n101 n110 n111 N : Nat)
    (hN : N = n000 + n001 + n010 + n011 + n100 + n101 + n110 + n111) :
    (n000 + n001 + n110 + n111) + (n000 + n100 + n011 + n111) +
      (n000 + n010 + n101 + n111) ≥ N := by
  omega

/-- Corollary 4.3. No classical joint distribution assigns probability 1/4
to agreement in each of the three pairs: four times each agreement weight
cannot equal the total unless the total is zero. -/
theorem no_joint_distribution
    (n000 n001 n010 n011 n100 n101 n110 n111 N : Nat)
    (hN : N = n000 + n001 + n010 + n011 + n100 + n101 + n110 + n111)
    (hpos : N > 0)
    (hAB : 4 * (n000 + n001 + n110 + n111) = N)
    (hBC : 4 * (n000 + n100 + n011 + n111) = N)
    (hAC : 4 * (n000 + n010 + n101 + n111) = N) : False := by
  omega

end Philosophy.LOG_13

#print axioms Philosophy.LOG_13.distributive
#print axioms Philosophy.LOG_13.mo2_not_distributive
#print axioms Philosophy.LOG_13.blocks_distributive
#print axioms Philosophy.LOG_13.no_joint_distribution
