/-
REL-03 · Divine Hiddenness as a Signalling Equilibrium
Formalization of Lemmas 3.1 and 3.2, Theorem 3.3, Corollary 3.4,
Proposition 3.5 and Theorem 4.1.

The hiddenness game (Definition 2.1). God chooses the clarity `c` of a
signal, from 0 to 4; `c = 4` is unambiguous revelation. Creatures are open
or closed and respond by turning toward God or away. Creature payoffs are
those of Definition 2.2; God's payoffs (Definition 2.5) are doubled to avoid
fractions. Ties are broken in favour of the creature's disposition.

What this file establishes. Under revelation both types turn toward God and
the response is not free (Definition 2.4); under hiddenness the types
separate. God's payoff is uniquely maximized at `c = 3`. With `n_o` open and
`n_c` closed creatures, `c = 3` beats `c = 4` iff `5 n_o > 3 n_c`. Given the
equilibrium choice, the likelihood of hiddenness under theism is maximal, so
hiddenness cannot raise the odds against theism.

What it does not establish. That the game, with these payoffs, represents
the relation between God and creatures; Sections 2 and 6 of the manuscript
argue for that.
-/

namespace Philosophy.REL_03

/-- Creature types (Definition 2.1). -/
inductive Ty
  | openT | closedT
  deriving DecidableEq

/-- Responses (Definition 2.1). -/
inductive Resp
  | toward | away
  deriving DecidableEq

/-- Definition 2.2. Creature payoffs at clarity `c`. -/
def creaturePay : Ty → Nat → Resp → Nat
  | .openT, c, .toward => 2 + c
  | .openT, _, .away => 0
  | .closedT, c, .toward => c
  | .closedT, _, .away => 3

/-- Best response, ties broken in favour of the creature's disposition
(toward for the open type, away for the closed type). -/
def best (t : Ty) (c : Nat) : Resp :=
  match t with
  | .openT => if creaturePay .openT c .toward ≥ creaturePay .openT c .away then .toward else .away
  | .closedT => if creaturePay .closedT c .toward > creaturePay .closedT c .away then .toward else .away

/-- Definition 2.4. The response is free at `c` if the two types' best
responses differ. -/
def Free (c : Nat) : Prop := best .openT c ≠ best .closedT c

instance (c : Nat) : Decidable (Free c) := by unfold Free; infer_instance

/-- Definition 2.5 (doubled). Relational value to God of one creature's
response: 8 for a free turning toward, 2 for compliance, 0 for refusal. -/
def relational (t : Ty) (c : Nat) : Nat :=
  if best t c = .toward then (if Free c then 8 else 2) else 0

/-- Definition 2.5 (doubled), with one creature of each type
(Assumption 2.7): relational values plus belief value `c` per creature. -/
def godPay (c : Nat) : Nat := relational .openT c + relational .closedT c + 2 * c

/-- Lemma 3.1 (revelation pools). -/
theorem revelation_pools :
    best .openT 4 = .toward ∧ best .closedT 4 = .toward ∧ ¬ Free 4 := by decide

/-- Lemma 3.2 (hiddenness separates). -/
theorem hiddenness_separates :
    ∀ c, c ≤ 3 → best .openT c = .toward ∧ best .closedT c = .away ∧ Free c := by decide

/-- Theorem 3.3 (optimal clarity). God's payoff is maximized, uniquely, at
`c = 3`, and the response is not free at `c = 4`. -/
theorem optimal_clarity :
    (∀ c, c ≤ 4 → godPay c ≤ godPay 3) ∧
    (∀ c, c ≤ 4 → c ≠ 3 → godPay c < godPay 3) ∧ ¬ Free 4 := by decide

/-- God's payoffs (doubled): 14 at `c = 3`, 12 at `c = 4`, i.e. 7 and 6. -/
theorem payoff_values : godPay 3 = 14 ∧ godPay 4 = 12 := by decide

/-- Corollary 3.4 (equilibrium). The creatures' strategies are best
responses at every clarity, and God's choice of `c = 3` is the unique
optimum given them. -/
theorem equilibrium :
    (∀ c, c ≤ 4 → best .openT c = .toward) ∧
    (∀ c, c ≤ 4 → (best .closedT c = .toward ↔ c = 4)) ∧
    (∀ c, c ≤ 4 → c ≠ 3 → godPay c < godPay 3) := by decide

/-- Proposition 3.5 (robustness), doubled payoffs with `no` open and `nc`
closed creatures: `11 no + 3 nc` at `c = 3`, `6 no + 6 nc` at `c = 4`. -/
theorem robustness (no nc : Nat) :
    6 * no + 6 * nc < 11 * no + 3 * nc ↔ 3 * nc < 5 * no := by omega

/-- The clarity a perfectly loving God chooses (Theorem 3.3). -/
def chosen : Nat := 3

/-- Likelihood, in units of `1/N`, of observing hiddenness (no unambiguous
revelation) given that God exists and plays the equilibrium. -/
def likelihoodHiddenGivenGod (N : Nat) : Nat := if chosen < 4 then N else 0

/-- Theorem 4.1. Given the equilibrium, `P(H | G) = 1`; for any
`P(H | ¬G) = m/N ≤ 1` and prior weight `b` on atheism, the posterior weight
on atheism after observing `H` is at most its prior weight scaled by
`P(H | G)`: the likelihood ratio does not favour atheism. -/
theorem not_evidence (N m b : Nat) (hm : m ≤ N) :
    likelihoodHiddenGivenGod N = N ∧ b * m ≤ b * likelihoodHiddenGivenGod N := by
  have h : likelihoodHiddenGivenGod N = N := by simp [likelihoodHiddenGivenGod, chosen]
  exact ⟨h, by rw [h]; exact Nat.mul_le_mul_left b hm⟩

end Philosophy.REL_03

#print axioms Philosophy.REL_03.optimal_clarity
#print axioms Philosophy.REL_03.robustness
#print axioms Philosophy.REL_03.not_evidence
