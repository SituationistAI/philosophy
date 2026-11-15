/-
ETH-06 · A Moderate Duty of Beneficence
Formalization of Lemma 3.1, Theorem 3.2, Propositions 3.3 and 3.4 and
Theorem 3.5.

Income, gifts and the cost of meeting basic need are measured in a common
unit for one period. An agent gives a share of p per cent of her income I
when her gift is at least p·I/100 (Definition 2.1). The marginal requirement
(Definition 2.2) asks an agent to give until she reaches the level s at
which further giving would sacrifice something of comparable importance.

What this file establishes. If the cost of meeting basic need is at most one
per cent of the income of the affluent (Assumption 2.3), then whenever agents
holding at least a tenth of that income each give ten per cent, the need is
met (Theorem 3.2), and no smaller whole-percentage share guarantees this
(Proposition 3.3). Given that a tenth is a moderate share and a half is not
(Assumptions 2.4 and 2.5), the ten per cent requirement is moderate while the
marginal requirement is not, for every agent whose income is at least twice
the level s (Proposition 3.4, Theorem 3.5).

What it does not establish. The empirical bound on need, the choice of the
one-in-ten compliance floor (Principle P2) and the judgments of moderateness
are premises. Nothing here concerns how gifts should be directed; that is the
subject of POL-13.
-/

namespace Philosophy.ETH_06

/-- Definition 2.1. Giving a share of `p` per cent of income `I`. -/
def GivesShare (p I gift : Nat) : Prop := p * I ≤ 100 * gift

/-- Total income of a list of (income, gift) pairs. -/
def totalIncome : List (Nat × Nat) → Nat
  | [] => 0
  | x :: t => x.1 + totalIncome t

/-- Total gifts of a list of (income, gift) pairs. -/
def totalGift : List (Nat × Nat) → Nat
  | [] => 0
  | x :: t => x.2 + totalGift t

/-- Lemma 3.1. If every member of a group gives share `p`, the group gives
share `p` of its total income. -/
theorem share_sum (p : Nat) :
    ∀ l : List (Nat × Nat), (∀ x, x ∈ l → GivesShare p x.1 x.2) →
      p * totalIncome l ≤ 100 * totalGift l
  | [], _ => by simp [totalIncome, totalGift]
  | x :: t, h => by
    have hx := h x (List.mem_cons_self _ _)
    have ht := share_sum p t (fun y hy => h y (List.mem_cons_of_mem _ hy))
    unfold GivesShare at hx
    simp only [totalIncome, totalGift, Nat.mul_add]
    omega

/-- The cost of meeting basic need in the period. -/
axiom need : Nat

/-- The aggregate income of affluent agents in the period. -/
axiom affluentIncome : Nat

/-- Assumption 2.3 (the cost of need). Meeting basic need costs at most one
per cent of the income of the affluent. -/
axiom need_bound : 100 * need ≤ affluentIncome

/-- Theorem 3.2 (sufficiency). If the agents who comply hold at least a tenth
of affluent income and each gives ten per cent, basic need is met. -/
theorem sufficiency (compliers : List (Nat × Nat))
    (hgive : ∀ x, x ∈ compliers → GivesShare 10 x.1 x.2)
    (hfloor : affluentIncome ≤ 10 * totalIncome compliers) :
    need ≤ totalGift compliers := by
  have h := share_sum 10 compliers hgive
  have hn := need_bound
  omega

/-- Proposition 3.3 (minimality). For every share below ten per cent there
is a distribution in which need is exactly one per cent of affluent income,
compliers hold exactly a tenth of it and give exactly that share, and need
is not met. -/
theorem minimality (p : Nat) (hp : p < 10) :
    ∃ Y N T, 100 * N = Y ∧ 10 * T = Y ∧ p * T < 100 * N :=
  ⟨1000, 10, 100, rfl, rfl, by omega⟩

/-- Moderateness of a required share (in per cent of income). -/
axiom Moderate : Nat → Prop

/-- Assumption 2.4. A requirement to give a tenth of one's income is
moderate. -/
axiom tenth_moderate : Moderate 10

/-- Assumption 2.5. A requirement to give half of one's income is not
moderate, and neither is any larger requirement. -/
axiom half_immoderate : ∀ q, 50 ≤ q → ¬ Moderate q

/-- Definition 2.2. The share (in per cent, rounded down) required by the
marginal principle of an agent with income `I` and threshold level `s`. -/
def marginalShare (I s : Nat) : Nat := 100 * (I - s) / I

/-- Proposition 3.4. For an agent whose income is at least twice the level at
which the marginal principle stops, the marginal requirement is at least
half of her income. -/
theorem marginal_at_least_half (I s : Nat) (hI : 0 < I) (haff : 2 * s ≤ I) :
    50 ≤ marginalShare I s := by
  unfold marginalShare
  rw [Nat.le_div_iff_mul_le hI]
  omega

/-- Theorem 3.5 (the moderate duty). The ten per cent requirement is
sufficient at the compliance floor and moderate, no smaller whole share is
sufficient at that floor, and the marginal requirement is not moderate for
any agent whose income is at least twice the marginal level. -/
theorem moderate_duty :
    Moderate 10 ∧
    (∀ l : List (Nat × Nat), (∀ x, x ∈ l → GivesShare 10 x.1 x.2) →
        affluentIncome ≤ 10 * totalIncome l → need ≤ totalGift l) ∧
    (∀ p, p < 10 → ∃ Y N T, 100 * N = Y ∧ 10 * T = Y ∧ p * T < 100 * N) ∧
    (∀ I s, 0 < I → 2 * s ≤ I → ¬ Moderate (marginalShare I s)) :=
  ⟨tenth_moderate, sufficiency, minimality,
   fun I s hI haff => half_immoderate _ (marginal_at_least_half I s hI haff)⟩

end Philosophy.ETH_06

#print axioms Philosophy.ETH_06.moderate_duty
