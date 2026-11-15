/-
ETH-18 · The Duty to Rescue and Its Limits
Formalization of Theorem 3.1 and Corollary 3.2.

Costs of rescue are measured in income-equivalents. An agent with annual
income I has a rescue allowance of one tenth of I for the year
(Definition 2.1). The rescue principle (Assumption 2.2) requires a rescue
whose cost does not exceed what remains of the allowance after the costs of
the rescues already required of her that year; the limit (Assumption 2.3)
says that a rescue costing more is not required. Every rescue is permitted
(Assumption 2.4). A rescue is supererogatory when it is permitted and not
required (Definition 2.5).

What this file establishes. An agent who performs exactly the rescues
required of her bears in a year a total cost no greater than her allowance,
whatever the sequence of emergencies; a costless rescue is always required;
a first rescue within the allowance is required; and a rescue beyond the
remaining allowance is supererogatory (Theorem 3.1, Corollary 3.2).

What it does not establish. The commensurability of rescue costs with income,
the size of the allowance and the three principles are premises. The upper
bound on supererogation (ETH-14) is not modelled.
-/

namespace Philosophy.ETH_18

/-- Definition 2.1. The annual rescue allowance: a tenth of income. -/
def allowance (I : Nat) : Nat := I / 10

/-- `Required I x c`: for an agent with income `I` who has already borne cost
`x` in required rescues this year, a rescue of cost `c` is required. -/
axiom Required : Nat → Nat → Nat → Prop

/-- `Permitted I x c`: the rescue is permitted. -/
axiom Permitted : Nat → Nat → Nat → Prop

/-- Assumption 2.2 (the rescue principle). A rescue whose cost does not
exceed the remaining allowance is required. -/
axiom rescue_principle : ∀ I x c, c ≤ allowance I - x → Required I x c

/-- Assumption 2.3 (the limit). A rescue whose cost exceeds the remaining
allowance is not required. -/
axiom rescue_limit : ∀ I x c, allowance I - x < c → ¬ Required I x c

/-- Assumption 2.4. Rescue is permitted. -/
axiom rescue_permitted : ∀ I x c, Permitted I x c

/-- Definition 2.5. Supererogatory: permitted and not required. -/
def Supererogatory (I x c : Nat) : Prop := Permitted I x c ∧ ¬ Required I x c

/-- The cost borne in a year by an agent who performs exactly the required
rescues among a sequence of emergencies with costs `l`, starting from `x`. -/
def borne (I : Nat) : Nat → List Nat → Nat
  | x, [] => x
  | x, c :: t => if c ≤ allowance I - x then borne I (x + c) t else borne I x t

theorem borne_bounded (I : Nat) :
    ∀ (l : List Nat) (x : Nat), x ≤ allowance I → borne I x l ≤ allowance I
  | [], x, hx => by simp [borne]; exact hx
  | c :: t, x, hx => by
    simp only [borne]
    split
    · exact borne_bounded I t (x + c) (by omega)
    · exact borne_bounded I t x hx

/-- Theorem 3.1 (the bounded duty to rescue). (a) Whatever the sequence of
emergencies, an agent who performs exactly the required rescues bears at
most her allowance in the year. (b) A costless rescue is always required.
(c) A first rescue costing no more than the allowance is required. -/
theorem bounded_duty (I : Nat) :
    (∀ l : List Nat, borne I 0 l ≤ allowance I) ∧
    (∀ x, Required I x 0) ∧
    (∀ c, c ≤ allowance I → Required I 0 c) := by
  refine ⟨fun l => borne_bounded I l 0 (Nat.zero_le _), fun x => ?_, fun c hc => ?_⟩
  · exact rescue_principle I x 0 (Nat.zero_le _)
  · exact rescue_principle I 0 c (by omega)

/-- Corollary 3.2. A rescue whose cost exceeds the remaining allowance is
supererogatory. -/
theorem beyond_supererogatory (I x c : Nat) (h : allowance I - x < c) :
    Supererogatory I x c :=
  ⟨rescue_permitted I x c, rescue_limit I x c h⟩

end Philosophy.ETH_18

#print axioms Philosophy.ETH_18.bounded_duty
#print axioms Philosophy.ETH_18.beyond_supererogatory
