/-
LOG-18 · What the Tortoise Said to Achilles, Revisited
Formalization of Proposition 3.1, Theorem 3.2 and Proposition 3.3.

A derivation system is given by a set of premises and a set of rules
(Definition 2.1). Here there is one possible rule, modus ponens, which is
either present or absent. The Tortoise's sequence of premise sets
(Definition 2.2) begins with A and A → Z and adds, at each stage, the
conditional whose antecedent is the conjunction of everything so far and
whose consequent is Z.

What this file establishes. Without a rule, what is derivable from a set of
premises is exactly the set of premises (Proposition 3.1); hence Z is
derivable at no stage of the Tortoise's sequence (Theorem 3.2). With modus
ponens as a rule, Z is derivable from the first two premises in one step
(Proposition 3.3). The regress is an artefact of treating the rule as a
premise. The file contains no philosophical axioms: the distinction between
premises and rules is built into the definition of derivability, which is
the point the manuscript defends. It does not establish that modus ponens
is justified; on that question see EPI-03.
-/

namespace Philosophy.LOG_18

/-- Formulas: atoms, conjunctions, conditionals. -/
inductive Formula where
  | atom : Nat → Formula
  | conj : Formula → Formula → Formula
  | imp : Formula → Formula → Formula
  deriving DecidableEq

/-- Definition 2.1. Derivability from premises Γ, with modus ponens as a rule
iff `mpRule = true`. -/
inductive Deriv (mpRule : Bool) (Γ : List Formula) : Formula → Prop where
  | prem {A : Formula} : A ∈ Γ → Deriv mpRule Γ A
  | mp {A B : Formula} : mpRule = true → Deriv mpRule Γ A →
      Deriv mpRule Γ (.imp A B) → Deriv mpRule Γ B

/-- The atoms A and Z of Carroll's dialogue. -/
def A : Formula := .atom 0
def Z : Formula := .atom 1

/-- The conjunction of a list of premises. -/
def conjAll : List Formula → Formula
  | [] => A
  | [x] => x
  | x :: xs => .conj x (conjAll xs)

/-- Definition 2.2. The Tortoise's premise sets: stage 0 is [A, A → Z]; each
later stage adds the conditional "if all of the above, then Z". -/
def tortoise : Nat → List Formula
  | 0 => [A, .imp A Z]
  | n + 1 => tortoise n ++ [.imp (conjAll (tortoise n)) Z]

/-- Proposition 3.1. Without rules, the derivable formulas are the premises. -/
theorem no_rule_only_premises (Γ : List Formula) (B : Formula) :
    Deriv false Γ B ↔ B ∈ Γ := by
  constructor
  · intro h
    cases h with
    | prem hm => exact hm
    | mp hr _ _ => exact absurd hr (by decide)
  · exact Deriv.prem

/-- Z is never among the Tortoise's premises: every premise after A is a
conditional. -/
theorem Z_not_premise : ∀ n, Z ∉ tortoise n := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [tortoise, List.mem_append, List.mem_singleton, not_or]
    exact ⟨ih, by simp [Z]⟩

/-- Theorem 3.2 (the regress). At no stage of the Tortoise's sequence is Z
derivable without a rule of inference. -/
theorem regress (n : Nat) : ¬ Deriv false (tortoise n) Z := by
  rw [no_rule_only_premises]
  exact Z_not_premise n

/-- Proposition 3.3. With modus ponens as a rule, Z follows from the first
two premises in one step. -/
theorem rule_suffices : Deriv true (tortoise 0) Z :=
  Deriv.mp (A := A) rfl (Deriv.prem (by decide)) (Deriv.prem (by decide))

end Philosophy.LOG_18

#print axioms Philosophy.LOG_18.regress
#print axioms Philosophy.LOG_18.rule_suffices
