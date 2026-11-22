/-
LOG-03 · Against Dialetheism
Formalization of Lemma 3.1, Theorems 3.2 and 3.3, and Propositions 3.4–3.6.

Sentences are evaluated in the three values 0, 1, 2 shared by the strong
Kleene logic K3 and the logic of paradox LP (Definition 2.1): negation is
`2 - x`, conjunction `min`, disjunction `max`. The two logics differ only in
which values are designated (Definition 2.2). The designated values are an
unknown set, constrained by two premises: truth is designated (Assumption
2.3) and a sentence and its negation are not both designated (Assumption
2.4, Exclusion). The dialetheist's cases are sentences that have the same
value as their negations (Assumption 2.5, Symmetry).

What this file establishes. Given Normality and Exclusion, only the value 2
is designated; no contradiction is true under any valuation; each of the
dialetheist's cases takes the middle value and is neither true nor false (a
gap). With the gap designation, modus ponens for the material conditional
holds; with the LP designation it fails. The gap and glut readings are dual.
It does not establish Exclusion, which the dialetheist denies and which
Section 4 of the manuscript defends.
-/

namespace Philosophy.LOG_03

/-- Definition 2.1. Formulas of the propositional language. -/
inductive Formula where
  | atom : Nat → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula

/-- Definition 2.1. Three-valued evaluation (shared by K3 and LP). Atoms are
capped at 2 so that every valuation is admissible. -/
def eval (v : Nat → Nat) : Formula → Nat
  | .atom n => min 2 (v n)
  | .neg A => 2 - eval v A
  | .conj A B => min (eval v A) (eval v B)
  | .disj A B => max (eval v A) (eval v B)

theorem eval_le (v : Nat → Nat) (A : Formula) : eval v A ≤ 2 := by
  induction A with
  | atom n => simp only [eval]; omega
  | neg A _ => simp only [eval]; omega
  | conj A B ihA _ => simp only [eval]; omega
  | disj A B ihA ihB => simp only [eval]; omega

/-- Definition 2.2. The designated values: those at which a sentence is true. -/
axiom Designated : Nat → Prop

/-- Assumption 2.3 (Normality). Full truth is designated. -/
axiom normality : Designated 2

/-- Assumption 2.4 (Exclusion). A sentence and its negation are not both true. -/
axiom exclusion : ∀ x, x ≤ 2 → ¬ (Designated x ∧ Designated (2 - x))

/-- The dialetheist's cases (the liar, Russell's set, instants of change, ...). -/
axiom Case : Type

/-- The value a case receives. -/
axiom value : Case → Nat

axiom value_le : ∀ c, value c ≤ 2

/-- Assumption 2.5 (Symmetry). In each case, a sentence and its negation have
the same value. -/
axiom symmetry : ∀ c, 2 - value c = value c

/-- Lemma 3.1. Only full truth is designated. -/
theorem designated_iff (x : Nat) (hx : x ≤ 2) : Designated x ↔ x = 2 := by
  constructor
  · intro hd
    apply Classical.byContradiction
    intro hne
    have h01 : x = 0 ∨ x = 1 := by omega
    cases h01 with
    | inl h0 =>
      subst h0
      exact exclusion 2 (Nat.le_refl 2) ⟨normality, hd⟩
    | inr h1 =>
      subst h1
      exact exclusion 1 (by decide) ⟨hd, hd⟩
  · intro h; subst h; exact normality

/-- Theorem 3.2. No contradiction is true: under every valuation,
`A ∧ ¬A` is undesignated. -/
theorem no_true_contradiction (v : Nat → Nat) (A : Formula) :
    ¬ Designated (eval v (.conj A (.neg A))) := by
  intro hd
  have hle := eval_le v (.conj A (.neg A))
  have h := (designated_iff _ hle).mp hd
  have := eval_le v A
  simp only [eval] at h
  omega

/-- Theorem 3.3. Every one of the dialetheist's cases takes the middle value
and is a gap: neither it nor its negation is true. -/
theorem cases_are_gaps (c : Case) :
    value c = 1 ∧ ¬ Designated (value c) ∧ ¬ Designated (2 - value c) := by
  have hs := symmetry c
  have hl := value_le c
  have h1 : value c = 1 := by omega
  refine ⟨h1, ?_, ?_⟩
  · intro hd; have := (designated_iff _ hl).mp hd; omega
  · intro hd; have := (designated_iff _ (by omega)).mp hd; omega

/-- Proposition 3.4. Under the gap designation, modus ponens for the material
conditional `¬A ∨ B` holds. -/
theorem gap_modus_ponens (v : Nat → Nat) (A B : Formula)
    (hA : Designated (eval v A)) (hAB : Designated (eval v (.disj (.neg A) B))) :
    Designated (eval v B) := by
  have hA' := (designated_iff _ (eval_le v A)).mp hA
  have hAB' := (designated_iff _ (eval_le v (.disj (.neg A) B))).mp hAB
  have hB := eval_le v B
  apply (designated_iff _ hB).mpr
  simp only [eval] at hAB'
  omega

/-- Proposition 3.5. Under the LP designation (values ≥ 1), modus ponens for
the material conditional fails. -/
theorem lp_modus_ponens_fails :
    ∃ v : Nat → Nat, 1 ≤ eval v (.atom 0) ∧
      1 ≤ eval v (.disj (.neg (.atom 0)) (.atom 1)) ∧ eval v (.atom 1) < 1 :=
  ⟨fun n => if n = 0 then 1 else 0, by decide⟩

/-- Proposition 3.6 (duality). `A` entails `B` on the gap reading iff `¬B`
entails `¬A` on the glut reading. -/
theorem duality (A B : Formula) :
    (∀ v, eval v A = 2 → eval v B = 2) ↔
      (∀ v, 1 ≤ eval v (.neg B) → 1 ≤ eval v (.neg A)) := by
  constructor
  · intro h v hB
    have := h v
    have := eval_le v A
    have := eval_le v B
    simp only [eval] at hB ⊢
    omega
  · intro h v hA
    have hv := h v
    have := eval_le v A
    have := eval_le v B
    simp only [eval] at hv
    omega

end Philosophy.LOG_03

#print axioms Philosophy.LOG_03.no_true_contradiction
#print axioms Philosophy.LOG_03.cases_are_gaps
