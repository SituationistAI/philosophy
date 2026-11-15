/-
LOG-07 · In Defence of the Material Conditional
Formalization of Theorem 3.1 and Propositions 3.2 and 3.3.

The conditional of logic is assumed to be a binary truth function
(Assumption 2.1). It is constrained by two principles that state its role
in deduction: modus ponens (Principle P1) and conditional proof
(Principle P2), the latter for sentences built from two atoms, evaluated
classically.

What this file establishes. Any truth-functional conditional satisfying
modus ponens and conditional proof is the material conditional; the
material conditional satisfies both, so the assumptions are consistent;
the so-called paradoxes of material implication follow from conditional
proof alone. It does not establish that the conditional of logic should be
truth-functional, nor anything about indicative conditionals in natural
language, which the manuscript (following LNG-20) treats separately.
-/

namespace Philosophy.LOG_07

/-- Definition 2.2. The material conditional. -/
def material (a b : Bool) : Bool := !a || b

/-- Valuations of two atoms p (first) and q (second). -/
abbrev Val := Bool × Bool

/-- Assumption 2.1 (Truth-functionality). The conditional of logic is a
binary truth function. -/
axiom cond : Bool → Bool → Bool

/-- Principle P1 (Modus ponens). A true conditional with a true antecedent
has a true consequent. -/
axiom modus_ponens : ∀ a b : Bool, a = true → cond a b = true → b = true

/-- Principle P2 (Conditional proof). If B is true at every valuation at
which A is true, then the conditional from A to B is true at every
valuation. -/
axiom conditional_proof : ∀ A B : Val → Bool,
  (∀ v, A v = true → B v = true) → ∀ v, cond (A v) (B v) = true

/-- Proposition 3.2 (part). Every conditional A → A is true. -/
theorem cond_refl (a : Bool) : cond a a = true :=
  conditional_proof (fun v => v.1) (fun v => v.1) (fun _ h => h) (a, false)

/-- Proposition 3.2 (part). A false antecedent makes a true conditional
(from p ∧ ¬p, q follows). -/
theorem cond_false_true : cond false true = true := by
  have h := conditional_proof (fun v => v.1 && !v.1) (fun v => v.2)
    (fun v hv => by cases h1 : v.1 <;> simp [h1] at hv) (false, true)
  simpa using h

/-- Theorem 3.1. The conditional of logic is the material conditional. -/
theorem material_unique : cond = material := by
  funext a b
  cases a <;> cases b
  · exact cond_refl false
  · exact cond_false_true
  · cases h : cond true false
    · rfl
    · exact absurd (modus_ponens true false rfl h) (by decide)
  · exact cond_refl true

/-- Proposition 3.3. The material conditional satisfies P1 and P2. -/
theorem material_satisfies :
    (∀ a b : Bool, a = true → material a b = true → b = true) ∧
    (∀ A B : Val → Bool, (∀ v, A v = true → B v = true) →
      ∀ v, material (A v) (B v) = true) := by
  constructor
  · intro a b ha h; subst ha; simpa [material] using h
  · intro A B h v
    cases hA : A v
    · simp [material]
    · simp [material, h v hA]

/-- Proposition 3.4. The paradoxes of material implication follow from
conditional proof alone: a false antecedent, or a true consequent, makes
the conditional true. -/
theorem paradoxes : (∀ b, cond false b = true) ∧ (∀ a, cond a true = true) := by
  constructor
  · intro b; cases b
    · exact cond_refl false
    · exact cond_false_true
  · intro a; cases a
    · exact cond_false_true
    · exact cond_refl true

end Philosophy.LOG_07

#print axioms Philosophy.LOG_07.material_unique
