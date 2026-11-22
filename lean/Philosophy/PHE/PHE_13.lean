/-
PHE-13 · The Infinite Demand of the Face
Formalization of Lemma 3.1, Theorem 3.2, Proposition 3.3, Theorem 3.4 and
Corollary 3.5.

What this file establishes. The demand of the face is modelled as a sequence
of claims indexed by the natural numbers (Assumption 2.4), and a discharge as
a finite list of answered claims (Definition 2.2). No finite discharge
exhausts the demand (Lemma 3.1, purely arithmetical). Given that every claim
binds (Assumption 2.5, stated with no premise about dischargeability), every
discharge leaves a binding claim unanswered (Theorem 3.2), and the holistic
ought-implies-can principle (Definition 2.8) is refuted (Proposition 3.3).
Given ought-implies-can for obligations (Assumption 2.7), some binding claims
are not obligations (Theorem 3.4): the infinite demand does not overload the
agent with obligations it cannot meet (Corollary 3.5).

What it does not establish. It does not establish that the face makes
claims, that each answer occasions a further claim, or that the claims bind;
these are the phenomenological premises defended in the manuscript. Nor does
it model the third party or the passage from the demand to justice
(Section 4).
-/

namespace Philosophy.PHE_13

/-- Definition 2.1. Claims that the other can make on me. -/
axiom Claim : Type

/-- Assumption 2.4 (unboundedness). The demand of the face is a sequence of
claims indexed by all natural numbers: each answer occasions a further
claim. -/
axiom claim : Nat → Claim

/-- Definition 2.2. A discharge answers finitely many claims of the demand,
listed by their indices. -/
abbrev Discharge := List Nat

/-- Definition 2.2. A discharge exhausts the demand if it answers every
claim. -/
def Exhausts (L : Discharge) : Prop := ∀ n, n ∈ L

/-- Auxiliary: the sum of a list of indices. -/
def total : List Nat → Nat
  | [] => 0
  | x :: xs => x + total xs

theorem le_total : ∀ (L : List Nat) (x : Nat), x ∈ L → x ≤ total L
  | [], _, h => by cases h
  | y :: ys, x, h => by
    cases h with
    | head => simp [total]
    | tail _ h' =>
      have := le_total ys x h'
      simp [total]; omega

/-- Lemma 3.1. No finite discharge exhausts the demand (Definition 2.3: the
demand is infinite). -/
theorem not_exhausted (L : Discharge) : ∃ n, ¬ (n ∈ L) :=
  ⟨total L + 1, fun h => by have := le_total L _ h; omega⟩

theorem no_exhaustion : ¬ ∃ L : Discharge, Exhausts L :=
  fun ⟨L, hL⟩ => match not_exhausted L with
    | ⟨n, hn⟩ => hn (hL n)

/-- Normative force: the claim binds the one to whom it is addressed. -/
axiom Binding : Claim → Prop

/-- Assumption 2.5 (normative force). Every claim of the demand binds. The
assumption has no premise about whether the claim, or the demand, can be
discharged. -/
axiom binding : ∀ n, Binding (claim n)

/-- Theorem 3.2 (main result). The demand is infinite and binding: every
discharge leaves some binding claim unanswered. -/
theorem infinite_binding_demand (L : Discharge) :
    ∃ n, Binding (claim n) ∧ ¬ (n ∈ L) :=
  match not_exhausted L with
  | ⟨n, hn⟩ => ⟨n, binding n, hn⟩

/-- Definition 2.8. Holistic ought-implies-can: if every claim of the demand
binds, some discharge exhausts it. -/
def HolisticOIC : Prop :=
  (∀ n, Binding (claim n)) → ∃ L : Discharge, Exhausts L

/-- Proposition 3.3. Holistic ought-implies-can is false. -/
theorem holistic_oic_fails : ¬ HolisticOIC :=
  fun h => no_exhaustion (h binding)

/-- Definition 2.6. `Obligated n`: answering claim `n` is obligatory, i.e.
failing to answer it is a fault. -/
axiom Obligated : Nat → Prop

/-- Assumption 2.7 (ought implies can, for obligations). Some single
discharge answers every obligatory claim. -/
axiom oic : ∃ L : Discharge, ∀ n, Obligated n → n ∈ L

/-- Theorem 3.4. Not every binding claim is an obligation. -/
theorem binding_not_obligated : ∃ n, Binding (claim n) ∧ ¬ Obligated n :=
  match oic with
  | ⟨L, hL⟩ => match not_exhausted L with
    | ⟨n, hn⟩ => ⟨n, binding n, fun ho => hn (hL n ho)⟩

/-- Corollary 3.5 (no overload). Some discharge meets every obligation, and
every such discharge still leaves a binding claim unanswered. -/
theorem no_overload :
    (∃ L : Discharge, ∀ n, Obligated n → n ∈ L) ∧
    ∀ L : Discharge, ∃ m, Binding (claim m) ∧ ¬ (m ∈ L) :=
  ⟨oic, infinite_binding_demand⟩

end Philosophy.PHE_13

#print axioms Philosophy.PHE_13.infinite_binding_demand
#print axioms Philosophy.PHE_13.holistic_oic_fails
#print axioms Philosophy.PHE_13.binding_not_obligated
#print axioms Philosophy.PHE_13.no_overload
