/-
REL-11 · Asymmetric Steadfastness in Religious Disagreement
Formalization of Theorems 3.1 and 3.2 and Corollary 3.3.

Two parties to a peer disagreement (Definition 2.1) share their total
evidence; `RationalCred x` says that credence `x` is rational on that shared
evidence. Steadfastness is rational for a party iff her credence is rational
on the shared evidence (Definition 2.2). `K i φ` says that party `i` is in a
position to know `φ`.

What this file establishes. Given uniqueness (Principle P1) and that the
credences differ, steadfastness is rational for at most one party (Theorem
3.1). Given also factivity (Assumption 2.3) and symmetry (Assumption 2.5),
neither party is in a position to know of either party that her credence is
the rational one (Theorem 3.2), hence neither is in a position to know that
her own steadfastness is rational (Corollary 3.3).

What it does not establish. Uniqueness, symmetry, or that steadfastness is in
fact rational for either party (Remark 3.4).
-/

namespace Philosophy.REL_11

/-- The two parties. -/
inductive Party
  | A | B
  deriving DecidableEq

/-- Credences. -/
axiom Credence : Type

/-- Each party's credence in the disputed proposition after disclosure. -/
axiom cred : Party → Credence

/-- `RationalCred x`: credence `x` is rational on the shared total evidence. -/
axiom RationalCred : Credence → Prop

/-- Principle P1 (uniqueness). At most one credence is rational on the
shared evidence. -/
axiom uniqueness : ∀ x y : Credence, RationalCred x → RationalCred y → x = y

/-- Definition 2.1. In a peer disagreement the credences differ. -/
axiom disagree : cred .A ≠ cred .B

/-- Definition 2.2. Steadfastness is rational for `i` iff `i`'s credence is
rational on the shared evidence. This is `R_A`, `R_B` in the manuscript. -/
def Rational (i : Party) : Prop := RationalCred (cred i)

/-- Position to know. -/
axiom K : Party → Prop → Prop

/-- Assumption 2.3 (factivity). -/
axiom factive : ∀ (i : Party) (φ : Prop), K i φ → φ

/-- Assumption 2.4 (shared evidence). -/
axiom shared : ∀ φ : Prop, K .A φ ↔ K .B φ

/-- Assumption 2.5 (symmetry). -/
axiom symmetry : ∀ i : Party, K i (Rational .A) ↔ K i (Rational .B)

/-- Theorem 3.1 (at most one). -/
theorem at_most_one : ¬ (Rational .A ∧ Rational .B) :=
  fun ⟨ha, hb⟩ => disagree (uniqueness _ _ ha hb)

/-- Theorem 3.2 (neither knows which). -/
theorem neither_knows (i : Party) :
    ¬ K i (Rational .A) ∧ ¬ K i (Rational .B) := by
  have hA : ¬ K i (Rational .A) := fun h =>
    at_most_one ⟨factive i _ h, factive i _ ((symmetry i).mp h)⟩
  exact ⟨hA, fun h => hA ((symmetry i).mpr h)⟩

/-- Corollary 3.3. Neither party is in a position to know that her own
steadfastness is rational. -/
theorem not_entitled (i : Party) : ¬ K i (Rational i) := by
  cases i
  · exact (neither_knows .A).1
  · exact (neither_knows .B).2

/-- Assumption 2.4 at work: the two parties' positions coincide, so what one
cannot know about the disagreement the other cannot know either. -/
theorem positions_coincide (φ : Prop) : ¬ K .A φ ↔ ¬ K .B φ :=
  ⟨fun h hb => h ((shared φ).mpr hb), fun h ha => h ((shared φ).mp ha)⟩

end Philosophy.REL_11

#print axioms Philosophy.REL_11.at_most_one
#print axioms Philosophy.REL_11.neither_knows
#print axioms Philosophy.REL_11.not_entitled
