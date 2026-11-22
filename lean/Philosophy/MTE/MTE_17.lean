/-
MTE-17 · The Collapse of Quasi-Realism
Formalization of Theorem 4.1 and Proposition 4.2.

Properties are primitive and have extensions (which acts have them at
which worlds). Wrongness is the minimal property expressed by "wrong";
ideal disapproval is the property of being an act for blaming which an
improved sensibility would be. The background assumptions are
deflationist: correctness of a judgment is the truth of its content
(Assumption 3.1), truth obeys the equivalence schema (Assumption 3.2),
and minimal properties are individuated by their extensions across
worlds (Assumption 3.3).

Quasi-realism, with its explanatory commitments explicit, is the
conjunction of the fallibility commitment (a judgment that an act is
wrong is correct exactly when an improved sensibility would be for
blaming for it: Definition 3.4, clause (Q1)) and the explanatory
commitment (the standard of improvement is characterized without moral
vocabulary, so that ideal disapproval is a natural property: clause
(Q2)). Realism, in the form of MTE-01, is the conjunction of the theses
that wrongness is ideal disapproval (R1) and that wrongness is a natural
property (R2) (Definition 3.5).

What this file establishes. Given the three background assumptions,
quasi-realism so explicated and realism so stated are equivalent
(Theorem 4.1). If the standard of improvement is not natural, the
explanatory commitment fails (Proposition 4.2).

What it does not establish. It does not establish that the quasi-realist
is committed to (Q1) and (Q2): that is argued in Section 2 of the
manuscript. It does not establish deflationism (LNG-10) or the
coarse individuation of minimal properties, which are assumptions.
-/

namespace Philosophy.MTE_17

/-- Primitive: act types. -/
axiom Act : Type

/-- Primitive: possible worlds. -/
axiom World : Type

/-- Primitive: properties of acts. -/
axiom Property : Type

/-- Primitive: `Has P a w`: act `a` has property `P` at world `w`. -/
axiom Has : Property → Act → World → Prop

/-- Primitive: the minimal property expressed by "wrong". -/
axiom wrongness : Property

/-- Primitive: being an act for blaming which an improved sensibility
would be. -/
axiom idealDisapproval : Property

/-- Primitive: being a natural property. -/
axiom Natural : Property → Prop

/-- Primitive: the content of the judgment that `a` is wrong is true
at `w`. -/
axiom TrueWrong : Act → World → Prop

/-- Primitive: the judgment that `a` is wrong is correct at `w`. -/
axiom Correct : Act → World → Prop

/-- Assumption 3.1 (Correctness as truth). A judgment is correct exactly
when its content is true. -/
axiom correct_iff_true : ∀ a w, Correct a w ↔ TrueWrong a w

/-- Assumption 3.2 (Equivalence schema). It is true that `a` is wrong
exactly when `a` is wrong. -/
axiom equivalence_schema : ∀ a w, TrueWrong a w ↔ Has wrongness a w

/-- Assumption 3.3 (Coarse individuation). Minimal properties with the
same extension at every world are identical. -/
axiom coarse : ∀ P Q : Property,
    (∀ a w, Has P a w ↔ Has Q a w) → P = Q

/-- Definition 3.4. Quasi-realism with its explanatory commitments
explicit. -/
def QuasiRealism : Prop :=
  (∀ a w, Correct a w ↔ Has idealDisapproval a w) ∧ Natural idealDisapproval

/-- Definition 3.5. Realism, in the form of MTE-01. -/
def Realism : Prop :=
  wrongness = idealDisapproval ∧ Natural wrongness

/-- Theorem 4.1 (main result). Quasi-realism with its explanatory
commitments explicit is equivalent to realism. -/
theorem collapse : QuasiRealism ↔ Realism := by
  constructor
  · intro ⟨q1, q2⟩
    have hid : wrongness = idealDisapproval := by
      apply coarse
      intro a w
      rw [← equivalence_schema, ← correct_iff_true]
      exact q1 a w
    exact ⟨hid, hid ▸ q2⟩
  · intro ⟨r1, r2⟩
    refine ⟨?_, r1 ▸ r2⟩
    intro a w
    rw [correct_iff_true, equivalence_schema, r1]

/-- Proposition 4.2. If the standard of improvement is not natural, the
explanatory commitment of quasi-realism fails. -/
theorem moralized_standard (h : ¬ Natural idealDisapproval) : ¬ QuasiRealism :=
  fun q => h q.2

end Philosophy.MTE_17

#print axioms Philosophy.MTE_17.collapse
#print axioms Philosophy.MTE_17.moralized_standard
