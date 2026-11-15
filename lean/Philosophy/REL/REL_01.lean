/-
REL-01 · On the Existence of God
Formalization of the main argument (Volume I, Chapter 3, Theorem 3.4).

Framework. Possible-worlds semantics with a constant domain of beings and an
accessibility relation assumed to be an equivalence relation (system S5).
Propositions are predicates on worlds; necessity and possibility are the
usual box and diamond relative to accessibility.

What this file establishes. The conclusion "necessarily, a maximally great
being exists" follows from the possibility premise together with the S5
conditions on accessibility. It does not establish the possibility premise.
Volume III of the manuscript is devoted to that premise; see also the remark
at the end of this file, which records that the S5 framework validates the
converse argument with equal ease.
-/

namespace Philosophy.REL_01

/-! ## Modal framework -/

/-- Possible worlds. -/
axiom World : Type

/-- The actual world. -/
axiom actual : World

/-- Accessibility between worlds. -/
axiom R : World → World → Prop

/-- Assumption 2.1 (S5), clause (i): accessibility is reflexive. -/
axiom R_refl : ∀ w, R w w

/-- Assumption 2.1 (S5), clause (ii): accessibility is symmetric. -/
axiom R_symm : ∀ {w v}, R w v → R v w

/-- Assumption 2.1 (S5), clause (iii): accessibility is transitive. -/
axiom R_trans : ∀ {w v u}, R w v → R v u → R w u

/-- Propositions, construed as sets of worlds. -/
abbrev WProp := World → Prop

/-- Necessity: truth at every accessible world. -/
def Box (p : WProp) : WProp := fun w => ∀ v, R w v → p v

/-- Possibility: truth at some accessible world. -/
def Dia (p : WProp) : WProp := fun w => ∃ v, R w v ∧ p v

/-! ## Beings and maximal greatness -/

/-- Beings (constant domain). -/
axiom Being : Type

/-- `Exists x w`: the being `x` exists at world `w`. -/
axiom Exists : Being → WProp

/-- `MaximallyExcellent x w`: `x` is omnipotent, omniscient and morally
perfect at `w` (Definition 2.2). -/
axiom MaximallyExcellent : Being → WProp

/-- Definition 2.4. A being is maximally great at `w` if it exists and is
maximally excellent at every world accessible from `w`. -/
def MaximallyGreat (x : Being) : WProp :=
  Box (fun v => Exists x v ∧ MaximallyExcellent x v)

/-- "Some maximally great being exists." -/
def SomeMaximallyGreat : WProp := fun w => ∃ x, MaximallyGreat x w

/-! ## The premise -/

/-- Assumption 3.1 (the possibility premise): at the actual world, it is
possible that a maximally great being exists. -/
axiom possibility_premise : Dia SomeMaximallyGreat actual

/-! ## The argument -/

/-- Lemma 3.3. The characteristic principle of S5: whatever is possibly
necessary is necessary. -/
theorem dia_box_implies_box (p : WProp) (w : World) :
    Dia (Box p) w → Box p w := by
  intro ⟨v, hwv, hv⟩ u hwu
  exact hv u (R_trans (R_symm hwv) hwu)

/-- Lemma 3.2. In S5, maximal greatness is necessary if it is possible. -/
theorem maximal_greatness_rigid {x : Being} {w v : World}
    (hwv : R w v) (h : MaximallyGreat x v) : Box (MaximallyGreat x) w := by
  intro u hwu u' huu'
  have hvu : R v u := R_trans (R_symm hwv) hwu
  exact h u' (R_trans hvu huu')

/-- Theorem 3.4 (main result). Necessarily, a maximally great being exists. -/
theorem necessary_existence : Box SomeMaximallyGreat actual := by
  intro u hu
  obtain ⟨v, hv, x, hx⟩ := possibility_premise
  exact ⟨x, maximal_greatness_rigid hv hx u hu⟩

/-- Corollary 3.5. A maximally great being exists, and is maximally
excellent, at the actual world. -/
theorem actual_existence :
    ∃ x, Exists x actual ∧ MaximallyExcellent x actual := by
  obtain ⟨x, hx⟩ := necessary_existence actual (R_refl actual)
  exact ⟨x, hx actual (R_refl actual)⟩

/-! ## Remark: the converse argument

The S5 framework is symmetric. Replacing the possibility premise by the
premise that it is possible that no maximally great being exists yields,
by an equally short proof, that no maximally great being exists. The
formal argument therefore transfers the whole weight of the question to
the choice between the two possibility premises. This is the subject of
Volume III. The converse premise is stated here as a hypothesis, not as an
axiom.
-/

/-- Proposition 4.1. The converse argument. -/
theorem converse_argument
    (h : Dia (fun w => ¬ SomeMaximallyGreat w) actual) :
    ¬ SomeMaximallyGreat actual := by
  intro ⟨x, hx⟩
  obtain ⟨v, hv, hnot⟩ := h
  exact hnot ⟨x, maximal_greatness_rigid (R_refl actual) hx v hv⟩

end Philosophy.REL_01

#print axioms Philosophy.REL_01.necessary_existence
#print axioms Philosophy.REL_01.actual_existence
#print axioms Philosophy.REL_01.converse_argument
