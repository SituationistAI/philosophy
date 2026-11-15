/-
MET-03 · Realism by Parsimony
Formalization of Proposition 3.1, Lemma 3.2, Theorems 3.3 and 3.4,
Proposition 3.5 and Corollary 3.6.

The ideology of a theory is the set of its primitive notions
(Definition 2.1). Four notions are in play (Definition 2.2): experience,
structure, production and conception. Explanatory adequacy requires the first
three (Assumption 2.3). Realism uses exactly those three (Definition 2.4);
Berkeleyan idealism uses those three and conception (Definition 2.5). A theory
that asserts that structure depends on mind must have conception in its
ideology (Assumption 2.6). Both theories are adequate (Assumption 2.7), and
parsimony of ideology eliminates an adequate theory whose ideology properly
includes that of another adequate theory (Principle 1).

What this file establishes. The idealist clauses are jointly satisfiable
(Proposition 3.1, by an explicit model). Idealism has exactly one primitive
that realism lacks (Lemma 3.2). Idealism, and every adequate theory asserting
the mind-dependence of structure, is eliminated by parsimony (Theorems 3.3 and
3.4), while no adequate theory has an ideology properly included in that of
realism (Proposition 3.5, Corollary 3.6). It does not establish the
assumptions: in particular, that conception is not definable in the other
notions, and that parsimony of ideology is a guide to truth.
-/

namespace Philosophy.MET_03

/-! ## Consistency of idealism -/

/-- The clauses of the idealist theory (Definition 2.5), read as conditions on
a model: every structural state is conceived by some mind; one mind (God)
conceives every state and has no sensory experience; every experience had by
a mind is produced by some state; some state produces no experience that any
mind has (the unperceived tree); and some finite mind has an experience. -/
structure IdealistModel where
  Mind : Type
  State : Type
  Exp : Type
  conceives : Mind → State → Prop
  produces : State → Exp → Prop
  has : Mind → Exp → Prop
  god : Mind
  god_conceives_all : ∀ s, conceives god s
  god_not_sensory : ∀ e, ¬ has god e
  experiences_produced : ∀ m e, has m e → ∃ s, produces s e
  unperceived_state : ∃ s, ∀ e, produces s e → ∀ m, ¬ has m e
  finite_experience : ∃ m e, has m e

/-- Proposition 3.1. Idealism is consistent: its clauses have a model. -/
theorem idealism_consistent : Nonempty IdealistModel :=
  ⟨{ Mind := Bool, State := Bool, Exp := Unit,
     conceives := fun g _ => g = true,
     produces := fun s _ => s = true,
     has := fun m _ => m = false,
     god := true,
     god_conceives_all := fun _ => rfl,
     god_not_sensory := fun _ h => Bool.noConfusion h,
     experiences_produced := fun _ _ _ => ⟨true, rfl⟩,
     unperceived_state := ⟨false, fun _ h => Bool.noConfusion h⟩,
     finite_experience := ⟨false, (), rfl⟩ }⟩

/-! ## Ideology and parsimony -/

/-- Definition 2.2. The primitive notions in play. -/
inductive Notion where
  | experience
  | structural
  | production
  | conception
  deriving DecidableEq

open Notion

/-- Theories. -/
axiom Theory : Type

/-- Definition 2.1. `ideology T n`: the notion `n` is primitive in `T`. -/
axiom ideology : Theory → Notion → Prop

/-- Explanatory adequacy (Section 2). -/
axiom Adequate : Theory → Prop

/-- `MindDependent T`: `T` asserts that every structural state depends on
being conceived by a mind. -/
axiom MindDependent : Theory → Prop

/-- Elimination by parsimony. -/
axiom Eliminated : Theory → Prop

/-- Realism and idealism. -/
axiom realism : Theory
axiom idealism : Theory

/-- Assumption 2.3. Every adequate theory has experience, structure and
production among its primitives. -/
axiom adequacy_requires : ∀ T, Adequate T →
  ideology T experience ∧ ideology T structural ∧ ideology T production

/-- Definition 2.4. The ideology of realism. -/
axiom realism_ideology : ∀ n, ideology realism n ↔
  (n = experience ∨ n = structural ∨ n = production)

/-- Definition 2.5. The ideology of idealism. -/
axiom idealism_ideology : ∀ n, ideology idealism n ↔
  (n = experience ∨ n = structural ∨ n = production ∨ n = conception)

/-- Definition 2.5. Idealism asserts the mind-dependence of structure. -/
axiom idealism_mind_dependent : MindDependent idealism

/-- Assumption 2.6 (indefinability). A theory that asserts the
mind-dependence of structure has conception among its primitives. -/
axiom mind_dependence_needs_conception :
  ∀ T, MindDependent T → ideology T conception

/-- Assumption 2.7. Realism and idealism are both adequate. -/
axiom realism_adequate : Adequate realism
axiom idealism_adequate : Adequate idealism

/-- Principle 1 (parsimony of ideology). Of two adequate theories, one whose
ideology properly includes the other's is eliminated. -/
axiom parsimony : ∀ T U, Adequate T → Adequate U →
  (∀ n, ideology T n → ideology U n) →
  (∃ n, ideology U n ∧ ¬ ideology T n) → Eliminated U

/-- Realism's ideology is included in that of every adequate theory. -/
theorem realism_included (T : Theory) (h : Adequate T) :
    ∀ n, ideology realism n → ideology T n := by
  intro n hn
  obtain ⟨he, hs, hp⟩ := adequacy_requires T h
  rcases (realism_ideology n).mp hn with rfl | rfl | rfl
  · exact he
  · exact hs
  · exact hp

/-- Conception is not a primitive of realism. -/
theorem conception_not_realist : ¬ ideology realism conception := by
  intro h
  rcases (realism_ideology conception).mp h with h | h | h <;> cases h

/-- Lemma 3.2. Realism's ideology is included in idealism's, and conception
is the one and only notion primitive in idealism and not in realism. -/
theorem one_more_primitive :
    (∀ n, ideology realism n → ideology idealism n) ∧
    (∀ n, (ideology idealism n ∧ ¬ ideology realism n) ↔ n = conception) := by
  refine ⟨realism_included idealism idealism_adequate, fun n => ⟨?_, ?_⟩⟩
  · intro ⟨hi, hr⟩
    rcases (idealism_ideology n).mp hi with h | h | h | h
    · exact absurd ((realism_ideology n).mpr (Or.inl h)) hr
    · exact absurd ((realism_ideology n).mpr (Or.inr (Or.inl h))) hr
    · exact absurd ((realism_ideology n).mpr (Or.inr (Or.inr h))) hr
    · exact h
  · intro h
    subst h
    exact ⟨(idealism_ideology conception).mpr (Or.inr (Or.inr (Or.inr rfl))),
      conception_not_realist⟩

/-- Theorem 3.4. Every adequate theory that asserts the mind-dependence of
structure is eliminated by parsimony. -/
theorem mind_dependence_eliminated (T : Theory)
    (hT : Adequate T) (hm : MindDependent T) : Eliminated T :=
  parsimony realism T realism_adequate hT (realism_included T hT)
    ⟨conception, mind_dependence_needs_conception T hm, conception_not_realist⟩

/-- Theorem 3.3 (main result). Idealism is eliminated by parsimony. -/
theorem idealism_eliminated : Eliminated idealism :=
  mind_dependence_eliminated idealism idealism_adequate idealism_mind_dependent

/-- Proposition 3.5. No adequate theory has an ideology properly included in
realism's: an adequate theory whose ideology is included in realism's has
the same ideology. -/
theorem realism_minimal (T : Theory) (hT : Adequate T)
    (hsub : ∀ n, ideology T n → ideology realism n) :
    ∀ n, ideology T n ↔ ideology realism n :=
  fun n => ⟨hsub n, realism_included T hT n⟩

/-- Corollary 3.6. Realism is not dominated under Principle 1, and every
adequate theory asserting mind-dependence is dominated by realism. -/
theorem realism_undominated :
    (∀ T, Adequate T → ¬ ∃ n, ideology realism n ∧ ¬ ideology T n) ∧
    (∀ T, Adequate T → MindDependent T → Eliminated T) :=
  ⟨fun T hT ⟨n, hr, hn⟩ => hn (realism_included T hT n hr),
   mind_dependence_eliminated⟩

end Philosophy.MET_03

#print axioms Philosophy.MET_03.idealism_consistent
#print axioms Philosophy.MET_03.idealism_eliminated
#print axioms Philosophy.MET_03.realism_undominated
