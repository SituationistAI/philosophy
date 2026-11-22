/-
LNG-17 · Structured Propositions
Formalization of Lemma 4.1, Theorem 4.2, Proposition 4.3, Corollary 4.4,
Propositions 6.2 and 6.3 and Theorem 7.1.

A language is given by a type of sentences and a function assigning to each
sentence the proposition it expresses (Definition 3.1); for a
context-sensitive language the sentences are sentence-context pairs. Sets of
sentences are objects (Assumption 3.3), and for every object there is a
singular proposition that has it as a constituent (Assumption 3.4).
Principle P1 says that structured propositions with different constituents
are different; here it appears as the injectivity of the map from objects to
their singular propositions, and Assumption 3.3 includes the extensionality
of sets of sentences.

What this file establishes. For the language described by the axioms, some
proposition is expressed by no sentence (Theorem 4.2), while every sentence
can be sent injectively to a proposition (Proposition 4.3); so there are
strictly more propositions than sentences (Corollary 4.4). The diagonal
argument behind this is stated as a theorem about arbitrary types
(Lemma 4.1), which is why the result holds for any language whatever,
including languages with uncountably many sentences. Structured propositions
can differ while being true at exactly the same possible worlds
(Proposition 6.2), and the contents defined from them over arbitrary points,
including impossible ones, are exactly as fine-grained as the propositions
themselves (Proposition 6.3). No map from collections of propositions into
propositions is injective (Theorem 7.1, the Russell-Myhill limit), so
Principle P1 cannot be extended to treat arbitrary collections of
propositions as constituents.

What it does not establish. It does not establish Principle P1 or
Assumptions 3.3 and 3.4, which carry the philosophical weight and are
defended in the manuscript; nor that propositions are abstract, which the
manuscript infers from Corollary 4.4 together with further premises
(Section 5).
-/

namespace Philosophy.LNG_17

/-! ## The diagonal lemma, for arbitrary types -/

/-- Lemma 4.1 (Cantor). If collections of members of `S` can be sent
injectively into `P`, then no map from `S` to `P` reaches every member of
`P`. -/
theorem diagonal {S P : Type} (i : (S → Prop) → P)
    (hi : ∀ X Y, i X = i Y → X = Y) (e : S → P) : ∃ p, ∀ s, e s ≠ p := by
  let D : S → Prop := fun s => ¬ ∃ X, e s = i X ∧ X s
  refine ⟨i D, fun s hs => ?_⟩
  have key : D s ↔ ¬ D s := by
    constructor
    · intro hD hD'
      exact hD ⟨D, hs, hD'⟩
    · intro hnD ⟨X, hX, hXs⟩
      have hXD : X = D := hi X D (hX.symm.trans hs)
      exact hnD (hXD ▸ hXs)
  have hn : ¬ D s := fun h => key.mp h h
  exact hn (key.mpr hn)

/-! ## The framework -/

/-- Propositions. -/
axiom Proposition : Type

/-- Definition 3.1. The sentences of an arbitrary language (for a
context-sensitive language, sentence-context pairs). -/
axiom Sentence : Type

/-- Definition 3.1. The proposition expressed by a sentence. -/
axiom expresses : Sentence → Proposition

/-- Objects that can be constituents of propositions. -/
axiom Obj : Type

/-- Assumption 3.3. Every collection of sentences has a set, which is an
object. -/
axiom setOf : (Sentence → Prop) → Obj

/-- Assumption 3.3 (extensionality). Sets with different members are
different objects. -/
axiom setOf_ext : ∀ X Y, setOf X = setOf Y → X = Y

/-- Assumption 3.4. For every object there is a singular proposition having
it as a constituent (for instance, the proposition that it exists). -/
axiom singular : Obj → Proposition

/-- Principle P1 (structure). Singular propositions with different
constituents are different propositions. -/
axiom structure_principle : ∀ a b, singular a = singular b → a = b

/-! ## The cardinality argument -/

/-- Theorem 4.2. Some proposition is expressed by no sentence of the
language. -/
theorem inexpressible : ∃ p : Proposition, ∀ s : Sentence, expresses s ≠ p :=
  diagonal (fun X => singular (setOf X))
    (fun X Y h => setOf_ext X Y (structure_principle _ _ h)) expresses

/-- Proposition 4.3. Distinct sentences can be sent to distinct
propositions: the singular propositions about their unit sets. -/
theorem sentences_embed :
    ∃ f : Sentence → Proposition, ∀ s t, f s = f t → s = t := by
  refine ⟨fun s => singular (setOf (fun x => x = s)), fun s t h => ?_⟩
  have h1 := setOf_ext _ _ (structure_principle _ _ h)
  have h2 : (fun x => x = s) t = (fun x => x = t) t := by rw [h1]
  exact (h2.mpr rfl).symm

/-- Corollary 4.4. There are strictly more propositions than sentences:
sentences embed in propositions, and no assignment of propositions to
sentences reaches them all. -/
theorem more_propositions :
    (∃ f : Sentence → Proposition, ∀ s t, f s = f t → s = t) ∧
    ∀ g : Sentence → Proposition, ∃ p, ∀ s, g s ≠ p :=
  ⟨sentences_embed, fun g =>
    diagonal (fun X => singular (setOf X))
      (fun X Y h => setOf_ext X Y (structure_principle _ _ h)) g⟩

/-! ## Fine grain -/

/-- Definition 6.1. Structured propositions of a simple propositional
language: atomic propositions, negations and conjunctions. -/
inductive SProp where
  | atom : Nat → SProp
  | neg : SProp → SProp
  | conj : SProp → SProp → SProp
  deriving DecidableEq

/-- Truth of a structured proposition at a possible world, a valuation of
the atoms. -/
def holds (w : Nat → Bool) : SProp → Bool
  | .atom n => w n
  | .neg p => !holds w p
  | .conj p q => holds w p && holds w q

/-- Proposition 6.2. Structured propositions can differ while being true at
exactly the same possible worlds. -/
theorem finer_than_intension :
    SProp.conj (.atom 0) (.atom 1) ≠ SProp.conj (.atom 1) (.atom 0) ∧
    ∀ w, holds w (.conj (.atom 0) (.atom 1)) = holds w (.conj (.atom 1) (.atom 0)) := by
  refine ⟨by decide, fun w => ?_⟩
  simp only [holds]
  cases w 0 <;> cases w 1 <;> rfl

/-- Proposition 6.3. Let points of evaluation be arbitrary collections of
propositions (worlds as in TSM-07, impossible ones included as in TSM-09),
and let a proposition be true at a point when it belongs to it. Then the
content of a proposition, the collection of points at which it is true,
determines the proposition. -/
theorem contents_as_fine {P : Type} (p q : P)
    (h : (fun w : P → Prop => w p) = (fun w : P → Prop => w q)) : p = q := by
  have h' : (fun x => x = p) p = (fun x => x = p) q := congrFun h (fun x => x = p)
  exact (h'.mp rfl).symm

/-! ## The Russell-Myhill limit -/

/-- Theorem 7.1 (Russell, Myhill). There is no injective map from
collections of propositions into propositions. Hence Principle P1 cannot
hold for propositions that have arbitrary collections of propositions as
constituents. -/
theorem russell_myhill {P : Type} (i : (P → Prop) → P) :
    ¬ ∀ X Y, i X = i Y → X = Y := by
  intro hi
  have ⟨p, hp⟩ := diagonal i hi (fun x => x)
  exact hp p rfl

end Philosophy.LNG_17

#print axioms Philosophy.LNG_17.more_propositions
#print axioms Philosophy.LNG_17.russell_myhill
