/-
LNG-10 · Deflationism Defended
Formalization of Theorem 3.1 and Propositions 3.2 and 3.3.

Sentences of a language and worlds are primitive (Definition 2.1). What a
sentence says obtains or fails at each world; this is the relation `holds`,
fixed by the meaning of the sentence and the way the world is, without any
appeal to truth. The truth predicate is a further primitive, governed by the
equivalence schema (Principle P1), here for the fragment of the language
that does not itself contain the truth predicate.

What this file establishes. The equivalence schema determines the truth
predicate completely: any two predicates that satisfy it are the same
predicate (Theorem 3.1). Generalizations over sentences by means of the
truth predicate are equivalent to generalizations over what the sentences
say, which is the expressive role of truth (Proposition 3.2). Whatever is
true of truth is true of the relation of saying what obtains, so that a
property alleged to explain truth adds nothing to the schema
(Proposition 3.3).

What it does not establish. It does not establish the equivalence schema,
nor that it holds for sentences that contain the truth predicate; the
treatment of those sentences is that of LOG-01, where the schema holds in a
non-classical logic. It does not establish the conservativeness of the
deflationary theory of truth, which is the subject of the companion
manuscript LNG-10-b.
-/

namespace Philosophy.LNG_10

/-- Definition 2.1. Sentences of the truth-free fragment of a language. -/
axiom Sentence : Type

/-- Definition 2.1. Worlds. -/
axiom World : Type

/-- Definition 2.1. What a sentence says obtains at a world. -/
axiom holds : World → Sentence → Prop

/-- The truth predicate, relativized to worlds. -/
axiom True' : World → Sentence → Prop

/-- Principle P1 (equivalence schema). At every world, a sentence is true
if and only if what it says obtains. -/
axiom equivalence : ∀ w s, True' w s ↔ holds w s

/-- Theorem 3.1. The equivalence schema fixes the truth predicate: any
predicate satisfying it is the truth predicate. -/
theorem schema_determines (T : World → Sentence → Prop)
    (hT : ∀ w s, T w s ↔ holds w s) : T = True' := by
  funext w s
  exact propext ((hT w s).trans (equivalence w s).symm)

/-- Proposition 3.2. Generalizing with the truth predicate over any
collection of sentences is equivalent to generalizing over what they say. -/
theorem generalization (w : World) (X : Sentence → Prop) :
    (∀ s, X s → True' w s) ↔ (∀ s, X s → holds w s) :=
  ⟨fun h s hs => (equivalence w s).mp (h s hs),
   fun h s hs => (equivalence w s).mpr (h s hs)⟩

/-- Proposition 3.3. Any condition satisfied by the truth predicate is
satisfied by the relation of saying what obtains, and conversely. -/
theorem no_surplus (Φ : (World → Sentence → Prop) → Prop) :
    Φ True' ↔ Φ holds := by
  rw [schema_determines holds (fun _ _ => Iff.rfl)]

end Philosophy.LNG_10

#print axioms Philosophy.LNG_10.schema_determines
#print axioms Philosophy.LNG_10.no_surplus
