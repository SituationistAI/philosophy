/-
PHE-20 · The Irreducible Residue
Formalization of Theorem 3.1, Theorem 3.2 and Corollary 3.3.

What this file establishes. Given that no act of bracketing brackets itself
(Assumption 2.2, residue), that every act can be bracketed by a further act
of reflection (Assumption 2.3, iteration), and that whatever persists across
acts can be bracketed by some act (Assumption 2.4, transcendence of the
persisting), every reduction leaves its own act unbracketed; nothing that
persists across acts survives every reduction; and the residue of each act,
when bracketed by a later reflection, is replaced by the residue of that
reflection.

What it does not establish. It does not establish the three assumptions,
which the manuscript defends, nor that the residue is given in reflection;
that is a phenomenological claim that the model does not represent.
-/

namespace Philosophy.PHE_20

/-- Items that can fall under a bracketing: objects, states, acts. -/
axiom Item : Type

/-- Acts of bracketing (reductions). -/
axiom Act : Type

/-- Every act is also an item that can be reflected on. -/
axiom asItem : Act → Item

/-- Definition 2.1. `Brackets b x`: the act `b` brackets the item `x`. -/
axiom Brackets : Act → Item → Prop

/-- Items that persist across acts, existing before or after any given one. -/
axiom Persisting : Item → Prop

/-- Assumption 2.2 (residue). No act of bracketing brackets itself. -/
axiom residue : ∀ b, ¬ Brackets b (asItem b)

/-- Assumption 2.3 (iteration). Every act can be bracketed by a further act
of reflection. -/
axiom iteration : ∀ b, ∃ b', Brackets b' (asItem b)

/-- Assumption 2.4 (transcendence of the persisting). Whatever persists
across acts can be bracketed by some act. -/
axiom persisting_bracketable : ∀ x, Persisting x → ∃ b, Brackets b x

/-- Theorem 3.1 (irreducible residue). Every reduction leaves something
unbracketed, namely its own act. -/
theorem irreducible_residue (b : Act) : ∃ x, x = asItem b ∧ ¬ Brackets b x :=
  ⟨asItem b, rfl, residue b⟩

/-- Theorem 3.2. Nothing that persists across acts survives every reduction. -/
theorem no_persisting_residue :
    ¬ ∃ x, Persisting x ∧ ∀ b, ¬ Brackets b x :=
  fun ⟨x, hp, hall⟩ =>
    match persisting_bracketable x hp with
    | ⟨b, hb⟩ => hall b hb

/-- Corollary 3.3. The residue of each act can be bracketed by a later
reflection, which leaves its own residue. -/
theorem residue_renewed (b : Act) :
    ∃ b', Brackets b' (asItem b) ∧ ¬ Brackets b' (asItem b') :=
  match iteration b with
  | ⟨b', h⟩ => ⟨b', h, residue b'⟩

end Philosophy.PHE_20

#print axioms Philosophy.PHE_20.irreducible_residue
#print axioms Philosophy.PHE_20.no_persisting_residue
