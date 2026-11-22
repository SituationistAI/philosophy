/-
PID-10 · Disembodied Persons
Formalization of Theorem 3.1 and Proposition 3.2.

What this file establishes. Given the phase-sortal definition of a person
(Definition 2.1, from PID-05), the definition of embodiment (Definition 2.2),
the functionalist premise (Assumption 2.4, from MND-08), the possibility of
a closed emulation (Assumption 2.5) and the principle that a body is
something one perceives or acts through (Assumption 2.6), there is a possible
world containing a person that has no body (Theorem 3.1). Given further that
a thinking organism perceives and acts through itself (Assumption 2.7), no
disembodied person is an organism (Proposition 3.2).

What it does not establish. It does not establish any of the assumptions,
and it says nothing about the actual world: no actual disembodied person is
asserted to exist.
-/

namespace Philosophy.PID_10

/-- Primitive: possible worlds. -/
axiom World : Type
/-- Primitive: things. -/
axiom Thing : Type

/-- Primitive: `x` has, at `w`, the capacities for rational thought and for
thinking of itself as itself. -/
axiom Capacities : World → Thing → Prop
/-- Primitive: `x` is a person at `w`. -/
axiom Person : World → Thing → Prop
/-- Primitive: `b` is, at `w`, something through which `x` perceives or on
which `x` acts directly. -/
axiom Coupled : World → Thing → Thing → Prop
/-- Primitive: `b` is a body of `x` at `w`. -/
axiom BodyOf : World → Thing → Thing → Prop
/-- Primitive: `x` is, at `w`, a closed emulation (Definition 2.3). -/
axiom ClosedEmulation : World → Thing → Prop
/-- Primitive: `x` is an organism at `w`. -/
axiom Organism : World → Thing → Prop

/-- Definition 2.1 (person, PID-05). -/
axiom definition_2_1 : ∀ w x, Person w x ↔ Capacities w x

/-- Definition 2.2 (embodiment). -/
def Embodied (w : World) (x : Thing) : Prop := ∃ b, BodyOf w b x

/-- Definition 2.3 (closed emulation), the part used here: a closed
emulation perceives through nothing and acts directly on nothing. -/
axiom definition_2_3 : ∀ w x, ClosedEmulation w x → ∀ b, ¬ Coupled w b x

/-- Assumption 2.4 (functionalism, MND-08). A closed emulation has the
capacities of Definition 2.1. -/
axiom assumption_2_4 : ∀ w x, ClosedEmulation w x → Capacities w x

/-- Assumption 2.5 (possibility). There could be a closed emulation. -/
axiom assumption_2_5 : ∃ w x, ClosedEmulation w x

/-- Assumption 2.6. A body of `x` is something `x` perceives through or acts
on directly. -/
axiom assumption_2_6 : ∀ w b x, BodyOf w b x → Coupled w b x

/-- Assumption 2.7. A thinking organism perceives through and acts on
itself, and so is its own body. -/
axiom assumption_2_7 : ∀ w x, Organism w x → BodyOf w x x

/-- Theorem 3.1 (main result). Disembodied persons are possible. -/
theorem disembodied_possible : ∃ w x, Person w x ∧ ¬ Embodied w x := by
  obtain ⟨w, x, hc⟩ := assumption_2_5
  refine ⟨w, x, (definition_2_1 w x).2 (assumption_2_4 w x hc), ?_⟩
  intro ⟨b, hb⟩
  exact definition_2_3 w x hc b (assumption_2_6 w b x hb)

/-- Proposition 3.2. No disembodied person is an organism. -/
theorem disembodied_not_organism (w : World) (x : Thing)
    (_hp : Person w x) (hd : ¬ Embodied w x) : ¬ Organism w x :=
  fun ho => hd ⟨x, assumption_2_7 w x ho⟩

end Philosophy.PID_10

#print axioms Philosophy.PID_10.disembodied_possible
#print axioms Philosophy.PID_10.disembodied_not_organism
