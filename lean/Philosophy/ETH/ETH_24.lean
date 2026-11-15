/-
ETH-24 · The Moral Status of Artificial Systems
Formalization of Theorem 3.1 and Proposition 3.2.

The premises of the argument are collected as the fields of a structure,
so that the main theorem holds for every interpretation of the primitive
notions that satisfies them, and so that their consistency with the
possibility of artificial moral status can be shown by exhibiting a model.

What this file establishes. Given that moral status requires and is secured
by sentience (Assumption 2.1, from ETH-07), that something is owed to a
being only if it has moral status (Principle P1), that sentience requires
an affective architecture (Assumption 2.3), and that current artificial
systems lack one (Assumption 2.4), no current artificial system has moral
status, and nothing is owed to any of them (Theorem 3.1). The premises are
jointly consistent with a current artificial system that thinks (as MND-08
allows) and with a future artificial system that has moral status
(Proposition 3.2): nothing in them excludes artificial systems as such.

What it does not establish. It does not establish the premises, and in
particular not the empirical Assumption 2.4. It does not show that any
future system will have moral status, only that the premises leave it open.
-/

namespace Philosophy.ETH_24

/-- The premises of Section 2, over a type `B` of beings. -/
structure Premises (B : Type) where
  /-- Being an artificial system. -/
  Artificial : B → Prop
  /-- Belonging to the current generation of systems. -/
  Current : B → Prop
  /-- Thinking (in the functional sense of MND-08). -/
  Thinks : B → Prop
  /-- Sentience: the capacity for valenced experience. -/
  Sentient : B → Prop
  /-- Definition 2.2. Having an affective architecture. -/
  Affective : B → Prop
  /-- Having moral status. -/
  HasStatus : B → Prop
  /-- Something is owed to the being. -/
  OwedTo : B → Prop
  /-- Assumption 2.1 (from ETH-07). Moral status iff sentience. -/
  status_iff_sentient : ∀ x, HasStatus x ↔ Sentient x
  /-- Principle P1. Something is owed to a being only if it has moral
  status. -/
  owed_requires_status : ∀ x, OwedTo x → HasStatus x
  /-- Assumption 2.3. Sentience requires an affective architecture. -/
  sentience_requires_affect : ∀ x, Sentient x → Affective x
  /-- Assumption 2.4. Current artificial systems lack an affective
  architecture. -/
  current_lack_affect : ∀ x, Artificial x → Current x → ¬ Affective x

/-- Theorem 3.1 (main result). No current artificial system has moral
status, and nothing is owed to any of them. -/
theorem no_status_now {B : Type} (P : Premises B) (x : B)
    (ha : P.Artificial x) (hc : P.Current x) :
    ¬ P.HasStatus x ∧ ¬ P.OwedTo x := by
  have hs : ¬ P.HasStatus x := fun h =>
    P.current_lack_affect x ha hc
      (P.sentience_requires_affect x ((P.status_iff_sentient x).mp h))
  exact ⟨hs, fun h => hs (P.owed_requires_status x h)⟩

/-- A model of the premises: `false` is a current artificial system that
thinks, `true` a future artificial system with an affective
architecture. -/
def model : Premises Bool where
  Artificial := fun _ => True
  Current := fun b => b = false
  Thinks := fun _ => True
  Sentient := fun b => b = true
  Affective := fun b => b = true
  HasStatus := fun b => b = true
  OwedTo := fun b => b = true
  status_iff_sentient := fun _ => Iff.rfl
  owed_requires_status := fun _ h => h
  sentience_requires_affect := fun _ h => h
  current_lack_affect := fun x _ hc ha => by
    simp only at hc ha
    rw [hc] at ha
    exact Bool.noConfusion ha

/-- Proposition 3.2 (substrate neutrality). The premises are consistent
with a current artificial system that thinks and lacks moral status, and
with a future artificial system that has moral status and to which
something is owed. -/
theorem may_change : ∃ (B : Type) (P : Premises B) (x y : B),
    P.Artificial x ∧ P.Current x ∧ P.Thinks x ∧ ¬ P.HasStatus x ∧
    P.Artificial y ∧ ¬ P.Current y ∧ P.HasStatus y ∧ P.OwedTo y := by
  refine ⟨Bool, model, false, true, ?_⟩
  simp [model]

end Philosophy.ETH_24

#print axioms Philosophy.ETH_24.no_status_now
#print axioms Philosophy.ETH_24.may_change
