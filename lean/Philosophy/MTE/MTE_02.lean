/-
MTE-02 · Objectivity Without Absoluteness
Formalization of Lemma 3.1, Theorem 3.2, Propositions 3.3 to 3.5,
Theorem 3.6, Corollaries 3.7 and 3.8, and Propositions 5.1 to 5.4.

Rational agents (actual and possible) have natures. A moral claim says that
an agent is required to perform an act in a situation, where situations are
specified without reference to the nature of the agent. An idealized
evaluator responds to the complete information about an agent's performing
an act in a situation; the moral facts are facts about such idealized
reactions (Assumption 2.10, the thesis of MTE-01).

What this file establishes. Given common rationality (Assumption 2.9),
identification (Assumption 2.10), universalizability over natures
(Assumption 2.11) and diversity (Assumption 2.12): morality is objective
(every rational agent's idealized verdict on every moral claim coincides with
the moral truth), its requirements factor through the natures of agents by a
unique standard, and it is not absolute (some act is required of one possible
rational agent and not of another in the same situation). Objectivity
excludes relativism, and the assumptions are jointly satisfiable
(Proposition 5.3); without common rationality they do not exclude relativism
(Proposition 5.4).

What it does not establish. It does not establish any of the four
assumptions, in particular the convergence of idealized reactions
(Assumption 2.9) or the existence of rational natures that differ in the way
Assumption 2.12 requires; nor does it say what the standard requires of any
particular nature.
-/

namespace Philosophy.MTE_02

/-- Definition 2.1. Rational agents, actual and possible. -/
axiom Agent : Type

/-- Definition 2.1. Natures: what the real definition of an agent's kind
states (its constitutive capacities, needs and vulnerabilities). -/
axiom Nature : Type

/-- Definition 2.1. The nature of each rational agent. -/
axiom nature : Agent → Nature

/-- Definition 2.2. Situations, specified without reference to the nature
of the agent whose situation it is. -/
axiom Sit : Type

/-- Definition 2.2. Act-types. -/
axiom Act : Type

/-- Definition 2.2. `Required x s a`: agent `x` is morally required to do `a`
in situation `s`. -/
axiom Required : Agent → Sit → Act → Prop

/-- Definition 2.3. Bodies of complete information. -/
axiom Info : Type

/-- Definition 2.3. The complete information about an agent's doing an act
in a situation. It does not depend on who considers it. -/
axiom info : Agent → Sit → Act → Info

/-- Definition 2.3. `Resp e i`: the idealized reaction of evaluator `e` to
complete information `i` is one of requiring. -/
axiom Resp : Agent → Info → Prop

/-- Definition 2.3. Evaluator `e`'s idealized verdict that `x` is required
to do `a` in `s`. -/
def Ideal (e x : Agent) (s : Sit) (a : Act) : Prop := Resp e (info x s a)

/-- Definition 2.4. Objectivity: every rational agent's idealized verdict on
every moral claim coincides with the moral truth. -/
def Objective : Prop := ∀ e x s a, Ideal e x s a ↔ Required x s a

/-- Definition 2.5. Absoluteness: what is required in a situation does not
vary with the agent. -/
def Absolute : Prop := ∀ x y s a, Required x s a ↔ Required y s a

/-- Definition 2.6. A standard `R` on natures fixes the requirements. -/
def Factors (R : Nature → Sit → Act → Prop) : Prop :=
  ∀ x s a, Required x s a ↔ R (nature x) s a

/-- Definition 2.6. Nature-relativity: some standard on natures fixes the
requirements. -/
def NatureRelative : Prop := ∃ R, Factors R

/-- Definition 2.7. Relativism: some moral claim is true relative to one
rational standpoint and not relative to another. -/
def Relativism : Prop := ∃ e e' x s a, Ideal e x s a ∧ ¬ Ideal e' x s a

/-- Assumption 2.9 (common rationality). Idealized evaluators react alike
to the same complete information. (Assumption 2.8, that complete
information is the same for every evaluator, is built into the type of
`info`.) -/
axiom common_rationality : ∀ (e e' : Agent) (i : Info), Resp e i ↔ Resp e' i

/-- Assumption 2.10 (identification, MTE-01). An agent is required to do an
act just in case every idealized reaction requires it. -/
axiom identification : ∀ x s a, Required x s a ↔ ∀ e, Ideal e x s a

/-- Assumption 2.11 (universalizability over natures). Agents of the same
nature in the same situation receive the same idealized verdicts. -/
axiom universalizability :
  ∀ e x y s a, nature x = nature y → (Ideal e x s a ↔ Ideal e y s a)

/-- Assumption 2.12 (diversity). Some act is required of one possible
rational agent and not of another in the same situation. -/
axiom diversity : ∃ x y s a, Required x s a ∧ ¬ Required y s a

/-- Lemma 3.1 (standpoint invariance). -/
theorem standpoint_invariance (e e' x : Agent) (s : Sit) (a : Act) :
    Ideal e x s a ↔ Ideal e' x s a :=
  common_rationality e e' (info x s a)

/-- Theorem 3.2 (objectivity). -/
theorem objectivity : Objective := fun e x s a =>
  ⟨fun h => (identification x s a).2
      (fun e' => (standpoint_invariance e e' x s a).1 h),
   fun h => (identification x s a).1 h e⟩

/-- Proposition 3.3 (factorization through natures). -/
theorem factorization : NatureRelative :=
  ⟨fun n s a => ∃ x, nature x = n ∧ Required x s a,
   fun x s a =>
     ⟨fun h => ⟨x, rfl, h⟩,
      fun ⟨y, hy, hr⟩ => (identification x s a).2
        (fun e => (universalizability e y x s a hy).1
          ((identification y s a).1 hr e))⟩⟩

/-- Proposition 3.4 (uniqueness of the standard on realized natures). -/
theorem standard_unique (R R' : Nature → Sit → Act → Prop)
    (hR : Factors R) (hR' : Factors R') (x : Agent) (s : Sit) (a : Act) :
    R (nature x) s a ↔ R' (nature x) s a :=
  (hR x s a).symm.trans (hR' x s a)

/-- Proposition 3.5 (non-absoluteness). -/
theorem not_absolute : ¬ Absolute := fun h =>
  match diversity with
  | ⟨x, y, s, a, hx, hy⟩ => hy ((h x y s a).1 hx)

/-- Theorem 3.6 (main result). Morality is objective and nature-relative,
and it is not absolute. -/
theorem objective_not_absolute : Objective ∧ NatureRelative ∧ ¬ Absolute :=
  ⟨objectivity, factorization, not_absolute⟩

/-- Corollary 3.7. Where requirements differ in a situation, natures
differ. -/
theorem variation_is_in_nature (x y : Agent) (s : Sit) (a : Act)
    (hx : Required x s a) (hy : ¬ Required y s a) : nature x ≠ nature y :=
  fun heq => hy ((identification y s a).2 (fun e =>
    (universalizability e x y s a heq).1 ((identification x s a).1 hx e)))

/-- Corollary 3.8 (absoluteness within a kind). -/
theorem absolute_within_kind (x y : Agent) (h : nature x = nature y)
    (s : Sit) (a : Act) : Required x s a ↔ Required y s a :=
  ⟨fun hx => Classical.byContradiction fun hy =>
      variation_is_in_nature x y s a hx hy h,
   fun hy => Classical.byContradiction fun hx =>
      variation_is_in_nature y x s a hy hx h.symm⟩

/-- Proposition 5.1. Relativism is false. -/
theorem not_relativism : ¬ Relativism := fun ⟨e, e', x, s, a, h, h'⟩ =>
  h' ((standpoint_invariance e e' x s a).1 h)

/-- Proposition 5.2 (diversity without disagreement). Some act is required
of one agent and not of another of a different nature, and every rational
agent's idealized verdicts agree on both claims. -/
theorem diversity_without_disagreement :
    ∃ x y s a, nature x ≠ nature y ∧
      ∀ e, Ideal e x s a ∧ ¬ Ideal e y s a :=
  match diversity with
  | ⟨x, y, s, a, hx, hy⟩ =>
    ⟨x, y, s, a, variation_is_in_nature x y s a hx hy,
     fun e => ⟨(objectivity e x s a).2 hx,
               fun h => hy ((objectivity e y s a).1 h)⟩⟩

/-! ## Models (Section 5)

The models are stated for an arbitrary frame, without the axioms above, to
show that the assumptions are jointly satisfiable and that common
rationality is what excludes relativism. -/

/-- A frame interprets the primitives of Definitions 2.1 to 2.3. -/
structure Frame where
  Agent : Type
  Nature : Type
  nature : Agent → Nature
  Sit : Type
  Act : Type
  Info : Type
  info : Agent → Sit → Act → Info
  Resp : Agent → Info → Prop
  Required : Agent → Sit → Act → Prop

namespace Frame

variable (F : Frame)

def Ideal (e x : F.Agent) (s : F.Sit) (a : F.Act) : Prop := F.Resp e (F.info x s a)
def Common : Prop := ∀ e e' i, F.Resp e i ↔ F.Resp e' i
def Identification : Prop := ∀ x s a, F.Required x s a ↔ ∀ e, F.Ideal e x s a
def Universalizable : Prop :=
  ∀ e x y s a, F.nature x = F.nature y → (F.Ideal e x s a ↔ F.Ideal e y s a)
def Diverse : Prop := ∃ x y s a, F.Required x s a ∧ ¬ F.Required y s a
def Objective : Prop := ∀ e x s a, F.Ideal e x s a ↔ F.Required x s a
def Absolute : Prop := ∀ x y s a, F.Required x s a ↔ F.Required y s a
def Relativism : Prop := ∃ e e' x s a, F.Ideal e x s a ∧ ¬ F.Ideal e' x s a

end Frame

/-- Two rational natures; an act required of agents of the first and not of
the second. -/
def twoNatures : Frame where
  Agent := Bool
  Nature := Bool
  nature := id
  Sit := Unit
  Act := Unit
  Info := Bool
  info := fun x _ _ => x
  Resp := fun _ i => i = true
  Required := fun x _ _ => x = true

/-- Proposition 5.3 (consistency). Assumptions 2.9 to 2.12 are jointly
satisfiable, and in a frame satisfying them morality is objective and not
absolute. -/
theorem consistency :
    twoNatures.Common ∧ twoNatures.Identification ∧
    twoNatures.Universalizable ∧ twoNatures.Diverse ∧
    twoNatures.Objective ∧ ¬ twoNatures.Absolute := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e e' i; exact Iff.rfl
  · intro x s a
    exact ⟨fun h _ => h, fun h => h true⟩
  · intro e x y s a h
    have h' : x = y := h
    subst h'; exact Iff.rfl
  · exact ⟨true, false, (), (), rfl, Bool.false_ne_true⟩
  · intro e x s a; exact Iff.rfl
  · intro h
    exact Bool.false_ne_true ((h true false () ()).1 rfl)

/-- Evaluators who react to information about an agent only when it
concerns themselves: common rationality fails. -/
def selfRegarding : Frame where
  Agent := Bool
  Nature := Bool
  nature := id
  Sit := Unit
  Act := Unit
  Info := Bool
  info := fun x _ _ => x
  Resp := fun e i => i = e
  Required := fun _ _ _ => False

/-- Proposition 5.4. Without common rationality, identification and
universalizability do not exclude relativism. -/
theorem relativism_without_common :
    selfRegarding.Identification ∧ selfRegarding.Universalizable ∧
    ¬ selfRegarding.Common ∧ selfRegarding.Relativism := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x s a
    refine ⟨fun h => False.elim h, fun h => ?_⟩
    have h1 : x = true := h true
    have h2 : x = false := h false
    exact Bool.false_ne_true (h2.symm.trans h1)
  · intro e x y s a h
    have h' : x = y := h
    subst h'; exact Iff.rfl
  · intro h
    have : (true = true) ↔ (true = false) := h true false true
    exact Bool.false_ne_true (this.1 rfl).symm
  · exact ⟨true, false, true, (), (), rfl, Bool.false_ne_true.symm⟩

end Philosophy.MTE_02

#print axioms Philosophy.MTE_02.objective_not_absolute
#print axioms Philosophy.MTE_02.not_relativism
#print axioms Philosophy.MTE_02.consistency
#print axioms Philosophy.MTE_02.relativism_without_common
