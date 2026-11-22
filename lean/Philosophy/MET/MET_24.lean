/-
MET-24 · Existence as a First-Order Property
Formalization of Propositions 4.1, 4.2 and 4.3, Theorem 4.4, Proposition 4.5,
Theorem 4.6, Corollary 4.7, Theorems 5.3 and 5.4, Corollary 5.5 and
Proposition 5.6.

Part I (Section 4). Existence is defined as the first-order property of
being identical to something (Definition 3.1), with the quantifier ranging
over absolutely everything (Assumption 3.2). Everything exists, and the
second-order notion of instantiation is interdefinable with first-order
existence. The unrestricted characterization principle is inconsistent, and
with existence among the characterizing properties it yields an existent
golden mountain. Given univocal predication (Assumption 3.4) and the plain
fact that there are no golden mountains (Assumption 3.5), the Meinongian
golden mountain is not in the domain, and whatever the Meinongian takes to
be a nonexistent object in the domain exists in the sense of Definition 3.1
and merely lacks the Meinongian's predicate.

Part II (Section 5). A Meinongian language has a particular quantifier
ranging over all objects, an existentially loaded quantifier, and an
existence predicate. Meinongian models are translated into classical
one-quantifier models with an ordinary first-order predicate in place of
Meinongian existence, and conversely, preserving truth under every
assignment.

What this file establishes. The logical skeleton of the argument: given the
definition of existence and absolute generality, there are no nonexistent
objects; given univocal predication and the plain facts, the objects the
characterization principle posits are not in the domain; and Meinongian
theories are intertranslatable with classical theories in which their
existence predicate is an ordinary predicate. It does not establish the
definition of existence, absolute generality (argued in LOG-08), or the
univocity of predication, which the manuscript defends in Sections 3 and 8.
-/

namespace Philosophy.MET_24

/-! ## Part I. Existence and the characterization principle -/

/-- Assumption 3.2 (absolute generality). The domain of absolutely
unrestricted quantification. -/
axiom Thing : Type

/-- Definition 3.1. Existence: being identical to something. -/
def Exists (x : Thing) : Prop := ∃ y : Thing, y = x

/-- Definition 3.3. Second-order existence: a condition is instantiated. -/
def Instantiated (F : Thing → Prop) : Prop := ∃ x, F x

/-- Proposition 4.1 (universality). Everything exists. -/
theorem everything_exists : ∀ x : Thing, Exists x := fun x => ⟨x, rfl⟩

/-- Proposition 4.2 (interdefinability). A condition is instantiated iff
some existent satisfies it, and a thing exists iff the condition of being
identical to it is instantiated. -/
theorem interdefinable :
    (∀ F : Thing → Prop, Instantiated F ↔ ∃ x, Exists x ∧ F x) ∧
    (∀ x, Exists x ↔ Instantiated (fun y => y = x)) := by
  refine ⟨fun F => ⟨fun ⟨x, hx⟩ => ⟨x, everything_exists x, hx⟩,
    fun ⟨x, _, hx⟩ => ⟨x, hx⟩⟩, fun x => Iff.rfl⟩

/-- Proposition 4.3 (Kant's point preserved). Adding existence to a
condition does not change what satisfies it. -/
theorem existence_adds_nothing (F : Thing → Prop) (x : Thing) :
    F x ↔ (F x ∧ Exists x) :=
  ⟨fun h => ⟨h, everything_exists x⟩, fun h => h.1⟩

/-- Theorem 4.4 (Russell). Over any domain whatever, the unrestricted
characterization principle, that every condition is satisfied by some
object, is inconsistent. -/
theorem cp_inconsistent (D : Type) : ¬ ∀ φ : D → Prop, ∃ x, φ x := by
  intro h
  obtain ⟨_, hx⟩ := h (fun _ => False)
  exact hx

/-- Proposition 4.5 (the existent golden mountain). If the characterization
principle applies to a condition that includes the Meinongian existence
predicate E, and nothing that satisfies the rest of the condition satisfies
E, contradiction follows. -/
theorem existent_golden_mountain (D : Type) (G M E : D → Prop)
    (cp : ∃ x, G x ∧ M x ∧ E x) (none : ∀ x, G x → M x → ¬ E x) : False := by
  obtain ⟨x, hg, hm, he⟩ := cp
  exact none x hg hm he

/-- Golden things and mountains (plain predicates). -/
axiom Golden : Thing → Prop
axiom Mountain : Thing → Prop

/-- Assumption 3.5 (the plain facts). There are no golden mountains. -/
axiom no_golden_mountain : ¬ ∃ x, Golden x ∧ Mountain x

/-- Definition 3.6. A Meinongian object for a condition is a thing that
satisfies the condition and does not exist. -/
def MeinongianObject (φ : Thing → Prop) (x : Thing) : Prop := φ x ∧ ¬ Exists x

/-- Theorem 4.6 (the Meinongian dilemma). Suppose the Meinongian's
characterization principle supplies, in the domain of everything, an object
that is golden and a mountain in her senses (MG, MM) and lacks her
existence predicate E. Then her predicates are not the plain ones
(Assumption 3.4 fails for them), and the object exists in the sense of
Definition 3.1 while lacking E, so that E is not existence. -/
theorem dilemma (MG MM E : Thing → Prop) (cp : ∃ x, MG x ∧ MM x ∧ ¬ E x) :
    ¬ ((∀ x, MG x → Golden x) ∧ (∀ x, MM x → Mountain x)) ∧
    (∃ x, Exists x ∧ ¬ E x) := by
  obtain ⟨x, hg, hm, he⟩ := cp
  refine ⟨fun ⟨ug, um⟩ => no_golden_mountain ⟨x, ug x hg, um x hm⟩, x,
    everything_exists x, he⟩

/-- Corollary 4.7 (main result). There are no Meinongian objects for any
condition, and the golden mountain, understood with univocal predication,
is not in the domain. -/
theorem no_meinongian_objects :
    (∀ F : Thing → Prop, ¬ ∃ x, MeinongianObject F x) ∧
    ¬ ∃ x, Golden x ∧ Mountain x := by
  refine ⟨fun F ⟨x, _, hx⟩ => hx (everything_exists x), no_golden_mountain⟩

/-! ## Part II. Meinongian and classical languages -/

/-- Definition 5.1. Meinongian formulas: atomic predications `pred k v`
(predicate k of variable v), identity, the existence predicate `ex`,
negation, conjunction, the particular quantifier `some` over all objects
and the existentially loaded quantifier `exist`. -/
inductive MFm where
  | pred : Nat → Nat → MFm
  | eq : Nat → Nat → MFm
  | ex : Nat → MFm
  | neg : MFm → MFm
  | conj : MFm → MFm → MFm
  | some : Nat → MFm → MFm
  | exist : Nat → MFm → MFm

/-- Definition 5.2. Classical formulas, with a single quantifier and an
ordinary unary predicate `epred` in place of Meinongian existence. -/
inductive CFm where
  | pred : Nat → Nat → CFm
  | eq : Nat → Nat → CFm
  | epred : Nat → CFm
  | neg : CFm → CFm
  | conj : CFm → CFm → CFm
  | ex : Nat → CFm → CFm

/-- Definitions 5.1 and 5.2. A model: a domain, a distinguished unary
predicate (Meinongian existence, or an ordinary predicate in the classical
reading), and interpretations of the other predicates. -/
structure Model where
  D : Type
  E : D → Prop
  P : Nat → D → Prop

/-- Variable assignments and their updates. -/
def upd {D : Type} (g : Nat → D) (v : Nat) (d : D) : Nat → D :=
  fun w => if w = v then d else g w

theorem upd_same {D : Type} (g : Nat → D) (v : Nat) (d : D) : upd g v d v = d := by
  simp [upd]

/-- Definition 5.1. Outer-domain semantics for Meinongian formulas. -/
def mEval (M : Model) : (Nat → M.D) → MFm → Prop
  | g, .pred k v => M.P k (g v)
  | g, .eq v w => g v = g w
  | g, .ex v => M.E (g v)
  | g, .neg φ => ¬ mEval M g φ
  | g, .conj φ ψ => mEval M g φ ∧ mEval M g ψ
  | g, .some v φ => ∃ d, mEval M (upd g v d) φ
  | g, .exist v φ => ∃ d, M.E d ∧ mEval M (upd g v d) φ

/-- Definition 5.2. Classical semantics. -/
def cEval (M : Model) : (Nat → M.D) → CFm → Prop
  | g, .pred k v => M.P k (g v)
  | g, .eq v w => g v = g w
  | g, .epred v => M.E (g v)
  | g, .neg φ => ¬ cEval M g φ
  | g, .conj φ ψ => cEval M g φ ∧ cEval M g ψ
  | g, .ex v φ => ∃ d, cEval M (upd g v d) φ

/-- Translation from Meinongian into classical formulas. -/
def tr : MFm → CFm
  | .pred k v => .pred k v
  | .eq v w => .eq v w
  | .ex v => .epred v
  | .neg φ => .neg (tr φ)
  | .conj φ ψ => .conj (tr φ) (tr ψ)
  | .some v φ => .ex v (tr φ)
  | .exist v φ => .ex v (.conj (.epred v) (tr φ))

/-- Translation from classical into Meinongian formulas. -/
def back : CFm → MFm
  | .pred k v => .pred k v
  | .eq v w => .eq v w
  | .epred v => .ex v
  | .neg φ => .neg (back φ)
  | .conj φ ψ => .conj (back φ) (back ψ)
  | .ex v φ => .some v (back φ)

/-- Theorem 5.3 (translation). Every Meinongian formula is true in a model
under an assignment iff its translation is true in the same model read
classically. -/
theorem translation (M : Model) (f : MFm) :
    ∀ g, mEval M g f ↔ cEval M g (tr f) := by
  induction f with
  | pred k v => intro g; exact Iff.rfl
  | eq v w => intro g; exact Iff.rfl
  | ex v => intro g; exact Iff.rfl
  | neg φ ih => intro g; simp only [mEval, cEval, tr]; rw [ih g]
  | conj φ ψ ih1 ih2 => intro g; simp only [mEval, cEval, tr]; rw [ih1 g, ih2 g]
  | some v φ ih =>
    intro g; simp only [mEval, cEval, tr]
    exact ⟨fun ⟨d, h⟩ => ⟨d, (ih _).mp h⟩, fun ⟨d, h⟩ => ⟨d, (ih _).mpr h⟩⟩
  | exist v φ ih =>
    intro g; simp only [mEval, cEval, tr, upd_same]
    exact ⟨fun ⟨d, he, h⟩ => ⟨d, he, (ih _).mp h⟩,
      fun ⟨d, he, h⟩ => ⟨d, he, (ih _).mpr h⟩⟩

/-- Theorem 5.4 (converse translation). Every classical formula is true in a
model under an assignment iff its back-translation, with the ordinary
predicate read as Meinongian existence and the quantifier as the particular
quantifier, is true in the same model. -/
theorem back_translation (M : Model) (φ : CFm) :
    ∀ g, cEval M g φ ↔ mEval M g (back φ) := by
  induction φ with
  | pred k v => intro g; exact Iff.rfl
  | eq v w => intro g; exact Iff.rfl
  | epred v => intro g; exact Iff.rfl
  | neg φ ih => intro g; simp only [mEval, cEval, back]; rw [ih g]
  | conj φ ψ ih1 ih2 => intro g; simp only [mEval, cEval, back]; rw [ih1 g, ih2 g]
  | ex v φ ih =>
    intro g; simp only [mEval, cEval, back]
    exact ⟨fun ⟨d, h⟩ => ⟨d, (ih _).mp h⟩, fun ⟨d, h⟩ => ⟨d, (ih _).mpr h⟩⟩

/-- Corollary 5.5. In every Meinongian model, the existence defined from the
particular quantifier as in Definition 3.1 (`some 1 (eq 1 0)`: something is
identical to x0) holds of every object, while the existence defined from
the loaded quantifier holds exactly of the objects with the Meinongian
existence predicate. -/
theorem defined_existence (M : Model) (g : Nat → M.D) :
    mEval M g (.some 1 (.eq 1 0)) ∧
    (mEval M g (.exist 1 (.eq 1 0)) ↔ M.E (g 0)) := by
  simp only [mEval, upd]
  refine ⟨⟨g 0, by simp⟩, ⟨fun ⟨d, he, h⟩ => ?_, fun h => ⟨g 0, h, by simp⟩⟩⟩
  simp at h
  rw [← h]; exact he

/-- Proposition 5.6 (collapse). If the Meinongian existence predicate holds
of everything, the two quantifiers agree on every formula; so if they ever
disagree, some object lacks the predicate. -/
theorem collapse (M : Model) (hall : ∀ d, M.E d) (v : Nat) (φ : MFm) (g : Nat → M.D) :
    mEval M g (.exist v φ) ↔ mEval M g (.some v φ) := by
  simp only [mEval]
  exact ⟨fun ⟨d, _, h⟩ => ⟨d, h⟩, fun ⟨d, h⟩ => ⟨d, hall d, h⟩⟩

end Philosophy.MET_24

#print axioms Philosophy.MET_24.no_meinongian_objects
#print axioms Philosophy.MET_24.dilemma
#print axioms Philosophy.MET_24.translation
#print axioms Philosophy.MET_24.back_translation
#print axioms Philosophy.MET_24.defined_existence
