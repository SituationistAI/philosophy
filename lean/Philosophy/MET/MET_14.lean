/-
MET-14 · The Unity of Grounding
Formalization of Definitions 2.3–2.8, Assumptions 2.9 and 2.10, Lemmas 3.1
and 3.2, Propositions 3.3 and 3.4, Theorems 3.5 and 3.6, Corollaries 3.7
and 3.8, and Proposition 5.1.

A grounding frame consists of facts, levels (each fact has one level),
and a family of apparent varieties of grounding, each a binary relation
on facts (Definitions 2.1 and 2.2 in the manuscript). A link is a pair of
facts related by some variety; generic grounding `G` is the transitive
closure of the links, that is, the relation of being connected by a
chain of links of any varieties (Definition 2.3, read with Principle P1).
The signature of a variety is the set of pairs of levels between which
it holds (Definition 2.4).

Part I proves, for an arbitrary frame: that `G` contains every variety,
is transitive, and is the only relation that contains every variety, is
transitive and is witnessed by chains of links (Lemmas 3.1, 3.2); that
under mixed acyclicity `G` is a strict partial order (Proposition 3.3);
that under level closure every variety is the restriction of `G` to its
signature (Proposition 3.4); that mixed acyclicity and level closure
together are equivalent to the existence of a witnessed strict partial
order of which the varieties are restrictions to classes of level pairs
(Theorem 3.5); and the unity theorem (Theorem 3.6) with its corollaries.

Part II applies the results to the actual frame, whose two substantive
premises are axioms (Assumptions 2.9 and 2.10).

Part III gives a concrete frame with two varieties, infinitely many
levels and no fundamental level, satisfying both assumptions
(Proposition 5.1): the unity of grounding does not require that
grounding be well-founded.

What this file establishes. Given mixed acyclicity and level closure,
there is exactly one witnessed transitive relation containing all the
varieties; it is a strict partial order; and each variety is its
restriction to the pairs of levels at which that variety operates.

What it does not establish. It does not establish either assumption,
that the apparent varieties listed in the manuscript are all the
varieties there are, that levels are individuated as the manuscript
says, or that the unique unifier is a genuine relation rather than a
constructed one (the explanatory argument of Section 4 is not
formalized). It concerns mediate grounding only; immediate grounding
is not treated.
-/

namespace Philosophy.MET_14

/-! ### Part I. Grounding frames -/

/-- Definitions 2.1 and 2.2 (facts, levels, varieties). A frame assigns
each fact a level and interprets each apparent variety of grounding as a
binary relation on facts (`R v f g`: `f` v-grounds `g`). -/
structure Frame where
  Fact : Type
  Level : Type
  Variety : Type
  lev : Fact → Level
  R : Variety → Fact → Fact → Prop

variable (F : Frame)

/-- A link: two facts related by some variety. -/
def Link (f g : F.Fact) : Prop := ∃ v, F.R v f g

/-- Definition 2.3 (generic grounding). `G f g` iff a chain of links of
any varieties leads from `f` to `g` (the transitive closure of the
links). -/
def G : F.Fact → F.Fact → Prop := Relation.TransGen (Link F)

/-- Definition 2.4 (signature). The pair of levels `(l, m)` belongs to
the signature of `v` iff some fact at `l` v-grounds some fact at `m`. -/
def sig (v : F.Variety) (l m : F.Level) : Prop :=
  ∃ f g, F.R v f g ∧ F.lev f = l ∧ F.lev g = m

/-- Definition 2.5 (strict partial order). -/
def StrictOrder (H : F.Fact → F.Fact → Prop) : Prop :=
  (∀ f, ¬ H f f) ∧ (∀ f g h, H f g → H g h → H f h)

/-- Definition 2.6 (witnessed). Every `H`-connection is made by a chain
of links. -/
def Witnessed (H : F.Fact → F.Fact → Prop) : Prop := ∀ f g, H f g → G F f g

/-- Definition 2.7 (unifier). A transitive, witnessed relation that
contains every variety. -/
def Unifier (H : F.Fact → F.Fact → Prop) : Prop :=
  (∀ v f g, F.R v f g → H f g) ∧ (∀ f g h, H f g → H g h → H f h) ∧
    Witnessed F H

/-- Definition 2.8 (level restrictions). The varieties are restrictions
of `H` to classes of level pairs: for some assignment `S` of a class of
level pairs to each variety, `f` v-grounds `g` iff `H f g` and the
levels of `f` and `g` are in `S v`. -/
def LevelRestrictions (H : F.Fact → F.Fact → Prop) : Prop :=
  ∃ S : F.Variety → F.Level → F.Level → Prop,
    ∀ v f g, F.R v f g ↔ (H f g ∧ S v (F.lev f) (F.lev g))

/-- Assumption 2.9 (mixed acyclicity), as a property of frames. -/
def MixedAcyclic : Prop := ∀ f, ¬ G F f f

/-- Assumption 2.10 (level closure), as a property of frames. -/
def LevelClosure : Prop :=
  ∀ v f g, G F f g → sig F v (F.lev f) (F.lev g) → F.R v f g

/-- Lemma 3.1. Generic grounding is a unifier. -/
theorem lemma_3_1 : Unifier F (G F) :=
  ⟨fun v _ _ h => Relation.TransGen.single ⟨v, h⟩,
   fun _ _ _ h1 h2 => Relation.TransGen.trans h1 h2,
   fun _ _ h => h⟩

/-- Lemma 3.2 (uniqueness). Every unifier coincides with generic
grounding. -/
theorem lemma_3_2 (H : F.Fact → F.Fact → Prop) (hH : Unifier F H) :
    ∀ f g, H f g ↔ G F f g := by
  obtain ⟨hR, htr, hw⟩ := hH
  intro f g
  constructor
  · exact hw f g
  · intro h
    induction h with
    | single hl => obtain ⟨v, hv⟩ := hl; exact hR v _ _ hv
    | tail _ hl ih => obtain ⟨v, hv⟩ := hl; exact htr _ _ _ ih (hR v _ _ hv)

/-- Proposition 3.3. Under mixed acyclicity, generic grounding is a
strict partial order, and hence asymmetric. -/
theorem proposition_3_3 (hA : MixedAcyclic F) :
    StrictOrder F (G F) ∧ ∀ f g, G F f g → ¬ G F g f :=
  ⟨⟨hA, fun _ _ _ h1 h2 => Relation.TransGen.trans h1 h2⟩,
   fun f _ h1 h2 => hA f (Relation.TransGen.trans h1 h2)⟩

/-- Proposition 3.4. Under level closure, each variety is the
restriction of generic grounding to its signature. -/
theorem proposition_3_4 (hC : LevelClosure F) :
    ∀ v f g, F.R v f g ↔ (G F f g ∧ sig F v (F.lev f) (F.lev g)) := by
  intro v f g
  constructor
  · intro h
    exact ⟨Relation.TransGen.single ⟨v, h⟩, ⟨f, g, h, rfl, rfl⟩⟩
  · intro ⟨hg, hs⟩
    exact hC v f g hg hs

/-- Theorem 3.5 (characterization). Mixed acyclicity and level closure
hold iff some witnessed strict partial order has the varieties as its
restrictions to classes of level pairs. -/
theorem theorem_3_5 :
    (MixedAcyclic F ∧ LevelClosure F) ↔
      ∃ H, StrictOrder F H ∧ Witnessed F H ∧ LevelRestrictions F H := by
  constructor
  · intro ⟨hA, hC⟩
    exact ⟨G F, (proposition_3_3 F hA).1, fun _ _ h => h,
      ⟨sig F, proposition_3_4 F hC⟩⟩
  · intro ⟨H, ⟨hirr, htr⟩, hw, ⟨S, hS⟩⟩
    have hR : ∀ v f g, F.R v f g → H f g := fun v f g h => ((hS v f g).1 h).1
    have hGH : ∀ f g, G F f g → H f g :=
      fun f g => ((lemma_3_2 F H ⟨hR, htr, hw⟩) f g).2
    constructor
    · intro f hf
      exact hirr f (hGH f f hf)
    · intro v f g hg hs
      obtain ⟨f', g', h', hf', hg'⟩ := hs
      have hS' : S v (F.lev f) (F.lev g) := by
        have := ((hS v f' g').1 h').2
        rw [hf', hg'] at this
        exact this
      exact (hS v f g).2 ⟨hGH f g hg, hS'⟩

/-- Theorem 3.6 (unity of grounding). Under mixed acyclicity and level
closure: generic grounding is a unifier and a strict partial order;
every variety is its restriction to the variety's signature; and every
unifier coincides with it. -/
theorem theorem_3_6 (hA : MixedAcyclic F) (hC : LevelClosure F) :
    Unifier F (G F) ∧ StrictOrder F (G F) ∧
      (∀ v f g, F.R v f g ↔ (G F f g ∧ sig F v (F.lev f) (F.lev g))) ∧
      (∀ H, Unifier F H → ∀ f g, H f g ↔ G F f g) :=
  ⟨lemma_3_1 F, (proposition_3_3 F hA).1, proposition_3_4 F hC,
   fun H hH => lemma_3_2 F H hH⟩

/-- Corollary 3.7 (shared profile). Under mixed acyclicity, every
variety is irreflexive and asymmetric, and no mixed chain returns to its
starting point. -/
theorem corollary_3_7 (hA : MixedAcyclic F) :
    ∀ v f g, ¬ F.R v f f ∧ (F.R v f g → ¬ F.R v g f) := by
  intro v f g
  refine ⟨fun h => hA f (Relation.TransGen.single ⟨v, h⟩), fun h1 h2 => ?_⟩
  exact hA f (Relation.TransGen.trans (Relation.TransGen.single ⟨v, h1⟩)
    (Relation.TransGen.single ⟨v, h2⟩))

/-- Corollary 3.8 (definability). Under level closure, each variety is
definable from generic grounding, the level assignment and its
signature: any relation so defined is that variety. -/
theorem corollary_3_8 (hC : LevelClosure F) (v : F.Variety)
    (R' : F.Fact → F.Fact → Prop)
    (hdef : ∀ f g, R' f g ↔ (G F f g ∧ sig F v (F.lev f) (F.lev g))) :
    ∀ f g, R' f g ↔ F.R v f g := by
  intro f g
  rw [hdef f g, proposition_3_4 F hC v f g]

/-! ### Part II. The actual frame -/

/-- Definitions 2.1 and 2.2: the actual facts, their levels, and the
apparent varieties of grounding (logical, set-theoretic, mereological,
determinable, realization, normative, social, nomic, and so on). -/
axiom actual : Frame

/-- Assumption 2.9 (mixed acyclicity). No fact is connected to itself by
a chain of grounding links, whatever their varieties. -/
axiom assumption_2_9 : MixedAcyclic actual

/-- Assumption 2.10 (level closure). If a chain of links leads from `f`
to `g`, and some fact at the level of `f` v-grounds some fact at the
level of `g`, then `f` v-grounds `g`. -/
axiom assumption_2_10 : LevelClosure actual

/-- Theorem 3.6, applied to the actual frame: grounding is one relation,
a strict partial order, of which the apparent varieties are the
restrictions to their signatures; and it is the only unifier. -/
theorem unity_of_grounding :
    Unifier actual (G actual) ∧ StrictOrder actual (G actual) ∧
      (∀ v f g, actual.R v f g ↔
        (G actual f g ∧ sig actual v (actual.lev f) (actual.lev g))) ∧
      (∀ H, Unifier actual H → ∀ f g, H f g ↔ G actual f g) :=
  theorem_3_6 actual assumption_2_9 assumption_2_10

/-! ### Part III. Unity without a fundamental level -/

/-- The model of Proposition 5.1. Levels are the integers; at each level
there are two facts, `(n, false)` and `(n, true)`. The intra-level
variety (`false`) relates `(n, false)` to `(n, true)`; the inter-level
variety (`true`) relates any fact at a lower level to any fact at a
higher level. -/
def descent : Frame where
  Fact := Int × Bool
  Level := Int
  Variety := Bool
  lev := fun f => f.1
  R := fun v f g =>
    (v = false ∧ f.1 = g.1 ∧ f.2 = false ∧ g.2 = true) ∨ (v = true ∧ f.1 < g.1)

/-- The lexicographic order on the model's facts. -/
def lex (f g : Int × Bool) : Prop :=
  f.1 < g.1 ∨ (f.1 = g.1 ∧ f.2 = false ∧ g.2 = true)

theorem link_lex (f g : Int × Bool) (h : Link descent f g) : lex f g := by
  obtain ⟨v, hv⟩ := h
  rcases hv with ⟨_, h1, h2, h3⟩ | ⟨_, h1⟩
  · exact Or.inr ⟨h1, h2, h3⟩
  · exact Or.inl h1

theorem lex_trans (f g h : Int × Bool) (h1 : lex f g) (h2 : lex g h) : lex f h := by
  rcases h1 with a | ⟨a, b, c⟩ <;> rcases h2 with d | ⟨d, e, k⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · rw [c] at e; cases e

theorem G_lex (f g : Int × Bool) (h : G descent f g) : lex f g := by
  induction h with
  | single hl => exact link_lex _ _ hl
  | tail _ hl ih => exact lex_trans _ _ _ ih (link_lex _ _ hl)

/-- Proposition 5.1. The model satisfies mixed acyclicity and level
closure; both of its varieties are instantiated; and every fact has a
ground at a strictly lower level, so that there is no fundamental
level. -/
theorem proposition_5_1 :
    MixedAcyclic descent ∧ LevelClosure descent ∧
      (∃ f g, descent.R false f g) ∧ (∃ f g, descent.R true f g) ∧
      (∀ g : Int × Bool, ∃ f : Int × Bool, G descent f g ∧ f.1 < g.1) := by
  refine ⟨?_, ?_, ⟨(0, false), (0, true), Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩,
    ⟨(0, false), (1, false), Or.inr ⟨rfl, by decide⟩⟩, ?_⟩
  · intro f hf
    rcases G_lex f f hf with h | ⟨_, h2, h3⟩
    · omega
    · rw [h2] at h3; cases h3
  · intro v f g hg hs
    obtain ⟨f', g', h', hf', hg'⟩ := hs
    have hl := G_lex f g hg
    show (v = false ∧ f.1 = g.1 ∧ f.2 = false ∧ g.2 = true) ∨ (v = true ∧ f.1 < g.1)
    have hf'' : f'.1 = f.1 := hf'
    have hg'' : g'.1 = g.1 := hg'
    rcases h' with ⟨hv, e, _, _⟩ | ⟨hv, e⟩
    · rcases hl with l | ⟨l1, l2, l3⟩
      · exact absurd l (by omega)
      · exact Or.inl ⟨hv, l1, l2, l3⟩
    · rcases hl with l | ⟨l1, _, _⟩
      · exact Or.inr ⟨hv, l⟩
      · exact absurd e (by omega)
  · intro g
    exact ⟨(g.1 - 1, g.2), Relation.TransGen.single ⟨true, Or.inr ⟨rfl, by
      show g.1 - 1 < g.1; omega⟩⟩, by show g.1 - 1 < g.1; omega⟩

end Philosophy.MET_14

#print axioms Philosophy.MET_14.unity_of_grounding
#print axioms Philosophy.MET_14.theorem_3_5
#print axioms Philosophy.MET_14.proposition_5_1
