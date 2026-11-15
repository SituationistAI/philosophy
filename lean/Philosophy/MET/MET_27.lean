/-
MET-27 · Natural Kinds and Their Number
Formalization of Definitions 2.4–2.6, Assumptions 2.3 and 2.8, Lemma 3.1,
Theorem 3.2, Proposition 3.3, Lemmas 4.1 and 4.2, Theorem 4.3, Corollary
4.4, Propositions 4.5 and 4.6, Assumptions 5.1–5.3 and Theorem 5.4.

A world has objects, genuine features (genuine properties of objects or
of their parts, and genuine relations among the parts; Definition 2.1),
a possession relation, and a relation of nomic necessitation between a
set of features and a feature (Definition 2.2). The extension of a set of
features is the class of objects having all of them; the intent of a
class of objects is the set of features all of its members have
(Definition 2.4). A cluster is the nomic closure of a core set of
features that contains some feature beyond the core (Definition 2.5); a
natural kind is the non-empty extension of a cluster (Definition 2.6).

Part I proves, for an arbitrary world in which the laws are true
(Assumption 2.3): projection from core to kind (Lemma 3.1); that a
natural kind exists if some law with surplus has an instantiated core
(Theorem 3.2); that membership in a natural kind is fixed by the genuine
features (Proposition 3.3); that natural kinds are upward closed and
closed under the intent-extent correspondence (Lemmas 4.1 and 4.2); the
outsider test and the privative test for non-kinds (Theorem 4.3,
Corollary 4.4); and that a natural kind is determined by its intent
(Proposition 4.5). Proposition 4.6 gives a finite model in which the
premises hold, a natural kind exists, and both tests have instances.

Part II applies the results to the actual world, with the empirical
premises about jade, the invertebrates and a typical biological species
as axioms (Assumptions 5.1–5.3), and proves Theorem 5.4: natural kinds
exist, and each of the three standard taxa is not one.

What this file establishes. Given the truth of laws, the existence of an
instantiated law with surplus, and the three empirical premises, there
are natural kinds, and there are standard taxa that are not natural
kinds. It does not establish the premises, that the cluster definition
is the right account of natural kinds, or how many natural kinds there
are.
-/

namespace Philosophy.MET_27

/-! ### Part I. Worlds, clusters and kinds -/

/-- Definitions 2.1 and 2.2. Objects, genuine features, possession, and
nomic necessitation (`N C p`: the laws entail that whatever has every
feature in `C` has `p`). -/
structure World where
  Obj : Type
  Feat : Type
  has : Obj → Feat → Prop
  N : (Feat → Prop) → Feat → Prop

variable (W : World)

/-- Assumption 2.3, as a property of worlds: the laws are true. -/
def LawsTrue : Prop :=
  ∀ C p, W.N C p → ∀ x, (∀ q, C q → W.has x q) → W.has x p

/-- Definition 2.4 (extension). The objects having every feature in `K`. -/
def ext (K : W.Feat → Prop) (x : W.Obj) : Prop := ∀ p, K p → W.has x p

/-- Definition 2.4 (intent). The features had by every member of `X`. -/
def int (X : W.Obj → Prop) (p : W.Feat) : Prop := ∀ x, X x → W.has x p

/-- Definition 2.5 (cluster with core). `K` consists of the core `C` and
the features the laws attach to it, and contains some feature beyond the
core (surplus). -/
def ClusterWithCore (K C : W.Feat → Prop) : Prop :=
  (∀ p, K p ↔ (C p ∨ W.N C p)) ∧ ∃ p, K p ∧ ¬ C p

/-- Definition 2.5 (cluster). -/
def Cluster (K : W.Feat → Prop) : Prop := ∃ C, ClusterWithCore W K C

/-- Definition 2.6 (natural kind). A class of objects that is the
non-empty extension of a cluster. -/
def NaturalKind (X : W.Obj → Prop) : Prop :=
  ∃ K, Cluster W K ∧ (∃ x, X x) ∧ ∀ x, X x ↔ ext W K x

/-- Lemma 3.1 (projection). If the laws are true and `X` is the extension
of a cluster with core `C`, every object having the core belongs to `X`. -/
theorem lemma_3_1 (hL : LawsTrue W) (K C : W.Feat → Prop) (X : W.Obj → Prop)
    (hK : ClusterWithCore W K C) (hX : ∀ x, X x ↔ ext W K x) :
    ∀ x, ext W C x → X x := by
  intro x hx
  apply (hX x).2
  intro p hp
  rcases (hK.1 p).1 hp with hc | hn
  · exact hx p hc
  · exact hL C p hn x hx

/-- Theorem 3.2 (existence). If the laws are true and some law attaches
to an instantiated core a feature outside it, there is a natural kind. -/
theorem theorem_3_2 (hL : LawsTrue W)
    (hS : ∃ C p, ¬ C p ∧ W.N C p ∧ ∃ x, ext W C x) :
    ∃ X, NaturalKind W X := by
  obtain ⟨C, p, hpC, hN, x, hx⟩ := hS
  let K : W.Feat → Prop := fun q => C q ∨ W.N C q
  have hK : ClusterWithCore W K C := ⟨fun _ => Iff.rfl, ⟨p, Or.inr hN, hpC⟩⟩
  refine ⟨ext W K, ⟨K, ⟨C, hK⟩, ⟨x, ?_⟩, fun _ => Iff.rfl⟩⟩
  exact lemma_3_1 W hL K C (ext W K) hK (fun _ => Iff.rfl) x hx

/-- Proposition 3.3 (real division). Objects that agree on every genuine
feature agree on membership in every natural kind. -/
theorem proposition_3_3 (X : W.Obj → Prop) (hX : NaturalKind W X)
    (x y : W.Obj) (hxy : ∀ p, W.has x p ↔ W.has y p) : X x ↔ X y := by
  obtain ⟨K, _, _, hK⟩ := hX
  rw [hK x, hK y]
  exact ⟨fun h p hp => (hxy p).1 (h p hp), fun h p hp => (hxy p).2 (h p hp)⟩

/-- Lemma 4.1 (upward closure). If `x` is in a natural kind and `y` has
every genuine feature `x` has, `y` is in the kind. -/
theorem lemma_4_1 (X : W.Obj → Prop) (hX : NaturalKind W X) (x y : W.Obj)
    (hx : X x) (hxy : ∀ p, W.has x p → W.has y p) : X y := by
  obtain ⟨K, _, _, hK⟩ := hX
  exact (hK y).2 (fun p hp => hxy p ((hK x).1 hx p hp))

/-- Lemma 4.2 (closure). Every object that has every feature common to
the members of a natural kind belongs to it. -/
theorem lemma_4_2 (X : W.Obj → Prop) (hX : NaturalKind W X) (y : W.Obj)
    (hy : ∀ p, int W X p → W.has y p) : X y := by
  obtain ⟨K, _, _, hK⟩ := hX
  exact (hK y).2 (fun p hp => hy p (fun x hx => (hK x).1 hx p hp))

/-- Theorem 4.3 (outsider test). A class with an outsider that has every
feature common to its members is not a natural kind. -/
theorem theorem_4_3 (X : W.Obj → Prop)
    (h : ∃ z, ¬ X z ∧ ∀ p, int W X p → W.has z p) : ¬ NaturalKind W X := by
  intro hX
  obtain ⟨z, hz, hzp⟩ := h
  exact hz (lemma_4_2 W X hX z hzp)

/-- Corollary 4.4 (privative test). A class that excludes an object having
every feature of one of its members is not a natural kind. -/
theorem corollary_4_4 (X : W.Obj → Prop)
    (h : ∃ x z, X x ∧ ¬ X z ∧ ∀ p, W.has x p → W.has z p) :
    ¬ NaturalKind W X := by
  intro hX
  obtain ⟨x, z, hx, hz, hxz⟩ := h
  exact hz (lemma_4_1 W X hX x z hx hxz)

/-- Proposition 4.5 (determination by intent). Natural kinds with the same
intent have the same members. -/
theorem proposition_4_5 (X Y : W.Obj → Prop) (hX : NaturalKind W X)
    (hY : NaturalKind W Y) (h : ∀ p, int W X p ↔ int W Y p) :
    ∀ x, X x ↔ Y x := by
  intro x
  constructor
  · intro hx
    apply lemma_4_2 W Y hY x
    intro p hp
    exact (h p).2 hp x hx
  · intro hy
    apply lemma_4_2 W X hX x
    intro p hp
    exact (h p).1 hp x hy

/-! ### A finite model (Proposition 4.6) -/

/-- Possession in the model: four objects, three features. Object 0 has
features 0 and 1; object 1 has all three; object 2 has feature 2; object
3 has features 1 and 2. -/
def hasB : Fin 4 → Fin 3 → Bool
  | 0, 0 => true | 0, 1 => true
  | 1, _ => true
  | 2, 2 => true
  | 3, 1 => true | 3, 2 => true
  | _, _ => false

/-- The model. The only law attaches feature 1 to the core {0}. -/
def model : World where
  Obj := Fin 4
  Feat := Fin 3
  has := fun x p => hasB x p = true
  N := fun C p => C 0 ∧ p = 1

theorem model_law : ∀ x : Fin 4, hasB x 0 = true → hasB x 1 = true := by decide

theorem model_core :
    ∀ p : Fin 3, (p = 0 ∨ p = 1) ↔ (p = 0 ∨ ((0 : Fin 3) = 0 ∧ p = 1)) := by decide

theorem model_ext :
    ∀ x : Fin 4, (x = 0 ∨ x = 1) ↔ ∀ p : Fin 3, (p = 0 ∨ p = 1) → hasB x p = true := by
  decide

theorem model_outsider :
    ∀ p : Fin 3, (∀ x : Fin 4, (x = 0 ∨ x = 2) → hasB x p = true) → hasB 3 p = true := by
  decide

theorem model_dominates : ∀ p : Fin 3, hasB 0 p = true → hasB 1 p = true := by decide

/-- Proposition 4.6. In the model the laws are true; the class {0, 1} is a
natural kind; the disjunctive class {0, 2} fails the outsider test; and
the class {0} fails the privative test. -/
theorem proposition_4_6 :
    LawsTrue model ∧
    NaturalKind model (fun x : Fin 4 => x = 0 ∨ x = 1) ∧
    ¬ NaturalKind model (fun x : Fin 4 => x = 0 ∨ x = 2) ∧
    ¬ NaturalKind model (fun x : Fin 4 => x = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C p hN x hx
    obtain ⟨h0, hp⟩ := hN
    subst hp
    exact model_law x (hx _ h0)
  · refine ⟨fun p : Fin 3 => p = 0 ∨ p = 1,
      ⟨fun p : Fin 3 => p = 0, ⟨model_core, ⟨(1 : Fin 3), Or.inr rfl, by decide⟩⟩⟩,
      ⟨(0 : Fin 4), Or.inl rfl⟩, model_ext⟩
  · exact theorem_4_3 model _ ⟨(3 : Fin 4), by decide, model_outsider⟩
  · exact corollary_4_4 model _ ⟨(0 : Fin 4), (1 : Fin 4), rfl, by decide, model_dominates⟩

/-! ### Part II. The actual world -/

/-- Definitions 2.1 and 2.2: the actual objects, genuine features,
possession and nomic necessitation. -/
axiom actual : World

/-- Assumption 2.3 (laws are true). -/
axiom assumption_2_3 : LawsTrue actual

/-- Assumption 2.8 (instantiated surplus). Some law attaches to an
instantiated core of genuine features a feature outside it. -/
axiom assumption_2_8 :
  ∃ C p, ¬ C p ∧ actual.N C p ∧ ∃ x, ext actual C x

/-- The taxon jade (Definition 2.7). -/
axiom jade : actual.Obj → Prop

/-- The taxon Invertebrata (Definition 2.7). -/
axiom invertebrata : actual.Obj → Prop

/-- A typical biological species taxon (Definition 2.7). -/
axiom species : actual.Obj → Prop

/-- Assumption 5.1. Some silicate that is not jade has every genuine
feature common to all specimens of jade. -/
axiom assumption_5_1 :
  ∃ z, ¬ jade z ∧ ∀ p, int actual jade p → actual.has z p

/-- Assumption 5.2. Some vertebrate has every genuine feature common to
all invertebrates. -/
axiom assumption_5_2 :
  ∃ z, ¬ invertebrata z ∧ ∀ p, int actual invertebrata p → actual.has z p

/-- Assumption 5.3. Some organism outside the species has every genuine
feature common to all its members. -/
axiom assumption_5_3 :
  ∃ z, ¬ species z ∧ ∀ p, int actual species p → actual.has z p

/-- Theorem 5.4 (natural kinds are real, and fewer than taxonomies
suggest). There is a natural kind, and jade, the invertebrates and a
typical species are not natural kinds. -/
theorem theorem_5_4 :
    (∃ X, NaturalKind actual X) ∧ ¬ NaturalKind actual jade ∧
      ¬ NaturalKind actual invertebrata ∧ ¬ NaturalKind actual species :=
  ⟨theorem_3_2 actual assumption_2_3 assumption_2_8,
   theorem_4_3 actual jade assumption_5_1,
   theorem_4_3 actual invertebrata assumption_5_2,
   theorem_4_3 actual species assumption_5_3⟩

end Philosophy.MET_27

#print axioms Philosophy.MET_27.theorem_5_4
#print axioms Philosophy.MET_27.theorem_4_3
#print axioms Philosophy.MET_27.proposition_4_6
