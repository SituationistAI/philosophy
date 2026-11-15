/-
REL-13 · A Consistency Proof for Trinitarian Doctrine
Formalization of Definitions 2.1 to 2.8, Theorem 3.1, Lemmas 4.1 and 4.2,
Theorem 4.3, Corollary 4.4, Proposition 4.5 and Proposition 6.1.

A relative-identity structure has objects, sortals, a relation "a is an F"
and a three-place relation "a is the same F as b" (Definition 2.1). There is
no absolute identity in the object language. Principles of a logic of
relative identity are universal Horn clauses in this language (Definitions
2.2 and 2.3); Geach's system G says that each relation "same F" is an
equivalence relation on the Fs (Definition 2.4). The Trinitarian claims,
in relative-identity form, are those of Definition 2.6.

What this file establishes.
* Theorem 3.1: an explicit three-element structure, built without axioms,
  satisfies G and every Trinitarian claim.
* Theorem 4.3 (main result): every Horn logic of relative identity that
  extends G and admits relativity (Definition 2.7) has a model of the
  Trinitarian claims. The model is a three-element substructure of the
  square of any model witnessing relativity.
* Corollary 4.4: for such logics, admitting relativity is also necessary.
* Proposition 4.5: in every model of the Trinitarian claims, "same God"
  fails substitutivity for the predicate "is the same person as the
  Father" (the point made in LOG-12-a).
* Proposition 6.1: the restriction to Horn principles is essential; a
  non-Horn principle can admit relativity and exclude the doctrine.

What it does not establish. It does not establish that the doctrine is
true, that the relative-identity reading is the correct reading of the
creeds, or that relative identity is the correct logic outside theology.
No axioms are used: every result is a theorem about structures.
-/

namespace Philosophy.REL_13

/-- Definition 2.1. A relative-identity structure: objects, sortals, the
relation "a is an F" and the relation "a is the same F as b". -/
structure RIStructure where
  Obj : Type
  Sortal : Type
  isA : Sortal → Obj → Prop
  same : Sortal → Obj → Obj → Prop

/-- Definition 2.2. Atomic formulas of the pure language of relative
identity, with sortal variables and object variables (both indexed by
natural numbers). -/
inductive Atom where
  | isA (s x : Nat)
  | same (s x y : Nat)

/-- Definition 2.2. A universal Horn clause: a list of atoms (the body)
and at most one atom (the head). A clause with no head says that its body
is never jointly satisfied. -/
structure Horn where
  body : List Atom
  head : Option Atom

/-- Satisfaction of an atom under assignments to sortal and object
variables. -/
def Atom.holds (M : RIStructure) (τ : Nat → M.Sortal) (ρ : Nat → M.Obj) :
    Atom → Prop
  | .isA s x => M.isA (τ s) (ρ x)
  | .same s x y => M.same (τ s) (ρ x) (ρ y)

/-- What the head of a clause requires. -/
def headHolds (M : RIStructure) (τ : Nat → M.Sortal) (ρ : Nat → M.Obj) :
    Option Atom → Prop
  | none => False
  | some a => a.holds M τ ρ

/-- Definition 2.2. A clause is valid in a structure if, under every
assignment, the head holds whenever the whole body holds. -/
def Valid (M : RIStructure) (c : Horn) : Prop :=
  ∀ τ ρ, (∀ a, a ∈ c.body → a.holds M τ ρ) → headHolds M τ ρ c.head

/-- Definition 2.3. A logic of relative identity is a set of Horn
principles; a structure is a model of it if every principle is valid. -/
def Models (M : RIStructure) (L : Horn → Prop) : Prop :=
  ∀ c, L c → Valid M c

/-- Definition 2.4. Geach's system G: reflexivity on the sortal, the field
condition, symmetry and transitivity, for sortal variable 0. -/
def reflC : Horn := ⟨[.isA 0 0], some (.same 0 0 0)⟩
def fieldC : Horn := ⟨[.same 0 0 1], some (.isA 0 0)⟩
def symmC : Horn := ⟨[.same 0 0 1], some (.same 0 1 0)⟩
def transC : Horn := ⟨[.same 0 0 1, .same 0 1 2], some (.same 0 0 2)⟩

/-- Definition 2.4. The clauses of G. -/
def G (c : Horn) : Prop := c = reflC ∨ c = fieldC ∨ c = symmC ∨ c = transC

/-- Definition 2.4, read semantically. -/
structure GeachProps (M : RIStructure) : Prop where
  refl : ∀ s x, M.isA s x → M.same s x x
  field : ∀ s x y, M.same s x y → M.isA s x
  symm : ∀ s x y, M.same s x y → M.same s y x
  trans : ∀ s x y z, M.same s x y → M.same s y z → M.same s x z

/-- An assignment of three objects to the first three object variables. -/
def asg3 {α : Type} (x y z : α) : Nat → α
  | 0 => x
  | 1 => y
  | _ => z

/-- Definition 2.4: a model of G has the semantic properties of G. -/
theorem geach_props (M : RIStructure) (h : ∀ c, G c → Valid M c) :
    GeachProps M := by
  constructor
  · intro s x hx
    exact h reflC (Or.inl rfl) (fun _ => s) (asg3 x x x)
      (by intro a ha; simp [reflC] at ha; subst ha; exact hx)
  · intro s x y hxy
    exact h fieldC (Or.inr (Or.inl rfl)) (fun _ => s) (asg3 x y y)
      (by intro a ha; simp [fieldC] at ha; subst ha; exact hxy)
  · intro s x y hxy
    exact h symmC (Or.inr (Or.inr (Or.inl rfl))) (fun _ => s) (asg3 x y y)
      (by intro a ha; simp [symmC] at ha; subst ha; exact hxy)
  · intro s x y z hxy hyz
    exact h transC (Or.inr (Or.inr (Or.inr rfl))) (fun _ => s) (asg3 x y z)
      (by
        intro a ha
        simp [transC] at ha
        rcases ha with ha | ha <;> subst ha
        · exact hxy
        · exact hyz)

/-- Definition 2.5. An interpretation of the theological vocabulary: three
names and two sortals. -/
structure Interp (M : RIStructure) where
  father : M.Obj
  son : M.Obj
  spirit : M.Obj
  god : M.Sortal
  person : M.Sortal

/-- Definition 2.6. The Trinitarian claims in relative-identity form:
(T1) each is God; (T2) each is a person; (T3) each is the same God as
each; (T4) no two are the same person; (T5) there is exactly one God;
(T6) every person is the same person as one of the three. -/
def Trinity (M : RIStructure) (I : Interp M) : Prop :=
  (M.isA I.god I.father ∧ M.isA I.god I.son ∧ M.isA I.god I.spirit) ∧
  (M.isA I.person I.father ∧ M.isA I.person I.son ∧ M.isA I.person I.spirit) ∧
  (M.same I.god I.father I.son ∧ M.same I.god I.son I.spirit ∧
    M.same I.god I.father I.spirit) ∧
  (¬ M.same I.person I.father I.son ∧ ¬ M.same I.person I.son I.spirit ∧
    ¬ M.same I.person I.father I.spirit) ∧
  (∃ x, M.isA I.god x ∧ ∀ y, M.isA I.god y → M.same I.god y x) ∧
  (∀ y, M.isA I.person y →
    M.same I.person y I.father ∨ M.same I.person y I.son ∨
    M.same I.person y I.spirit)

/-- Definition 2.7. A structure witnesses relativity (Geach's thesis) if
two objects that are both Fs and both Gs are the same F but not the same
G. -/
def Relativity (M : RIStructure) : Prop :=
  ∃ (F H : M.Sortal) (a b : M.Obj),
    M.isA H a ∧ M.isA H b ∧ M.same F a b ∧ ¬ M.same H a b

/-! ### The explicit model (Theorem 3.1) -/

inductive Hyp where
  | father | son | spirit
  deriving DecidableEq

inductive Kind where
  | god | person
  deriving DecidableEq

/-- The explicit model: three objects, all of which are Gods and persons;
any two are the same God; each is the same person only as itself. -/
def T : RIStructure where
  Obj := Hyp
  Sortal := Kind
  isA := fun _ _ => True
  same := fun k x y => match k with
    | .god => True
    | .person => x = y

def TI : Interp T := ⟨Hyp.father, Hyp.son, Hyp.spirit, Kind.god, Kind.person⟩

/-- Theorem 3.1. The explicit model satisfies Geach's system and every
Trinitarian claim. -/
theorem explicit_model : Models T G ∧ Trinity T TI := by
  constructor
  · intro c hc τ ρ hb
    rcases hc with h | h | h | h <;> subst h
    · show T.same (τ 0) (ρ 0) (ρ 0)
      cases τ 0 <;> simp [T]
    · show T.isA (τ 0) (ρ 0)
      trivial
    · have h1 : T.same (τ 0) (ρ 0) (ρ 1) := hb (.same 0 0 1) (by simp [symmC])
      show T.same (τ 0) (ρ 1) (ρ 0)
      revert h1
      cases τ 0 <;> simp [T, Eq.comm]
    · have h1 : T.same (τ 0) (ρ 0) (ρ 1) := hb (.same 0 0 1) (by simp [transC])
      have h2 : T.same (τ 0) (ρ 1) (ρ 2) := hb (.same 0 1 2) (by simp [transC])
      show T.same (τ 0) (ρ 0) (ρ 2)
      revert h1 h2
      cases τ 0 <;> simp [T]
      exact fun h1 h2 => h1.trans h2
  · refine ⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩,
      ⟨trivial, trivial, trivial⟩, ?_, ⟨Hyp.father, trivial, fun _ _ => trivial⟩, ?_⟩
    · refine ⟨?_, ?_, ?_⟩ <;> (show ¬ (_ = _); decide)
    · intro y _
      show y = Hyp.father ∨ y = Hyp.son ∨ y = Hyp.spirit
      cases y <;> simp

/-! ### Preservation (Lemmas 4.1 and 4.2) -/

/-- The square of a structure: pairs of objects, pairs of sortals,
relations holding componentwise. -/
def sq (M : RIStructure) : RIStructure where
  Obj := M.Obj × M.Obj
  Sortal := M.Sortal × M.Sortal
  isA := fun s x => M.isA s.1 x.1 ∧ M.isA s.2 x.2
  same := fun s x y => M.same s.1 x.1 y.1 ∧ M.same s.2 x.2 y.2

/-- The substructure of a structure on the objects satisfying `P`. -/
def sub (M : RIStructure) (P : M.Obj → Prop) : RIStructure where
  Obj := {x : M.Obj // P x}
  Sortal := M.Sortal
  isA := fun s x => M.isA s x.val
  same := fun s x y => M.same s x.val y.val

/-- Lemma 4.1. Every Horn clause valid in a structure is valid in its
square. -/
theorem horn_square (M : RIStructure) (c : Horn) (h : Valid M c) :
    Valid (sq M) c := by
  intro τ ρ hb
  have key : ∀ a : Atom, a.holds (sq M) τ ρ ↔
      a.holds M (fun n => (τ n).1) (fun n => (ρ n).1) ∧
      a.holds M (fun n => (τ n).2) (fun n => (ρ n).2) := by
    intro a; cases a <;> exact Iff.rfl
  have h1 := h (fun n => (τ n).1) (fun n => (ρ n).1)
    (fun a ha => ((key a).1 (hb a ha)).1)
  have h2 := h (fun n => (τ n).2) (fun n => (ρ n).2)
    (fun a ha => ((key a).1 (hb a ha)).2)
  cases hc : c.head with
  | none => rw [hc] at h1; exact h1.elim
  | some a =>
    rw [hc] at h1 h2
    exact (key a).2 ⟨h1, h2⟩

/-- Lemma 4.2. Every Horn clause valid in a structure is valid in each of
its substructures. -/
theorem horn_sub (M : RIStructure) (P : M.Obj → Prop) (c : Horn)
    (h : Valid M c) : Valid (sub M P) c := by
  intro τ ρ hb
  have key : ∀ a : Atom, a.holds (sub M P) τ ρ ↔
      a.holds M τ (fun n => (ρ n).val) := by
    intro a; cases a <;> exact Iff.rfl
  have h1 := h τ (fun n => (ρ n).val) (fun a ha => (key a).1 (hb a ha))
  cases hc : c.head with
  | none => rw [hc] at h1; exact h1.elim
  | some a => rw [hc] at h1; exact (key a).2 h1

/-! ### The main theorem -/

/-- The Trinitarian substructure of the square built from a witness of
relativity `a`, `b`: the pairs (a, a), (a, b) and (b, a). -/
def triad (M : RIStructure) (a b : M.Obj) : RIStructure :=
  sub (sq M) (fun p => p = (a, a) ∨ p = (a, b) ∨ p = (b, a))

/-- Theorem 4.3 (main result). Let L be a logic of relative identity
extending Geach's system (Definition 2.8): a Horn logic that contains G
(hypothesis `hG`) and has a model witnessing relativity (`hM`, `hR`). Then
L has a model of the Trinitarian claims. -/
theorem consistency (L : Horn → Prop) (hG : ∀ c, G c → L c)
    (M : RIStructure) (hM : Models M L) (hR : Relativity M) :
    ∃ (N : RIStructure) (I : Interp N), Models N L ∧ Trinity N I := by
  obtain ⟨F, H, a, b, hHa, hHb, hFab, hHab⟩ := hR
  have g := geach_props M (fun c hc => hM c (hG c hc))
  have hFa : M.isA F a := g.field F a b hFab
  have hFba : M.same F b a := g.symm F a b hFab
  have hFb : M.isA F b := g.field F b a hFba
  have hFaa : M.same F a a := g.refl F a hFa
  have hHaa : M.same H a a := g.refl H a hHa
  have hHbb : M.same H b b := g.refl H b hHb
  refine ⟨triad M a b,
    ⟨⟨(a, a), Or.inl rfl⟩, ⟨(a, b), Or.inr (Or.inl rfl)⟩,
     ⟨(b, a), Or.inr (Or.inr rfl)⟩, (F, F), (H, H)⟩, ?_, ?_⟩
  · intro c hc
    exact horn_sub (sq M) _ c (horn_square M c (hM c hc))
  · refine ⟨⟨⟨hFa, hFa⟩, ⟨hFa, hFb⟩, ⟨hFb, hFa⟩⟩,
      ⟨⟨hHa, hHa⟩, ⟨hHa, hHb⟩, ⟨hHb, hHa⟩⟩,
      ⟨⟨hFaa, hFab⟩, ⟨hFab, hFba⟩, ⟨hFab, hFaa⟩⟩,
      ⟨fun h => hHab h.2, fun h => hHab h.1, fun h => hHab h.1⟩,
      ⟨⟨(a, a), Or.inl rfl⟩, ⟨hFa, hFa⟩, ?_⟩, ?_⟩
    · intro ⟨y, hy⟩ _
      rcases hy with h | h | h <;> subst h
      · exact ⟨hFaa, hFaa⟩
      · exact ⟨hFaa, hFba⟩
      · exact ⟨hFba, hFaa⟩
    · intro ⟨y, hy⟩ _
      rcases hy with h | h | h <;> subst h
      · exact Or.inl ⟨hHaa, hHaa⟩
      · exact Or.inr (Or.inl ⟨hHaa, hHbb⟩)
      · exact Or.inr (Or.inr ⟨hHbb, hHaa⟩)

/-- Corollary 4.4. For a Horn logic extending G, the Trinitarian claims
have a model if and only if the logic admits relativity. -/
theorem consistency_iff (L : Horn → Prop) (hG : ∀ c, G c → L c) :
    (∃ (N : RIStructure) (I : Interp N), Models N L ∧ Trinity N I) ↔
    (∃ M : RIStructure, Models M L ∧ Relativity M) := by
  constructor
  · intro ⟨N, I, hN, hT⟩
    exact ⟨N, hN, I.god, I.person, I.father, I.son,
      hT.2.1.1, hT.2.1.2.1, hT.2.2.1.1, hT.2.2.2.1.1⟩
  · intro ⟨M, hM, hR⟩
    exact consistency L hG M hM hR

/-- Proposition 4.5. In every model of the Trinitarian claims, the relation
"same God" fails substitutivity for the predicate "is the same person as
the Father". -/
theorem god_not_substitutive (N : RIStructure) (I : Interp N)
    (gp : GeachProps N) (hT : Trinity N I) :
    ¬ ∀ P : N.Obj → Prop, ∀ x y, N.same I.god x y → P x → P y := by
  intro h
  have hpf : N.same I.person I.father I.father := gp.refl _ _ hT.2.1.1
  have := h (fun z => N.same I.person I.father z) I.father I.son
    hT.2.2.1.1 hpf
  exact hT.2.2.2.1.1 this

/-! ### The Horn restriction is essential (Proposition 6.1) -/

/-- The non-Horn principle of Section 6: no relation "same F" collects
three Gs of which no two are the same G. -/
def AtMostTwo (M : RIStructure) : Prop :=
  ∀ (F H : M.Sortal) (x y z : M.Obj),
    M.same F x y → M.same F y z → M.isA H x → M.isA H y → M.isA H z →
    M.same H x y ∨ M.same H y z ∨ M.same H x z

/-- The two-element structure of LOG-12-a, Proposition 3.4: one sortal
under which the two objects are the same, one under which they differ. -/
def Two : RIStructure where
  Obj := Bool
  Sortal := Bool
  isA := fun _ _ => True
  same := fun s x y => s = true ∨ x = y

/-- Proposition 6.1. The principle AtMostTwo is consistent with Geach's
system and with relativity, and excludes every model of the Trinitarian
claims. -/
theorem horn_essential :
    GeachProps Two ∧ AtMostTwo Two ∧ Relativity Two ∧
    ∀ (N : RIStructure) (I : Interp N), AtMostTwo N → ¬ Trinity N I := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro s x _; exact Or.inr rfl
  · intro _ _ _ _; trivial
  · intro s x y h
    show s = true ∨ y = x
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  · intro s x y z h1 h2
    show s = true ∨ x = z
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · rcases h2 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (h1.trans h2)
  · intro _ H x y z _ _ _ _ _
    show (H = true ∨ x = y) ∨ (H = true ∨ y = z) ∨ (H = true ∨ x = z)
    cases x <;> cases y <;> cases z <;> simp
  · refine ⟨true, false, true, false, trivial, trivial, Or.inl rfl, ?_⟩
    show ¬ (false = true ∨ true = false)
    simp
  · intro N I h hT
    rcases h I.god I.person I.father I.son I.spirit hT.2.2.1.1 hT.2.2.1.2.1
      hT.2.1.1 hT.2.1.2.1 hT.2.1.2.2 with h | h | h
    · exact hT.2.2.2.1.1 h
    · exact hT.2.2.2.1.2.1 h
    · exact hT.2.2.2.1.2.2 h

end Philosophy.REL_13

#print axioms Philosophy.REL_13.explicit_model
#print axioms Philosophy.REL_13.consistency
#print axioms Philosophy.REL_13.consistency_iff
#print axioms Philosophy.REL_13.god_not_substitutive
#print axioms Philosophy.REL_13.horn_essential
