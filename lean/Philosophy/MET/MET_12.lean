/-
MET-12 · Laws Without Governance
Formalization of Definitions 2.1–2.5, Assumption 2.6, Principles P1 and
P2, Propositions 3.1, 3.2 and 3.6, Theorems 3.3 and 3.4 and Corollary 3.5.

Part I is a toy best-system account. A mosaic is a finite list of points,
each recording whether two natural properties F and G are instantiated
there. Candidate axioms are four generalizations in the vocabulary of F
and G; a system is a set of them. A system is true in a mosaic if no point
is of a kind it excludes; its strength is the number of kinds it excludes
and its size the number of its axioms; its score is twice its strength
minus its size (shifted by a constant to stay in the natural numbers). The
laws are the generalizations entailed by every best true system.

Part II is the argument against governance. Facts, partial grounding,
lawhood, instancehood and scientific explanation are primitives. Grounding
is a strict partial order (Assumption 2.6); the instances of a law partly
ground it (Principle P1, Humean grounding); laws scientifically explain
their instances (Principle P2). A law governs an instance if it grounds it
(Definition 2.5).

What this file establishes. Best-system laws are true; whether a
generalization is a law depends on the whole mosaic, so that one further
event elsewhere can remove a law; given Assumption 2.6 and P1, no law
governs any of its instances; given P2 as well, laws explain their
instances without governing them; and, if explanation is irreflexive, the
principle that grounding followed by explanation is explanation fails.
Finally, the premises are jointly satisfiable (a concrete model).

What it does not establish. It does not establish Assumption 2.6 or the
principles, that the toy measure of simplicity and strength is the right
one, or that actual laws are best-system laws.
-/

namespace Philosophy.MET_12

/-! ### Part I. Best systems over a finite mosaic -/

/-- Definition 2.1 (mosaic). A point records whether `F` and whether `G`
is instantiated there; a mosaic is a finite list of points. -/
abbrev Point := Bool × Bool
abbrev Mosaic := List Point

/-- The kind of a point: 0 = neither, 1 = `G` only, 2 = `F` only, 3 = both. -/
def kind (p : Point) : Nat := (if p.1 then 2 else 0) + (if p.2 then 1 else 0)

/-- Definition 2.2 (candidate axioms). Generalization `g` excludes kind `k`:
0 `all F are G`, 1 `all G are F`, 2 `everything is F`, 3 `everything is G`. -/
def excl : Nat → Nat → Bool
  | 0, k => k == 2
  | 1, k => k == 1
  | 2, k => k == 0 || k == 1
  | 3, k => k == 0 || k == 2
  | _, _ => false

/-- A generalization is true in a mosaic if no point is of a kind it excludes. -/
def holds (m : Mosaic) (g : Nat) : Bool := m.all fun p => !(excl g (kind p))

/-- Definition 2.2 (systems). A system is a set of the four generalizations,
coded as a mask below 16; it excludes a kind if one of its axioms does. -/
def sysExcl (s k : Nat) : Bool :=
  (List.range 4).any fun g => Nat.testBit s g && excl g k

def sysTrue (m : Mosaic) (s : Nat) : Bool := m.all fun p => !(sysExcl s (kind p))

/-- Strength: the number of kinds excluded. -/
def strength (s : Nat) : Nat := ((List.range 4).filter (sysExcl s)).length

/-- Size: the number of axioms. -/
def size (s : Nat) : Nat := ((List.range 4).filter (Nat.testBit s)).length

/-- Score: balance of strength and simplicity (2 · strength − size, plus 4). -/
def score (s : Nat) : Nat := 2 * strength s + 4 - size s

/-- Definition 2.3 (best system). A true system whose score is not exceeded
by that of any true system. -/
def isBest (m : Mosaic) (s : Nat) : Bool :=
  sysTrue m s && (List.range 16).all fun t => !(sysTrue m t) || decide (score t ≤ score s)

/-- A system entails a generalization if it excludes every kind the
generalization excludes. -/
def entails (s g : Nat) : Bool := (List.range 4).all fun k => !(excl g k) || sysExcl s k

/-- Definition 2.4 (law). A generalization entailed by every best system
(there is always at least one). -/
def isLaw (m : Mosaic) (g : Nat) : Bool :=
  (List.range 16).any (isBest m) &&
    (List.range 16).all fun s => !(isBest m s) || entails s g

theorem kind_lt (p : Point) : kind p < 4 := by
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;> decide

/-- Proposition 3.1. Every law is true in its mosaic. -/
theorem proposition_3_1 (m : Mosaic) (g : Nat) (h : isLaw m g = true) :
    holds m g = true := by
  simp only [isLaw, Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at h
  obtain ⟨⟨s, hs, hb⟩, hall⟩ := h
  have he : entails s g = true := by
    have := hall s hs
    simp only [hb, Bool.not_true, Bool.false_or] at this
    exact this
  have ht : sysTrue m s = true := by
    simp only [isBest, Bool.and_eq_true] at hb
    exact hb.1
  simp only [holds, List.all_eq_true]
  intro p hp
  simp only [sysTrue, List.all_eq_true] at ht
  simp only [entails, List.all_eq_true] at he
  have h1 := ht p hp
  have h2 := he (kind p) (List.mem_range.2 (kind_lt p))
  cases hx : excl g (kind p) <;> cases hy : sysExcl s (kind p) <;> simp_all

/-- A mosaic in which every `F` is `G` and every `G` is `F`. -/
def m1 : Mosaic := [(true, true), (true, true), (false, false)]

/-- The same mosaic with one further event: an `F` that is not `G`. -/
def m2 : Mosaic := m1 ++ [(true, false)]

/-- Proposition 3.2 (laws depend on the whole mosaic). In `m1` both
`all F are G` and `all G are F` are laws; adding one point elsewhere
removes the first and leaves the second. -/
theorem proposition_3_2 :
    isLaw m1 0 = true ∧ isLaw m1 1 = true ∧ isLaw m2 0 = false ∧ isLaw m2 1 = true := by
  decide

/-! ### Part II. Explanation without governance -/

/-- Facts. -/
axiom Fact : Type

/-- Partial grounding. -/
axiom Grounds : Fact → Fact → Prop

/-- Assumption 2.6 (grounding is a strict partial order): irreflexivity. -/
axiom grounds_irrefl : ∀ f, ¬ Grounds f f

/-- Assumption 2.6 (grounding is a strict partial order): transitivity. -/
axiom grounds_trans : ∀ f g h, Grounds f g → Grounds g h → Grounds f h

/-- The fact that some generalization is a law. -/
axiom IsLaw : Fact → Prop

/-- `InstanceOf i l`: `i` is an instance of the law stated by `l`. -/
axiom InstanceOf : Fact → Fact → Prop

/-- Scientific explanation. -/
axiom Explains : Fact → Fact → Prop

/-- Definition 2.5 (governing). A law governs an instance if the law-fact
grounds it. -/
def Governs (l i : Fact) : Prop := IsLaw l ∧ InstanceOf i l ∧ Grounds l i

/-- Principle P1 (Humean grounding). The instances of a law are among the
facts of the mosaic that ground its being a law. -/
axiom principle_P1 : ∀ l i, IsLaw l → InstanceOf i l → Grounds i l

/-- Principle P2 (explanation by subsumption). A law scientifically
explains its instances. -/
axiom principle_P2 : ∀ l i, IsLaw l → InstanceOf i l → Explains l i

/-- Theorem 3.3 (no governance). No law governs any of its instances. -/
theorem theorem_3_3 (l i : Fact) : ¬ Governs l i := fun ⟨hl, hi, hg⟩ =>
  grounds_irrefl i (grounds_trans i l i (principle_P1 l i hl hi) hg)

/-- Theorem 3.4 (explanation without governance). -/
theorem theorem_3_4 (l i : Fact) (hl : IsLaw l) (hi : InstanceOf i l) :
    Explains l i ∧ ¬ Governs l i :=
  ⟨principle_P2 l i hl hi, theorem_3_3 l i⟩

/-- Corollary 3.5. If scientific explanation is irreflexive and some law
has an instance, then the mixed transitivity principle (whatever grounds
an explanans explains its explanandum) fails. -/
theorem corollary_3_5 (hirr : ∀ f, ¬ Explains f f)
    (l i : Fact) (hl : IsLaw l) (hi : InstanceOf i l) :
    ¬ (∀ a b c, Grounds a b → Explains b c → Explains a c) := fun hmix =>
  hirr i (hmix i l i (principle_P1 l i hl hi) (principle_P2 l i hl hi))

/-! ### Consistency -/

/-- A two-element model: a law-fact and one instance. -/
inductive F2 where
  | law
  | inst
  deriving DecidableEq

def G2 (a b : F2) : Prop := a = .inst ∧ b = .law
def E2 (a b : F2) : Prop := a = .law ∧ b = .inst
def L2 (a : F2) : Prop := a = .law
def I2 (a b : F2) : Prop := a = .inst ∧ b = .law

/-- Proposition 3.6 (consistency). In the two-element model, grounding is
a strict partial order, P1 and P2 hold, explanation is irreflexive, and
there is a law with an instance. -/
theorem proposition_3_6 :
    (∀ f, ¬ G2 f f) ∧ (∀ f g h, G2 f g → G2 g h → G2 f h) ∧
    (∀ l i, L2 l → I2 i l → G2 i l) ∧ (∀ l i, L2 l → I2 i l → E2 l i) ∧
    (∀ f, ¬ E2 f f) ∧ (∃ l i, L2 l ∧ I2 i l) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨.law, .inst, rfl, rfl, rfl⟩⟩
  · intro f ⟨h1, h2⟩; rw [h1] at h2; cases h2
  · intro f g h ⟨_, h2⟩ ⟨h3, _⟩; rw [h2] at h3; cases h3
  · intro l i _ hi; exact hi
  · intro l i hl hi; exact ⟨hl, hi.1⟩
  · intro f ⟨h1, h2⟩; rw [h1] at h2; cases h2

end Philosophy.MET_12

#print axioms Philosophy.MET_12.proposition_3_1
#print axioms Philosophy.MET_12.proposition_3_2
#print axioms Philosophy.MET_12.theorem_3_4
#print axioms Philosophy.MET_12.corollary_3_5
#print axioms Philosophy.MET_12.proposition_3_6
