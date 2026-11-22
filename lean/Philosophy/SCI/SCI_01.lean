/-
SCI-01 · The Demarcation Problem Revisited
Formalization of Lemmas 4.1 and 4.2, Theorems 4.3 and 4.4,
Proposition 4.5 and Corollary 4.6.

Time is discrete. For a given false claim, an enterprise's checks are
represented by the times at which they would refute it, and the record
(Definition 3.1) contains the claim from the time of its admission until a
refutation removes it. An enterprise's record is self-cleansing if every
false claim, whenever admitted, is eventually removed (Definition 3.3); its
error-correction is standing if, for every false claim, refutations recur
without a last occasion (Definition 3.4).

What this file establishes. Without refutations an admitted error persists
forever; with standing correction every admitted error is eventually
removed; and a record is self-cleansing exactly when its correction is
standing. Given Principle P3 (the point of demarcation), an enterprise is a
science exactly when its error-correction is standing. Given Assumption 3.5
(twin enterprises), no criterion that depends only on the content of an
enterprise is extensionally adequate. It does not establish Principle P3,
Assumption 3.5, or that peer review, replication and public criticism are
the institutions that realize standing correction; these are defended in
Sections 3 to 5 of the manuscript.
-/

namespace Philosophy.SCI_01

/-- Definition 3.1. The record for a single claim admitted at time `t0`,
under a refutation schedule `ref`: the claim is in the record at its
admission and stays until a refutation removes it. -/
def inRec (ref : Nat → Bool) (t0 : Nat) : Nat → Bool
  | 0 => t0 == 0
  | t + 1 => (inRec ref t0 t && !ref t) || (t + 1 == t0)

/-- The claim is in the record at its admission time. -/
theorem admitted (ref : Nat → Bool) (t0 : Nat) : inRec ref t0 t0 = true := by
  cases t0 with
  | zero => simp [inRec]
  | succ n => simp [inRec]

/-- Lemma 4.1 (Persistence). If no refutation occurs from the admission time
on, the claim stays in the record at every later time. -/
theorem persistence (ref : Nat → Bool) (t0 : Nat)
    (h : ∀ s, s ≥ t0 → ref s = false) : ∀ t, t ≥ t0 → inRec ref t0 t = true := by
  intro t ht
  induction t with
  | zero =>
    have : t0 = 0 := by omega
    subst this; simp [inRec]
  | succ n ih =>
    by_cases hn : n + 1 = t0
    · subst hn; exact admitted ref (n + 1)
    · have hn' : n ≥ t0 := by omega
      simp [inRec, ih hn', h n hn']

/-- Lemma 4.2 (Elimination). If a refutation occurs at some time at or after
admission, the claim is out of the record at the next time. -/
theorem elimination (ref : Nat → Bool) (t0 s : Nat) (hs : s ≥ t0)
    (hr : ref s = true) : inRec ref t0 (s + 1) = false := by
  have : (s + 1 == t0) = false := by
    simp; omega
  simp [inRec, hr, this]

/-- Definition 3.3. Self-cleansing for a claim: whenever it is admitted, it is
eventually out of the record. -/
def SelfCleansingFor (ref : Nat → Bool) : Prop :=
  ∀ t0, ∃ s, s ≥ t0 ∧ inRec ref t0 s = false

/-- Definition 3.4. Standing correction for a claim: refutations recur
without a last occasion. -/
def StandingFor (ref : Nat → Bool) : Prop :=
  ∀ t, ∃ s, s ≥ t ∧ ref s = true

/-- Theorem 4.3. A record is self-cleansing for a claim if and only if the
correction of that claim is standing. -/
theorem cleansing_iff_standing (ref : Nat → Bool) :
    SelfCleansingFor ref ↔ StandingFor ref := by
  constructor
  · intro hc t
    apply Classical.byContradiction
    intro hno
    have h : ∀ s, s ≥ t → ref s = false := by
      intro s hs
      cases hrs : ref s with
      | false => rfl
      | true => exact absurd ⟨s, hs, hrs⟩ hno
    obtain ⟨s, hs, hout⟩ := hc t
    have := persistence ref t h s hs
    rw [this] at hout
    exact Bool.noConfusion hout
  · intro hst t0
    obtain ⟨s, hs, hr⟩ := hst t0
    exact ⟨s + 1, by omega, elimination ref t0 s hs hr⟩

/-- Primitive: enterprises (Principle P1: the unit of demarcation). -/
axiom Enterprise : Type
/-- Primitive: claims. -/
axiom Claim : Type
/-- Primitive: the truth value of a claim. -/
axiom truth : Claim → Bool
/-- Primitive: the times at which an enterprise's checks would refute a claim. -/
axiom refutes : Enterprise → Claim → Nat → Bool
/-- Primitive: being a science. -/
axiom Science : Enterprise → Prop

/-- Definition 3.3. An enterprise is self-cleansing if its record is
self-cleansing for every false claim. -/
def SelfCleansing (e : Enterprise) : Prop :=
  ∀ c, truth c = false → SelfCleansingFor (refutes e c)

/-- Definition 3.4. Institutionalized (standing) error-correction. -/
def InstitutionalizedEC (e : Enterprise) : Prop :=
  ∀ c, truth c = false → StandingFor (refutes e c)

/-- Principle P3 (The point of demarcation). An enterprise is a science
exactly when its record is self-cleansing. -/
axiom demarcation_point : ∀ e, Science e ↔ SelfCleansing e

/-- Theorem 4.4. An enterprise is a science if and only if it has
institutionalized error-correction. -/
theorem demarcation (e : Enterprise) : Science e ↔ InstitutionalizedEC e := by
  rw [demarcation_point]
  constructor
  · intro h c hc; exact (cleansing_iff_standing _).mp (h c hc)
  · intro h c hc; exact (cleansing_iff_standing _).mpr (h c hc)

/-- Primitive: the content of an enterprise (the claims it accepts). -/
axiom Content : Type
/-- Primitive: the content of each enterprise. -/
axiom content : Enterprise → Content

/-- Assumption 3.5 (Twin enterprises). There are two enterprises with the same
content of which one is a science and the other is not. -/
axiom twins : ∃ e1 e2, content e1 = content e2 ∧ Science e1 ∧ ¬ Science e2

/-- Proposition 4.5. No criterion that depends only on content is
extensionally adequate. -/
theorem no_content_criterion :
    ¬ ∃ crit : Content → Prop, ∀ e, Science e ↔ crit (content e) := by
  intro ⟨crit, h⟩
  obtain ⟨e1, e2, hc, s1, s2⟩ := twins
  exact s2 ((h e2).mpr (hc ▸ (h e1).mp s1))

/-- Corollary 4.6 (Closed canon). If an enterprise's checks of a false claim
cease at some time, a version of the claim admitted after that time is never
removed, and the enterprise is not a science. -/
theorem closed_canon (e : Enterprise) (c : Claim) (hc : truth c = false) (T : Nat)
    (hstop : ∀ s, s ≥ T → refutes e c s = false) :
    (∀ t, t ≥ T → inRec (refutes e c) T t = true) ∧ ¬ Science e := by
  refine ⟨persistence _ T hstop, fun hs => ?_⟩
  obtain ⟨s, hs', hr⟩ := (demarcation e).mp hs c hc T
  rw [hstop s hs'] at hr
  exact Bool.noConfusion hr

end Philosophy.SCI_01

#print axioms Philosophy.SCI_01.cleansing_iff_standing
#print axioms Philosophy.SCI_01.demarcation
#print axioms Philosophy.SCI_01.no_content_criterion
