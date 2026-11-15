/-
REL-20 · Proportionality and Eternal Punishment
Formalization of Lemma 3.1, Proposition 3.2, Lemma 3.3, Theorem 3.4 and
Corollary 3.5.

A punishment is a schedule assigning to each period a natural number of
units of harm; its cumulative amount after `n` periods is the sum over the
first `n` periods. Desert is represented by predicates on cumulative amounts:
`Merits w m` says that cumulative punishment `m` is within the desert of the
wrong `w`, and `Deserves x m` that it is within the desert of the person `x`.

What this file establishes. Eternal punishment (at least one unit in every
period, without end) has unbounded cumulative amount (Lemma 3.1), so it is
not within the desert of any wrong whose desert is bounded (Proposition 3.2).
Given that every human wrong has bounded desert (Assumption 2.3), that the
bounded deserts of a finite record aggregate to a bounded desert
(Assumption 2.4) and that a just punisher keeps cumulative punishment within
desert at every time (Principle P1), a just God inflicts eternal punishment
on no one (Theorem 3.4), and hell, in the sense of Definition 2.5, is
unoccupied (Corollary 3.5).

What it does not establish. Any of the three premises; that God exists or is
just; or anything about annihilation or universal reconciliation.
-/

namespace Philosophy.REL_20

/-- Persons (human beings, judged for the record of a finite life). -/
axiom Person : Type

/-- Wrongs. -/
axiom Wrong : Type

/-- Assumption 2.4, first part. The record of a person: the finitely many
wrongs committed in a human life (finitude is carried by `List`). -/
axiom record : Person → List Wrong

/-- `Merits w m`: cumulative punishment of amount `m` is within the desert
of the wrong `w`. -/
axiom Merits : Wrong → Nat → Prop

/-- `Deserves x m`: cumulative punishment of amount `m` is within the desert
of the person `x`, for her record. -/
axiom Deserves : Person → Nat → Prop

/-- Definition 2.1. A punishment schedule: units of harm in each period. -/
def Schedule : Type := Nat → Nat

/-- Definition 2.1. Cumulative amount of a schedule after `n` periods. -/
def cum (P : Schedule) : Nat → Nat
  | 0 => 0
  | n + 1 => cum P n + P n

/-- Definition 2.2. A schedule is eternal if it inflicts at least one unit of
harm in every period, without end. -/
def Eternal (P : Schedule) : Prop := ∀ t, 1 ≤ P t

/-- A desert predicate is bounded if some amount exceeds everything within it. -/
def Bounded (M : Nat → Prop) : Prop := ∃ b, ∀ m, M m → m ≤ b

/-- Assumption 2.3 (finite wrongs). Every wrong a human being commits has
bounded desert. -/
axiom finite_wrong : ∀ w, Bounded (Merits w)

/-- Assumption 2.4, second part (aggregation). If every wrong in a person's
record has bounded desert, so does the person. -/
axiom aggregation :
  ∀ x, (∀ w, w ∈ record x → Bounded (Merits w)) → Bounded (Deserves x)

/-- God is just. -/
axiom Just : Prop

/-- `Inflicts x P`: God inflicts the schedule `P` on `x`. -/
axiom Inflicts : Person → Schedule → Prop

/-- Principle P1 (proportionality). A just punisher keeps the cumulative
punishment of every person within her desert at every time. -/
axiom proportionality :
  Just → ∀ x P, Inflicts x P → ∀ n, Deserves x (cum P n)

/-- Definition 2.5. `x` is in hell if God inflicts an eternal punishment on
`x`. -/
def InHell (x : Person) : Prop := ∃ P, Inflicts x P ∧ Eternal P

/-- Lemma 3.1. Eternal punishment is unbounded: after `n` periods its
cumulative amount is at least `n`. -/
theorem eternal_unbounded (P : Schedule) (h : Eternal P) :
    ∀ n, n ≤ cum P n := by
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    show k + 1 ≤ cum P k + P k
    have := h k
    omega

/-- Lemma 3.1, general form: no bounded predicate contains every cumulative
amount of an eternal punishment. -/
theorem bounded_excludes_eternal (M : Nat → Prop) (hM : Bounded M)
    (P : Schedule) (hP : Eternal P) : ¬ ∀ n, M (cum P n) := by
  intro hall
  obtain ⟨b, hb⟩ := hM
  have h1 := hb _ (hall (b + 1))
  have h2 := eternal_unbounded P hP (b + 1)
  omega

/-- Proposition 3.2. No finite wrong merits eternal punishment. -/
theorem no_wrong_merits_eternal (w : Wrong) (P : Schedule) (hP : Eternal P) :
    ¬ ∀ n, Merits w (cum P n) :=
  bounded_excludes_eternal (Merits w) (finite_wrong w) P hP

/-- Lemma 3.3. Every person's desert is bounded. -/
theorem person_bounded (x : Person) : Bounded (Deserves x) :=
  aggregation x (fun w _ => finite_wrong w)

/-- Theorem 3.4. A just God inflicts eternal punishment on no one. -/
theorem no_eternal_punishment (hJ : Just) (x : Person) (P : Schedule)
    (hI : Inflicts x P) : ¬ Eternal P := fun hP =>
  bounded_excludes_eternal (Deserves x) (person_bounded x) P hP
    (proportionality hJ x P hI)

/-- Corollary 3.5 (empty hell). If God is just, no one is in hell. -/
theorem empty_hell (hJ : Just) : ∀ x, ¬ InHell x := by
  intro x ⟨P, hI, hP⟩
  exact no_eternal_punishment hJ x P hI hP

end Philosophy.REL_20

#print axioms Philosophy.REL_20.no_wrong_merits_eternal
#print axioms Philosophy.REL_20.empty_hell
