/-
MTE-19 · Moral Progress Is Measurable
Formalization of Theorem 3.1, Propositions 3.2, 3.3 and 3.4, and
Proposition 4.2.

A moral circle is the set of beings to whom a society's effective norms give
due consideration (Definition 2.1). The standard is the correct circle, the
beings who are owed consideration, fixed independently of any society's
norms (Definition 2.2, Assumption 2.3). The beings relevant to a comparison
form a finite list. The measure of a circle is the number of relevant
beings in the standard that it includes (Definition 2.4). One circle is a
progress over another if it includes every standard being the other
includes, and at least one more (Definition 2.5).

What this file establishes. Progress strictly increases the measure
(Theorem 3.1); progress is irreflexive and transitive (Proposition 3.2);
any two circles are comparable by the measure (Proposition 3.3); and under
a standard fixed by the latest stage of a history, no history can end in a
regress (Proposition 3.4). A concrete history shows that the fixed standard
does register a regress after a progress (Proposition 4.2), so the
standard does not make progress steady or irreversible.

What it does not establish. It does not establish which beings belong to
the standard (ETH-07, MTE-01), or any historical claim about which circles
societies have had; those are argued in Sections 3 and 4. Graded
consideration (Remark 2.6) is not formalized.
-/

namespace Philosophy.MTE_19

/-- Beings. -/
axiom Being : Type

/-- Definition 2.1. A moral circle: the beings given due consideration. -/
abbrev Circle := Being → Bool

/-- Definition 2.2. The standard: the correct circle. Assumption 2.3 is that
it is fixed independently of the norms of any society, which is reflected in
its being a constant rather than a function of a history. -/
axiom standard : Circle

/-- The finite list of beings relevant to the comparison. -/
axiom relevant : List Being

/-- Counting the beings of a list that satisfy a test. -/
def count (p : Being → Bool) : List Being → Nat
  | [] => 0
  | b :: l => (if p b then 1 else 0) + count p l

/-- Definition 2.4. The measure of a circle relative to a standard. -/
noncomputable def measureBy (s : Circle) (c : Circle) : Nat :=
  count (fun b => c b && s b) relevant

/-- Definition 2.4, with the fixed standard. -/
noncomputable def measure (c : Circle) : Nat := measureBy standard c

/-- Definition 2.5. Progress from circle `c` to circle `d`. -/
def Progress (c d : Circle) : Prop :=
  (∀ b, standard b = true → c b = true → d b = true) ∧
  ∃ b, b ∈ relevant ∧ standard b = true ∧ d b = true ∧ c b = false

theorem count_mono (p q : Being → Bool) (h : ∀ b, p b = true → q b = true) :
    ∀ l, count p l ≤ count q l
  | [] => Nat.le_refl 0
  | b :: l => by
    have ih := count_mono p q h l
    simp only [count]
    cases hp : p b
    · cases q b <;> simp <;> omega
    · simp [h b hp]; omega

theorem count_strict (p q : Being → Bool) (h : ∀ b, p b = true → q b = true) :
    ∀ l, (∃ b, b ∈ l ∧ q b = true ∧ p b = false) → count p l < count q l
  | [], ⟨_, hb, _⟩ => absurd hb (List.not_mem_nil _)
  | b :: l, ⟨x, hx, hqx, hpx⟩ => by
    have hm := count_mono p q h l
    simp only [count]
    cases List.mem_cons.mp hx with
    | inl he =>
      subst he
      simp [hqx, hpx]; omega
    | inr ht =>
      have ih := count_strict p q h l ⟨x, ht, hqx, hpx⟩
      cases hp : p b
      · cases q b <;> simp <;> omega
      · simp [h b hp]; omega

/-- Theorem 3.1. Progress strictly increases the measure. -/
theorem progress_increases (c d : Circle) (h : Progress c d) :
    measure c < measure d := by
  obtain ⟨hinc, b, hb, hs, hd, hc⟩ := h
  apply count_strict
  · intro x hx
    cases hcx : c x <;> cases hsx : standard x <;> simp_all
  · exact ⟨b, hb, by simp [hd, hs], by simp [hc]⟩

/-- Proposition 3.2 (a). No circle is a progress over itself. -/
theorem progress_irrefl (c : Circle) : ¬ Progress c c :=
  fun ⟨_, _, _, _, hd, hc⟩ => by rw [hd] at hc; exact Bool.noConfusion hc

/-- Proposition 3.2 (b). Progress is transitive. -/
theorem progress_trans (c d e : Circle) (h1 : Progress c d) (h2 : Progress d e) :
    Progress c e := by
  obtain ⟨i1, b, hb, hs, hd, hc⟩ := h1
  obtain ⟨i2, _⟩ := h2
  exact ⟨fun x hs hx => i2 x hs (i1 x hs hx), b, hb, hs, i2 b hs hd, hc⟩

/-- Proposition 3.3. Any two circles are comparable by the measure. -/
theorem comparable (c d : Circle) : measure c ≤ measure d ∨ measure d ≤ measure c :=
  Nat.le_total _ _

/-- Proposition 3.4. If the standard is fixed by the latest stage of a
history, no earlier stage measures higher than the latest: no history can
end in a regress. -/
theorem latest_standard_no_regress (h : Nat → Circle) (t n : Nat) :
    measureBy (h n) (h t) ≤ measureBy (h n) (h n) := by
  apply count_mono
  intro b hb
  cases ht : h t b <;> cases hn : h n b <;> simp_all

end Philosophy.MTE_19

namespace Philosophy.MTE_19.Example

/-! Proposition 4.2: a concrete history with three relevant beings, all in
the standard, in which a progress is followed by a regress. -/

def standard : Nat → Bool := fun _ => true
def relevant : List Nat := [0, 1, 2]

def measure (c : Nat → Bool) : Nat :=
  (relevant.filter (fun b => c b && standard b)).length

def Progress (c d : Nat → Bool) : Prop :=
  (∀ b, standard b = true → c b = true → d b = true) ∧
  ∃ b, b ∈ relevant ∧ standard b = true ∧ d b = true ∧ c b = false

/-- The history: beings 0; then 0 and 1; then 0 again. -/
def stage : Nat → Nat → Bool
  | 0, b => b == 0
  | 1, b => b == 0 || b == 1
  | _, b => b == 0

/-- Proposition 4.2. The fixed standard registers a progress from stage 0 to
stage 1 and a regress from stage 1 to stage 2. -/
theorem progress_then_regress :
    Progress (stage 0) (stage 1) ∧ Progress (stage 2) (stage 1) ∧
    measure (stage 2) < measure (stage 1) := by
  refine ⟨⟨?_, 1, by decide, rfl, rfl, rfl⟩, ⟨?_, 1, by decide, rfl, rfl, rfl⟩, by decide⟩
  · intro b _ h; simp [stage] at h ⊢; omega
  · intro b _ h; simp [stage] at h ⊢; omega

end Philosophy.MTE_19.Example

#print axioms Philosophy.MTE_19.progress_increases
#print axioms Philosophy.MTE_19.latest_standard_no_regress
#print axioms Philosophy.MTE_19.Example.progress_then_regress
