/-
MET-06 · A Solution to the Special Composition Question
Formalization of Theorem 4.1, Proposition 4.2, Corollaries 4.3 and 4.4,
Lemma 7.1, Corollary 7.2 and Proposition 7.3.

Simples, perturbations and outcomes are primitive types. A plurality is
represented by its membership predicate. The admissible perturbations of a
plurality (Definition 3.2) and the fate of each member of a plurality under
a perturbation (Definition 3.3) are primitives. A plurality shares a common
fate (Definition 3.4) if it is non-empty and, under every admissible
perturbation, all its members have the same fate. A composition rule
(Definition 3.5) is any predicate of pluralities.

What this file establishes. Every composition rule satisfying Unity (P1),
Parity (P2) and Ordinary Objects (P3), stated as hypotheses, holds of exactly
the pluralities that share a common fate; the common-fate rule satisfies the
three principles; given Assumptions 3.6 and 3.7, tables and organisms
compose, the scattered plurality does not, and both universalism and
nihilism are false. Section 7: every sorites series of pluralities that
begins with a composing plurality and ends with a non-composing one has a
sharp transition, and the transition is unique when composition is a
threshold on a coupling magnitude that decreases along the series.

What it does not establish. It does not establish the three principles
(defended in Section 5 of the manuscript), nor the empirical Assumptions 3.6
and 3.7, nor that the boundary located by Lemma 7.1 can be known.
-/

namespace Philosophy.MET_06

/-- Definition 3.1. Simples. -/
axiom Simple : Type

/-- Definition 3.1. A plurality, represented by its membership predicate. -/
abbrev Plurality := Simple → Prop

/-- Perturbations of the relevant dynamics. -/
axiom Perturbation : Type

/-- Outcomes: the coarse-grained fates a simple may have. -/
axiom Outcome : Type

/-- Definition 3.2. `Admissible xx p`: `p` is an admissible perturbation of
the plurality `xx`, that is, an intervention on some of its members of a
magnitude within the ambient regime of its environment. -/
axiom Admissible : Plurality → Perturbation → Prop

/-- Definition 3.3. `fate xx p x`: the fate of the member `x` of `xx` under
the perturbation `p`, when `xx` evolves under its internal dynamics. -/
axiom fate : Plurality → Perturbation → Simple → Outcome

/-- Definition 3.4. A plurality shares a common fate if it is non-empty and
every admissible perturbation leaves all its members with the same fate. -/
def CommonFate (xx : Plurality) : Prop :=
  (∃ x, xx x) ∧
    ∀ p, Admissible xx p → ∀ x y, xx x → xx y → fate xx p x = fate xx p y

/-- Assumption 3.6. A table (whose simples are given by `table`) shares a
common fate, and has at least two simples. -/
axiom table : Plurality
axiom table_commonFate : CommonFate table
axiom table_two : ∃ x y, table x ∧ table y ∧ x ≠ y

/-- Assumption 3.6. An organism shares a common fate. -/
axiom organism : Plurality
axiom organism_commonFate : CommonFate organism

/-- Assumption 3.7. A scattered plurality (one simple of a table and one of
a distant star, say) does not share a common fate: some admissible
perturbation leaves two of its members with different fates. -/
axiom scattered : Plurality
axiom scattered_divergent : ∃ p, Admissible scattered p ∧
  ∃ x y, scattered x ∧ scattered y ∧ fate scattered p x ≠ fate scattered p y

/-- P1 (Unity). -/
def Unity (rho : Plurality → Prop) : Prop := ∀ xx, rho xx → CommonFate xx

/-- P2 (Parity). -/
def Parity (rho : Plurality → Prop) : Prop :=
  ∀ xx yy, CommonFate xx → CommonFate yy → (rho xx ↔ rho yy)

/-- P3 (Ordinary objects): the simples of the table compose something. -/
def Ordinary (rho : Plurality → Prop) : Prop := rho table

/-- Theorem 4.1 (uniqueness). Any composition rule satisfying P1, P2 and P3
holds of exactly the pluralities that share a common fate. -/
theorem uniqueness (rho : Plurality → Prop)
    (h1 : Unity rho) (h2 : Parity rho) (h3 : Ordinary rho) :
    ∀ xx, rho xx ↔ CommonFate xx := by
  intro xx
  constructor
  · exact h1 xx
  · intro hcf
    exact (h2 xx table hcf table_commonFate).mpr h3

/-- Proposition 4.2. The common-fate rule satisfies P1, P2 and P3. -/
theorem commonFate_adequate :
    Unity CommonFate ∧ Parity CommonFate ∧ Ordinary CommonFate :=
  ⟨fun _ h => h, fun _ _ hx hy => ⟨fun _ => hy, fun _ => hx⟩, table_commonFate⟩

/-- The scattered plurality does not share a common fate. -/
theorem scattered_not_commonFate : ¬ CommonFate scattered := by
  intro ⟨_, h⟩
  obtain ⟨p, hp, x, y, hx, hy, hne⟩ := scattered_divergent
  exact hne (h p hp x y hx hy)

/-- Corollary 4.3. Under any rule satisfying P1–P3, the simples of the table
and those of the organism compose, and the scattered plurality does not. -/
theorem ordinary_objects (rho : Plurality → Prop)
    (h1 : Unity rho) (h2 : Parity rho) (h3 : Ordinary rho) :
    rho table ∧ rho organism ∧ ¬ rho scattered := by
  have hu := uniqueness rho h1 h2 h3
  exact ⟨(hu table).mpr table_commonFate, (hu organism).mpr organism_commonFate,
    fun h => scattered_not_commonFate ((hu scattered).mp h)⟩

/-- Universalism: every non-empty plurality composes something. -/
def Universalism (rho : Plurality → Prop) : Prop := ∀ xx, (∃ x, xx x) → rho xx

/-- Nihilism: only pluralities with a single member compose something. -/
def Nihilism (rho : Plurality → Prop) : Prop :=
  ∀ xx, rho xx → ∀ x y, xx x → xx y → x = y

/-- Corollary 4.4. Under any rule satisfying P1–P3, universalism and
nihilism are both false. -/
theorem neither_extreme (rho : Plurality → Prop)
    (h1 : Unity rho) (h2 : Parity rho) (h3 : Ordinary rho) :
    ¬ Universalism rho ∧ ¬ Nihilism rho := by
  obtain ⟨_, _, hs⟩ := ordinary_objects rho h1 h2 h3
  constructor
  · intro hU
    obtain ⟨_, _, x, _, hx, _, _⟩ := scattered_divergent
    exact hs (hU scattered ⟨x, hx⟩)
  · intro hN
    obtain ⟨x, y, hx, hy, hne⟩ := table_two
    exact hne (hN table h3 x y hx hy)

/-- Lemma 7.1 (sharp transition). If a property holds at the start of a
finite series and fails at its end, there is a last point at which it holds
followed by a point at which it fails. -/
theorem sharp_transition (P : Nat → Prop) (n : Nat) (h0 : P 0) (hn : ¬ P n) :
    ∃ k, k < n ∧ P k ∧ ¬ P (k + 1) := by
  induction n with
  | zero => exact absurd h0 hn
  | succ m ih =>
    by_cases hm : P m
    · exact ⟨m, Nat.lt_succ_self m, hm, hn⟩
    · obtain ⟨k, hk, hpk, hpk1⟩ := ih hm
      exact ⟨k, Nat.lt_succ_of_lt hk, hpk, hpk1⟩

/-- Proposition 7.3 (uniqueness of the transition). If membership is a
threshold `θ` on a coupling magnitude `c` that does not increase along the
series, there is at most one transition point. -/
theorem unique_transition (c : Nat → Nat) (θ : Nat)
    (anti : ∀ a b, a ≤ b → c b ≤ c a) (k j : Nat)
    (hk : θ ≤ c k ∧ ¬ θ ≤ c (k + 1)) (hj : θ ≤ c j ∧ ¬ θ ≤ c (j + 1)) :
    k = j := by
  apply Classical.byContradiction
  intro hne
  cases Nat.lt_or_gt_of_ne hne with
  | inl hlt =>
    have := anti (k + 1) j hlt
    omega
  | inr hgt =>
    have := anti (j + 1) k hgt
    omega

/-- Corollary 7.2. In a sorites series of pluralities that begins with a
plurality sharing a common fate and ends with one that does not, any rule
satisfying P1–P3 has a sharp boundary. -/
theorem composition_sharp (rho : Plurality → Prop)
    (h1 : Unity rho) (h2 : Parity rho) (h3 : Ordinary rho)
    (s : Nat → Plurality) (n : Nat)
    (h0 : CommonFate (s 0)) (hn : ¬ CommonFate (s n)) :
    ∃ k, k < n ∧ rho (s k) ∧ ¬ rho (s (k + 1)) := by
  have hu := uniqueness rho h1 h2 h3
  obtain ⟨k, hk, hp, hq⟩ := sharp_transition (fun i => CommonFate (s i)) n h0 hn
  exact ⟨k, hk, (hu (s k)).mpr hp, fun h => hq ((hu (s (k + 1))).mp h)⟩

end Philosophy.MET_06

#print axioms Philosophy.MET_06.uniqueness
#print axioms Philosophy.MET_06.ordinary_objects
#print axioms Philosophy.MET_06.neither_extreme
#print axioms Philosophy.MET_06.sharp_transition
#print axioms Philosophy.MET_06.unique_transition
