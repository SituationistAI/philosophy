/-
MND-05 · Zombies Are Conceivable but Impossible
Formalization of Lemma 3.2 and Theorem 3.3.

What this file establishes. Given physicalism (Assumption 3.1) and the ideal
conceivability of the zombie hypothesis, the unrestricted principle that
whatever is ideally conceivable is possible (Z2) fails. It does not establish
either physicalism or the conceivability of zombies; it shows that the two,
together, are inconsistent with (Z2).
-/

namespace Philosophy.MND_05

/-- Propositions. -/
axiom Proposition : Type

/-- Ideal conceivability and metaphysical possibility. -/
axiom Conceivable : Proposition → Prop
axiom Possible : Proposition → Prop

/-- The zombie hypothesis: a world physically identical to ours without
consciousness. -/
axiom zombie : Proposition

/-- Assumption 3.1 (physicalism), in the form used by Lemma 3.2: the physical
facts necessitate consciousness, so the zombie hypothesis is impossible. -/
axiom physicalism : ¬ Possible zombie

/-- Lemma 3.2. A zombie world is not possible. -/
theorem zombie_impossible : ¬ Possible zombie := physicalism

/-- Theorem 3.3. If zombies are ideally conceivable, (Z2) fails. -/
theorem z2_fails (conceivable_zombie : Conceivable zombie) :
    ¬ (∀ p, Conceivable p → Possible p) :=
  fun z2 => zombie_impossible (z2 zombie conceivable_zombie)

/-- The anti-zombie hypothesis: a world physically identical to ours in which
the physical facts necessitate consciousness (Section 4). -/
axiom antiZombie : Proposition

/-- Proposition 4.2 (parity). If both hypotheses are conceivable and the
possibility of the anti-zombie hypothesis excludes that of the zombie
hypothesis (as it does in S5), unrestricted (Z2) fails. Physicalism is not
used. -/
theorem parity (cz : Conceivable zombie) (ca : Conceivable antiZombie)
    (incompatible : Possible antiZombie → ¬ Possible zombie) :
    ¬ (∀ p, Conceivable p → Possible p) :=
  fun z2 => incompatible (z2 antiZombie ca) (z2 zombie cz)

end Philosophy.MND_05

#print axioms Philosophy.MND_05.z2_fails
#print axioms Philosophy.MND_05.parity
