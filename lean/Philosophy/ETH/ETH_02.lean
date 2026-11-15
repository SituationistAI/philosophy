/-
ETH-02 · The Consequentializing Equivalence
Formalization of Lemma 3.1, Theorems 3.3, 3.4 and 3.5, Corollary 3.6 and
Propositions 4.2, 4.3, 4.4 and 4.6.

A choice structure (Definition 2.1) gives, for each agent and situation, a
finite nonempty menu of options and, for each option, its outcome. A deontic
theory (Definition 2.2) says which options are permissible. A consequentialist
theory (Definition 2.3) is given by an agent-relative value function on
outcomes and permits exactly the options whose outcomes are ranked highest by
the agent's value function. Outcomes are act-inclusive (Definition 2.5) when
the outcome of an option records the situation and the option.

What this file establishes. Given act-inclusive outcomes, a deontic theory is
extensionally equivalent to some consequentialist theory if and only if it
permits only available options and has no dilemmas (Theorem 3.5); every
consequentialist theory is a deontic theory of that kind (Theorem 3.4); and the
two translations are mutually inverse up to extensional equivalence
(Corollary 3.6). With coarse, menu-independent outcomes, consequentialist
theories satisfy contraction consistency (Proposition 4.2), Horton's
all-or-nothing verdicts cannot be represented (Proposition 4.3), and an
agent-centered constraint cannot be represented by an agent-neutral value on
the number of killings (Proposition 4.4). A lexical priority of constraints
over the good is represented by a finite penalty (Proposition 4.6).

What it does not establish. That outcomes may be individuated act-inclusively
(Assumption 2.6) and that there are no moral dilemmas (Assumption 2.7) are
premises; they appear as hypotheses of the theorems. Nothing here settles
which value function, or which deontic theory, is correct, and nothing
concerns choice under risk.
-/

namespace Philosophy.ETH_02

/-! ## Framework -/

/-- Definition 2.1. A finite choice structure: menus are finite (lists) and
nonempty; every option in a situation has an outcome for the agent. -/
structure ChoiceStructure (Agent Sit Opt Out : Type) where
  menu : Agent → Sit → List Opt
  outcome : Agent → Sit → Opt → Out
  nonempty : ∀ i s, menu i s ≠ []

section
variable {Agent Sit Opt Out : Type}

/-- Definition 2.2. A deontic theory assigns permissibility to options. -/
abbrev DeonticTheory (Agent Sit Opt : Type) := Agent → Sit → Opt → Prop

/-- Definition 2.2 (admissibility). Only available options are permitted. -/
def Admissible (C : ChoiceStructure Agent Sit Opt Out)
    (D : DeonticTheory Agent Sit Opt) : Prop :=
  ∀ i s a, D i s a → a ∈ C.menu i s

/-- Assumption 2.7 (as a property of theories). No dilemmas: in every
situation some available option is permissible. -/
def NoDilemmas (C : ChoiceStructure Agent Sit Opt Out)
    (D : DeonticTheory Agent Sit Opt) : Prop :=
  ∀ i s, ∃ a, a ∈ C.menu i s ∧ D i s a

/-- Definition 2.3. Agent-relative value functions. -/
abbrev ValueFunction (Agent Out : Type) := Agent → Out → Nat

/-- Definition 2.3. The consequentialist theory with value function `V`:
an option is permissible iff it is available and no available option has an
outcome the agent's value function ranks higher. -/
def maximizing (C : ChoiceStructure Agent Sit Opt Out) (V : ValueFunction Agent Out) :
    DeonticTheory Agent Sit Opt :=
  fun i s a => a ∈ C.menu i s ∧
    ∀ b, b ∈ C.menu i s → V i (C.outcome i s b) ≤ V i (C.outcome i s a)

/-- Definition 2.4. Extensional equivalence of deontic theories. -/
def Equivalent (D E : DeonticTheory Agent Sit Opt) : Prop :=
  ∀ i s a, D i s a ↔ E i s a

/-- Definition 2.5. Act-inclusive outcomes: the outcome of an option for an
agent records the situation and the option. -/
def ActInclusive (C : ChoiceStructure Agent Sit Opt Out) : Prop :=
  ∀ i s a s' a', C.outcome i s a = C.outcome i s' a' → s = s' ∧ a = a'

/-! ## The equivalence -/

/-- Lemma 3.1. Every value function attains a maximum on a finite nonempty
menu. -/
theorem finite_maximum {α : Type} (f : α → Nat) :
    ∀ l : List α, l ≠ [] → ∃ a, a ∈ l ∧ ∀ b, b ∈ l → f b ≤ f a
  | [], h => absurd rfl h
  | x :: t, _ => by
    cases t with
    | nil =>
      refine ⟨x, List.mem_cons_self _ _, ?_⟩
      intro b hb
      simp at hb
      subst hb
      exact Nat.le_refl _
    | cons y u =>
      obtain ⟨m, hm, hmax⟩ := finite_maximum f (y :: u) (by simp)
      by_cases hx : f m ≤ f x
      · refine ⟨x, List.mem_cons_self _ _, ?_⟩
        intro b hb
        cases List.mem_cons.mp hb with
        | inl h => subst h; exact Nat.le_refl _
        | inr h => exact Nat.le_trans (hmax b h) hx
      · refine ⟨m, List.mem_cons_of_mem _ hm, ?_⟩
        intro b hb
        cases List.mem_cons.mp hb with
        | inl h => subst h; omega
        | inr h => exact hmax b h

open Classical in
/-- Definition 3.2. The indicator value
function of a deontic theory: an outcome has value 1 for an agent if it is
the outcome of an option the theory permits that agent, and 0 otherwise. -/
noncomputable def indicator (C : ChoiceStructure Agent Sit Opt Out)
    (D : DeonticTheory Agent Sit Opt) : ValueFunction Agent Out :=
  fun i o => if ∃ s a, C.outcome i s a = o ∧ D i s a then 1 else 0

theorem indicator_le_one (C : ChoiceStructure Agent Sit Opt Out)
    (D : DeonticTheory Agent Sit Opt) (i : Agent) (o : Out) :
    indicator C D i o ≤ 1 := by
  unfold indicator; split <;> omega

/-- Theorem 3.3 (from deontology to consequentialism). Given act-inclusive
outcomes, every admissible deontic theory without dilemmas is extensionally
equivalent to the consequentialist theory whose value function is its
indicator. -/
theorem consequentialize (C : ChoiceStructure Agent Sit Opt Out)
    (D : DeonticTheory Agent Sit Opt)
    (hinc : ActInclusive C) (hadm : Admissible C D) (hnd : NoDilemmas C D) :
    Equivalent D (maximizing C (indicator C D)) := by
  intro i s a
  constructor
  · intro hD
    refine ⟨hadm i s a hD, fun b _ => ?_⟩
    have h1 : indicator C D i (C.outcome i s a) = 1 := by
      unfold indicator
      rw [if_pos ⟨s, a, rfl, hD⟩]
    rw [h1]
    exact indicator_le_one C D i _
  · intro ⟨_, hmax⟩
    obtain ⟨b, hb, hDb⟩ := hnd i s
    have hb1 : indicator C D i (C.outcome i s b) = 1 := by
      unfold indicator
      rw [if_pos ⟨s, b, rfl, hDb⟩]
    have h := hmax b hb
    rw [hb1] at h
    have ha : ∃ s' a', C.outcome i s' a' = C.outcome i s a ∧ D i s' a' := by
      apply Classical.byContradiction
      intro hn
      have h0 : indicator C D i (C.outcome i s a) = 0 := by
        unfold indicator
        rw [if_neg hn]
      omega
    obtain ⟨s', a', heq, hD'⟩ := ha
    obtain ⟨rfl, rfl⟩ := hinc i s' a' s a heq
    exact hD'

/-- Theorem 3.4 (from consequentialism to deontology). Every consequentialist
theory is an admissible deontic theory without dilemmas. -/
theorem deontologize (C : ChoiceStructure Agent Sit Opt Out)
    (V : ValueFunction Agent Out) :
    Admissible C (maximizing C V) ∧ NoDilemmas C (maximizing C V) := by
  refine ⟨fun _ _ _ h => h.1, fun i s => ?_⟩
  obtain ⟨a, ha, hmax⟩ :=
    finite_maximum (fun b => V i (C.outcome i s b)) (C.menu i s) (C.nonempty i s)
  exact ⟨a, ha, ha, hmax⟩

/-- Theorem 3.5 (the consequentializing equivalence). Given act-inclusive
outcomes, a deontic theory is extensionally equivalent to some
consequentialist theory if and only if it is admissible and has no
dilemmas. -/
theorem equivalence (C : ChoiceStructure Agent Sit Opt Out)
    (D : DeonticTheory Agent Sit Opt) (hinc : ActInclusive C) :
    (∃ V : ValueFunction Agent Out, Equivalent D (maximizing C V)) ↔
      (Admissible C D ∧ NoDilemmas C D) := by
  constructor
  · intro ⟨V, hV⟩
    obtain ⟨hadm, hnd⟩ := deontologize C V
    refine ⟨fun i s a hD => hadm i s a ((hV i s a).mp hD), fun i s => ?_⟩
    obtain ⟨a, ha, hm⟩ := hnd i s
    exact ⟨a, ha, (hV i s a).mpr hm⟩
  · intro ⟨hadm, hnd⟩
    exact ⟨indicator C D, consequentialize C D hinc hadm hnd⟩

/-- Corollary 3.6 (notational variants). The translation from value
functions to deontic theories and back returns a value function with the
same verdicts. Together with Theorem 3.3 (the other round trip), the two
translations are inverse up to extensional equivalence. -/
theorem round_trip (C : ChoiceStructure Agent Sit Opt Out)
    (V : ValueFunction Agent Out) (hinc : ActInclusive C) :
    Equivalent (maximizing C V) (maximizing C (indicator C (maximizing C V))) :=
  consequentialize C (maximizing C V) hinc (deontologize C V).1 (deontologize C V).2

/-! ## Coarse outcomes, agent-neutrality and lexical constraints -/

/-- Definition 4.1. Coarse outcomes: the outcome of an option does not depend
on the situation (menu) in which it is chosen. -/
def Coarse (C : ChoiceStructure Agent Sit Opt Out) (g : Agent → Opt → Out) : Prop :=
  ∀ i s a, C.outcome i s a = g i a

/-- Proposition 4.2 (contraction consistency). With coarse outcomes, an option
permitted by a consequentialist theory in a situation is permitted in any
situation whose menu contains it and is contained in the first menu. -/
theorem contraction (C : ChoiceStructure Agent Sit Opt Out) (g : Agent → Opt → Out)
    (hc : Coarse C g) (V : ValueFunction Agent Out) (i : Agent) (s s' : Sit) (a : Opt)
    (hsub : ∀ b, b ∈ C.menu i s' → b ∈ C.menu i s) (ha : a ∈ C.menu i s')
    (hperm : maximizing C V i s a) : maximizing C V i s' a := by
  refine ⟨ha, fun b hb => ?_⟩
  have h := hperm.2 b (hsub b hb)
  rw [hc, hc] at h ⊢
  exact h

end

/-- The options in Horton's all-or-nothing case. -/
inductive Rescue | none | one | both
  deriving DecidableEq

/-- Proposition 4.3 (Horton's case). No coarse value on the three options
yields the verdicts: in the three-option menu, saving none and saving both are
permissible and saving one is not; in the two-option menu without saving both,
saving one is permissible. -/
theorem horton_coarse :
    ¬ ∃ v : Rescue → Nat,
      (∀ b, b ∈ [Rescue.none, Rescue.one, Rescue.both] → v b ≤ v Rescue.none) ∧
      (∀ b, b ∈ [Rescue.none, Rescue.one, Rescue.both] → v b ≤ v Rescue.both) ∧
      ¬ (∀ b, b ∈ [Rescue.none, Rescue.one, Rescue.both] → v b ≤ v Rescue.one) ∧
      (∀ b, b ∈ [Rescue.none, Rescue.one] → v b ≤ v Rescue.one) := by
  intro ⟨v, hn, _, hone, hsmall⟩
  apply hone
  intro b hb
  have h1 := hsmall Rescue.none (by simp)
  have h2 := hn Rescue.both (by simp)
  have h3 := hn b hb
  omega

/-- Proposition 4.3 (continued). An act-inclusive value, which records whether
saving both was available, yields Horton's verdicts. -/
theorem horton_inclusive :
    ∃ v : Bool → Rescue → Nat,
      (∀ b, b ∈ [Rescue.none, Rescue.one, Rescue.both] → v true b ≤ v true Rescue.none) ∧
      (∀ b, b ∈ [Rescue.none, Rescue.one, Rescue.both] → v true b ≤ v true Rescue.both) ∧
      ¬ (∀ b, b ∈ [Rescue.none, Rescue.one, Rescue.both] → v true b ≤ v true Rescue.one) ∧
      (∀ b, b ∈ [Rescue.none, Rescue.one] → v false b ≤ v false Rescue.one) := by
  refine ⟨fun big r => if big && r == Rescue.one then 0 else 1, ?_, ?_, ?_, ?_⟩
  · intro b _; cases b <;> decide
  · intro b _; cases b <;> decide
  · intro h; have := h Rescue.none (by simp); revert this; decide
  · intro b _; cases b <;> decide

/-- Proposition 4.4 (agent-centered constraints). No agent-neutral value on
the total number of killings yields both verdicts: refrain from killing one to
prevent two killings by others (one killing ranked strictly below two), and
prevent one of two killings by others at no cost (one killing ranked at least
as high as two). An agent-relative value on (killings by the agent, killings
by others) yields both. -/
theorem constraint_needs_relativity :
    (¬ ∃ v : Nat → Nat, v 1 < v 2 ∧ v 2 ≤ v 1) ∧
    (∃ w : Nat → Nat → Nat, w 1 0 < w 0 2 ∧ w 0 2 ≤ w 0 1) := by
  refine ⟨fun ⟨v, h1, h2⟩ => by omega, ⟨fun m o => 10 - 5 * m - o, by decide, by decide⟩⟩

section
variable {α : Type}

/-- Definition 4.5 (lexical constraint theory). An option is permissible iff
it minimizes the agent's own constraint violations `c` and, among options
that do, maximizes the impersonal good `g`. -/
def lexical (menu : List α) (c g : α → Nat) (a : α) : Prop :=
  a ∈ menu ∧ ∀ b, b ∈ menu → c a ≤ c b ∧ (c b = c a → g b ≤ g a)

/-- Definition 4.5 (weighted cost). A violation is penalized by `B + 1`, one
more than the greatest value of the good. -/
def weightedCost (B : Nat) (c g : α → Nat) (a : α) : Nat := (B + 1) * c a + (B - g a)

/-- Definition 4.5. The theory minimizing a cost (maximizing its negation). -/
def minimizing (menu : List α) (w : α → Nat) (a : α) : Prop :=
  a ∈ menu ∧ ∀ b, b ∈ menu → w a ≤ w b

theorem weighted_compare (B : Nat) (c g : α → Nat) (hg : ∀ x, g x ≤ B) (a b : α) :
    weightedCost B c g a ≤ weightedCost B c g b ↔
      (c a ≤ c b ∧ (c b = c a → g b ≤ g a)) := by
  unfold weightedCost
  have hga := hg a
  have hgb := hg b
  by_cases hlt : c a < c b
  · have : (B + 1) * (c a + 1) ≤ (B + 1) * c b := Nat.mul_le_mul_left _ hlt
    rw [Nat.mul_succ] at this
    constructor
    · intro _; exact ⟨Nat.le_of_lt hlt, fun h => by omega⟩
    · intro _; omega
  · by_cases hgt : c b < c a
    · have : (B + 1) * (c b + 1) ≤ (B + 1) * c a := Nat.mul_le_mul_left _ hgt
      rw [Nat.mul_succ] at this
      constructor
      · intro h; omega
      · intro ⟨h, _⟩; omega
    · have heq : c a = c b := by omega
      rw [heq]
      constructor
      · intro h; exact ⟨Nat.le_refl _, fun _ => by omega⟩
      · intro ⟨_, h⟩; have := h rfl; omega

/-- Proposition 4.6 (finite representation of lexical constraints). If the
good is bounded by `B`, the lexical constraint theory coincides with the
theory that minimizes the weighted cost, in which each violation counts for
`B + 1` units of the good. -/
theorem lexical_finite (menu : List α) (B : Nat) (c g : α → Nat)
    (hg : ∀ x, g x ≤ B) (a : α) :
    lexical menu c g a ↔ minimizing menu (weightedCost B c g) a := by
  unfold lexical minimizing
  constructor
  · intro ⟨ha, h⟩
    exact ⟨ha, fun b hb => (weighted_compare B c g hg a b).mpr (h b hb)⟩
  · intro ⟨ha, h⟩
    exact ⟨ha, fun b hb => (weighted_compare B c g hg a b).mp (h b hb)⟩

end

end Philosophy.ETH_02

#print axioms Philosophy.ETH_02.equivalence
#print axioms Philosophy.ETH_02.round_trip
#print axioms Philosophy.ETH_02.horton_coarse
#print axioms Philosophy.ETH_02.lexical_finite
