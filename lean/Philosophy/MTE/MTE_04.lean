/-
MTE-04 · Why Be Moral? A Two-Case Argument
Formalization of Principle P1, Definitions 2.1 and 2.2, Assumption 2.3,
Theorem 3.1, Lemma 3.2, Corollary 3.3, Proposition 3.4 and
Proposition 3.5.

In each situation the agent has a list of options, and each option is
supported by moral reasons and by prudential reasons of some strength.
What one morally (prudentially) ought to do is the option the moral
(prudential) reasons favor over each alternative (Definition 2.2). The
question "why be moral?", asked of the option one morally ought to take,
has two readings (Principle P1), and an answer on a reading is a showing
that the reasons of the corresponding kind favor that option.

What this file establishes. On the moral reading the question is
answered by the definition of moral ought; on the prudential reading it is
answered in every convergent situation (Theorem 3.1). Where moral and
prudential reasons both favor an option, every positive weighting of the
two kinds favors it (Lemma 3.2, Corollary 3.3). Where they diverge, the
prudential answer is negative (Proposition 3.4), and over a life the
number of negative prudential answers is bounded by the number of
divergent situations (Proposition 3.5).

What it does not establish. It does not establish the convergence
assumption (Assumption 2.3), or that divergent situations are few, which
the manuscript argues for informally; nor does it say what is rational in
divergent situations, which is the subject of ETH-25.
-/

namespace Philosophy.MTE_04

section General

variable {A : Type}

/-- Definition 2.2 (general form). `a` is favored over each alternative in
`S` by the reasons of strength `w`. -/
def Best (w : A → Nat) (S : List A) (a : A) : Prop :=
  a ∈ S ∧ ∀ b, b ∈ S → b ≠ a → w b < w a

theorem best_unique (w : A → Nat) (S : List A) (a b : A)
    (ha : Best w S a) (hb : Best w S b) : a = b :=
  Classical.byContradiction fun hne => by
    have h1 := ha.2 b hb.1 (fun e => hne e.symm)
    have h2 := hb.2 a ha.1 hne
    omega

/-- Lemma 3.2 (dominance). If two kinds of reasons both favor `a`, every
positive weighting of them favors `a`. -/
theorem dominance (w₁ w₂ : A → Nat) (k₁ k₂ : Nat) (hk₁ : 0 < k₁)
    (S : List A) (a : A) (h₁ : Best w₁ S a) (h₂ : Best w₂ S a) :
    Best (fun x => k₁ * w₁ x + k₂ * w₂ x) S a := by
  refine ⟨h₁.1, fun b hb hne => ?_⟩
  have l1 : k₁ * w₁ b < k₁ * w₁ a := Nat.mul_lt_mul_of_pos_left (h₁.2 b hb hne) hk₁
  have l2 : k₂ * w₂ b ≤ k₂ * w₂ a := Nat.mul_le_mul_left k₂ (Nat.le_of_lt (h₂.2 b hb hne))
  exact Nat.add_lt_add_of_lt_of_le l1 l2

open Classical in
/-- The number of items in a list satisfying a property. -/
noncomputable def count (p : A → Prop) : List A → Nat
  | [] => 0
  | x :: l => (if p x then 1 else 0) + count p l

theorem count_mono (p q : A → Prop) (h : ∀ x, p x → q x) :
    ∀ l : List A, count p l ≤ count q l
  | [] => Nat.le_refl _
  | x :: l => by
      have ih := count_mono p q h l
      simp only [count]
      rcases Classical.em (p x) with hp | hp
      · have hq := h x hp
        simp only [hp, hq, if_true]
        omega
      · simp only [hp, if_false]
        split <;> omega

end General

/-- Situations in which an agent asks what to do. -/
axiom Sit : Type
/-- Acts. -/
axiom Act : Type
/-- The options open in a situation. -/
axiom opts : Sit → List Act
/-- Definition 2.1. The strength of the moral reasons for each act. -/
axiom moral : Sit → Act → Nat
/-- Definition 2.1. The strength of the prudential reasons for each act. -/
axiom prudential : Sit → Act → Nat

/-- Definition 2.2. Moral and prudential ought. -/
def MorallyOught (s : Sit) (a : Act) : Prop := Best (moral s) (opts s) a
def PrudentiallyOught (s : Sit) (a : Act) : Prop := Best (prudential s) (opts s) a

/-- Principle P1. The question "why should I do what I morally ought?" has
two readings: it asks for moral reasons or for prudential ones. -/
inductive Reading
  | moral
  | prudential

/-- An answer, on a reading, to the question why one should take `a`: the
reasons of that reading's kind favor `a` over each alternative. -/
def Answered : Reading → Sit → Act → Prop
  | .moral, s, a => MorallyOught s a
  | .prudential, s, a => PrudentiallyOught s a

/-- The situations in which moral and prudential reasons converge. -/
axiom Convergent : Sit → Prop

/-- Assumption 2.3 (convergence). In a convergent situation, what one
morally ought to do is what one prudentially ought to do. -/
axiom convergence : ∀ s a, Convergent s → MorallyOught s a → PrudentiallyOught s a

/-- Theorem 3.1 (two cases). In a convergent situation, the question why
one should do what one morally ought to do is answered on both readings. -/
theorem two_case (s : Sit) (a : Act) (hc : Convergent s) (hm : MorallyOught s a) :
    ∀ r, Answered r s a
  | .moral => hm
  | .prudential => convergence s a hc hm

/-- Corollary 3.3. In a convergent situation, every positive weighting of
moral and prudential reasons favors what one morally ought to do. -/
theorem all_things_considered (s : Sit) (a : Act) (k₁ k₂ : Nat) (hk : 0 < k₁)
    (hc : Convergent s) (hm : MorallyOught s a) :
    Best (fun x => k₁ * moral s x + k₂ * prudential s x) (opts s) a :=
  dominance _ _ k₁ k₂ hk _ a hm (convergence s a hc hm)

/-- Proposition 3.4 (divergence). If what one morally ought to do differs
from what one prudentially ought to do, the prudential reading receives a
negative answer, and the situation is not convergent. -/
theorem divergence (s : Sit) (a b : Act) (hm : MorallyOught s a)
    (hp : PrudentiallyOught s b) (hne : a ≠ b) :
    ¬ Answered .prudential s a ∧ ¬ Convergent s := by
  have h1 : ¬ PrudentiallyOught s a := fun ha => hne (best_unique _ _ a b ha hp)
  exact ⟨h1, fun hc => h1 (convergence s a hc hm)⟩

/-- Proposition 3.5. Over a life, the number of situations in which the
prudential reading receives no positive answer for the moral option is at
most the number of divergent situations. -/
theorem negative_answers_bounded (life : List Sit) (choice : Sit → Act)
    (hm : ∀ s, MorallyOught s (choice s)) :
    count (fun s => ¬ Answered .prudential s (choice s)) life ≤
      count (fun s => ¬ Convergent s) life :=
  count_mono _ _ (fun s h hc => h (convergence s (choice s) hc (hm s))) life

end Philosophy.MTE_04

#print axioms Philosophy.MTE_04.two_case
#print axioms Philosophy.MTE_04.all_things_considered
#print axioms Philosophy.MTE_04.negative_answers_bounded
