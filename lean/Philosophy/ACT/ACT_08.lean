/-
ACT-08 · The Basic Argument Fails
Formalization of Lemma 3.1, Theorem 3.2 and Proposition 3.3.

What this file establishes. Agency is divided into stages indexed by the
natural numbers; stage 0 is the agent's initial, unchosen nature. Strawson's
regress premise (Principle P3: ultimate responsibility for one's nature at a
stage requires a previous stage at which one was already ultimately
responsible for one's nature) entails that no one is ultimately responsible
for her nature at any stage (Lemma 3.1); together with the ultimacy premise
(P2) it entails that no one is responsible for any action. Given the
sufficiency of owned reasons-responsiveness for responsibility
(Assumption 2.4) and the existence of a stage from which the agent's mechanism
is reasons-responsive (Assumption 2.5), P2 is false (Theorem 3.2), and every
later nature is partly formed by actions for which the agent is responsible
(Proposition 3.3).

What it does not establish. It does not establish Assumptions 2.4-2.6,
which the manuscript defends (with ACT-01), nor that anyone is ultimately
responsible for anything: P3 is granted throughout as an analysis of
ultimacy, and it is P2 that is rejected.
-/

namespace Philosophy.ACT_08

/-- Primitive: the agent is responsible for what she does at stage `n`. -/
axiom RespAct : Nat → Prop

/-- Primitive: the agent is ultimately responsible for her nature at stage
`n` (Definition 2.2). -/
axiom UltNature : Nat → Prop

/-- Primitive: at stage `n` the agent acts from an owned, reasons-responsive
mechanism (Definition 2.3). -/
axiom OwnedRR : Nat → Prop

/-- Primitive: what the agent does at stage `m` contributes to her nature at
stage `n`. -/
axiom Shapes : Nat → Nat → Prop

/-- Assumption 2.4 (sufficiency, ACT-01). Action from an owned,
reasons-responsive mechanism is action for which the agent is responsible. -/
axiom assumption_2_4 : ∀ n, OwnedRR n → RespAct n

/-- The stage from which the agent's mechanism is reasons-responsive. -/
axiom k : Nat

/-- Assumption 2.5 (maturation). From stage `k` on, the agent acts from an
owned, reasons-responsive mechanism. -/
axiom assumption_2_5 : ∀ n, k ≤ n → OwnedRR n

/-- Assumption 2.6 (sedimentation). What the agent does at a stage
contributes to her nature at the next stage. -/
axiom assumption_2_6 : ∀ n, Shapes n (n + 1)

/-- Principle P2 (ultimacy): responsibility for action requires ultimate
responsibility for one's nature at that stage. Stated as a hypothesis. -/
def P2 : Prop := ∀ n, RespAct n → UltNature n

/-- Principle P3 (regress): ultimate responsibility for one's nature at a
stage requires an earlier stage at which one was already ultimately
responsible for one's nature. Stated as a hypothesis. -/
def P3 : Prop := ∀ n, UltNature n → ∃ m, n = m + 1 ∧ UltNature m

/-- Lemma 3.1 (the regress). Under P3 no one is ultimately responsible for
her nature at any stage; with P2, no one is responsible for any action. -/
theorem lemma_3_1 (h3 : P3) : ∀ n, ¬ UltNature n := by
  intro n
  induction n with
  | zero =>
    intro hu
    obtain ⟨m, hm, _⟩ := h3 0 hu
    omega
  | succ n ih =>
    intro hu
    obtain ⟨m, hm, hum⟩ := h3 (n + 1) hu
    have : m = n := by omega
    subst this
    exact ih hum

/-- Lemma 3.1, second part: P2 and P3 together entail that the agent is
responsible for nothing she does (the Basic Argument is valid). -/
theorem basic_argument_valid (h2 : P2) (h3 : P3) : ∀ n, ¬ RespAct n :=
  fun n hr => lemma_3_1 h3 n (h2 n hr)

/-- Theorem 3.2 (main result). Granting P3, P2 is false: there is a stage at
which the agent is responsible for what she does without being ultimately
responsible for her nature. -/
theorem basic_argument_fails (h3 : P3) :
    ∃ n, RespAct n ∧ ¬ UltNature n :=
  ⟨k, assumption_2_4 k (assumption_2_5 k (Nat.le_refl k)), lemma_3_1 h3 k⟩

/-- Remark after Theorem 3.2: P2 and P3 are not both true. -/
theorem not_both : ¬ (P2 ∧ P3) := fun ⟨h2, h3⟩ =>
  basic_argument_valid h2 h3 k (assumption_2_4 k (assumption_2_5 k (Nat.le_refl k)))

/-- Proposition 3.3 (self-formation without regress). Every nature after
stage `k` is shaped by an earlier action for which the agent is
responsible. -/
theorem self_formation (n : Nat) (h : k < n) :
    ∃ m, m < n ∧ RespAct m ∧ Shapes m n := by
  refine ⟨n - 1, by omega, assumption_2_4 _ (assumption_2_5 _ (by omega)), ?_⟩
  have e : n = (n - 1) + 1 := by omega
  have hs := assumption_2_6 (n - 1)
  rw [← e] at hs
  exact hs

end Philosophy.ACT_08

#print axioms Philosophy.ACT_08.basic_argument_fails
#print axioms Philosophy.ACT_08.self_formation
