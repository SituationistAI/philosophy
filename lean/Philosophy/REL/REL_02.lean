/-
REL-02 · Evil, Omnipotence and the Structure of Logical Space
Formalization of Proposition 3.1, Lemma 3.2, Theorem 3.3, Corollary 3.4,
Proposition 3.5, Theorem 4.2, Proposition 4.3, Theorem 6.3 and
Corollary 6.4.

Framework. States of affairs are predicates on worlds. `Brings x p w` is
strong actualization (Definition 2.1). The x-independent version of p
(Definition 2.4) is the state in which p obtains and x does not bring it
about.

What this file establishes. (1) Mackie's argument is valid (Proposition
3.1). (2) No agent brings about, or can bring about, a state defined by its
own not bringing it about (Lemma 3.2, Theorem 3.3); hence an ideal state that
includes God-independent goodness is not available to God (Corollary 3.4),
and the states a stratified-omnipotent being cannot bring about are
impossible or self-referential (Proposition 3.5). (3) A concrete finite model
in which an omnipotent (stratified) and morally perfect God permits evil
while an evil-free ideal world is possible (Theorem 4.2, Proposition 4.3).
(4) The arithmetic of the noseeum inference: posterior odds of r to 1
against theism from even priors require detection probability at least
(r-1)/r (Theorem 6.3, Corollary 6.4).

What it does not establish. That the independent good is a good, or how
much it is worth (Assumption 4.1 enters only through the numbers of the
model); that God exists; that the detection probability is in fact low.
-/

namespace Philosophy.REL_02

/-! ## Framework (Section 2) -/

/-- Possible worlds. -/
axiom World : Type

/-- Agents. -/
axiom Agent : Type

/-- States of affairs, construed as sets of worlds. -/
abbrev State := World → Prop

/-- Definition 2.1. `Brings x p w`: at `w`, `x` strongly actualizes `p`. -/
axiom Brings : Agent → State → World → Prop

/-- Assumption 2.2 (factivity). What is brought about obtains. -/
axiom brings_factive : ∀ {x : Agent} {p : State} {w : World}, Brings x p w → p w

/-- Assumption 2.3 (conjunction). To bring about a conjunction is to bring
about its first conjunct. -/
axiom brings_left : ∀ {x : Agent} {p q : State} {w : World},
  Brings x (fun v => p v ∧ q v) w → Brings x p w

/-- Definition 2.4. The `x`-independent version of `p`. -/
def Indep (x : Agent) (p : State) : State := fun v => p v ∧ ¬ Brings x p v

/-- Definition 2.5. `CanBring x p w`: at `w`, `x` can bring about `p`. -/
axiom CanBring : Agent → State → World → Prop

/-- Definition 2.5. A state is possible if it obtains at some world. -/
def Possible (p : State) : Prop := ∃ w, p w

/-- Assumption 2.6 (realization). An ability is exercised at some world. -/
axiom can_realized : ∀ {x : Agent} {p : State} {w : World},
  CanBring x p w → ∃ v, Brings x p v

/-- Definition 2.7 (i). Unrestricted omnipotence. -/
def UnrestrictedlyOmnipotent (x : Agent) (w : World) : Prop :=
  ∀ p, Possible p → CanBring x p w

/-- Self-reference: the description of the state quantifies over the
exercise of the agent's own powers (Definition 2.7). -/
axiom SelfRef : Agent → State → Prop

/-- Definition 2.7 (ii). Omnipotence in the stratified sense of REL-04-a. -/
def Omnipotent (x : Agent) (w : World) : Prop :=
  ∀ p, Possible p → ¬ SelfRef x p → CanBring x p w

/-- Assumption 2.8 (classification). Independent states are
self-referential for the agent they are indexed to. -/
axiom independent_selfref : ∀ (x : Agent) (p : State), SelfRef x (Indep x p)

/-- Evil occurs at a world. -/
axiom Evil : State

/-! ## The logical problem (Section 3) -/

/-- Proposition 3.1 (validity of Mackie's argument). Principles P1-P3
entail that no evil exists. `ideal` is the ideal state. -/
theorem mackie_valid (g : Agent) (w : World) (ideal : State)
    (P1 : UnrestrictedlyOmnipotent g w)
    (P2 : CanBring g ideal w → ¬ Evil w)
    (P3 : Possible ideal) : ¬ Evil w :=
  P2 (P1 ideal P3)

/-- Lemma 3.2 (diagonal lemma). No agent brings about its own independent
version of a state. -/
theorem no_agent_brings_independent (x : Agent) (p : State) (w : World) :
    ¬ Brings x (Indep x p) w := by
  intro h
  have hp : Brings x p w := brings_left h
  exact (brings_factive h).2 hp

/-- Theorem 3.3 (the structure of logical space). -/
theorem structure_of_logical_space (x : Agent) (p : State) :
    (∀ w, ¬ CanBring x (Indep x p) w) ∧
    (Possible (Indep x p) → ∀ w, ¬ UnrestrictedlyOmnipotent x w) := by
  have h1 : ∀ w, ¬ CanBring x (Indep x p) w := fun w hc =>
    let ⟨v, hv⟩ := can_realized hc
    no_agent_brings_independent x p v hv
  exact ⟨h1, fun hpos w hu => h1 w (hu _ hpos)⟩

/-- The ideal state for God `g`: the `g`-independent goodness of creatures
`q`, the other goods `others`, and no evil. -/
def Ideal (g : Agent) (q others : State) : State :=
  fun v => (Indep g q v ∧ others v) ∧ ¬ Evil v

/-- Corollary 3.4. God cannot bring about an ideal state that includes
God-independent goodness; so P1 fails if it is possible, and the antecedent
of P2 is false at every world. -/
theorem ideal_unavailable (g : Agent) (q others : State) :
    (∀ w, ¬ CanBring g (Ideal g q others) w) ∧
    (Possible (Ideal g q others) → ∀ w, ¬ UnrestrictedlyOmnipotent g w) := by
  have h1 : ∀ w, ¬ CanBring g (Ideal g q others) w := fun w hc =>
    let ⟨v, hv⟩ := can_realized hc
    no_agent_brings_independent g q v (brings_left (brings_left hv))
  exact ⟨h1, fun hpos w hu => h1 w (hu _ hpos)⟩

/-- Proposition 3.5. What a stratified-omnipotent being cannot bring about
is impossible or self-referential; independent states are self-referential. -/
theorem stratified_limits (x : Agent) (w : World) (h : Omnipotent x w) :
    (∀ p, ¬ CanBring x p w → ¬ Possible p ∨ SelfRef x p) ∧
    (∀ p, SelfRef x (Indep x p)) := by
  refine ⟨fun p hn => ?_, fun p => independent_selfref x p⟩
  apply Classical.byContradiction
  intro hc
  apply hn
  apply h p
  · exact Classical.byContradiction fun hp => hc (Or.inl hp)
  · exact fun hs => hc (Or.inr hs)

/-! ## A consistency model (Section 4) -/

namespace Model

/-- God's options: determine the creatures' conduct, release them, or
release them and thwart every wrong act. -/
inductive Opt
  | determine | release | thwart
  deriving DecidableEq

/-- The possible states of the model: the outcomes of the three options and
the ideal world. -/
inductive St
  | outcome (o : Opt) | ideal
  deriving DecidableEq

/-- Every state of the model is possible. -/
def possible : St → Bool := fun _ => true

/-- Only the ideal world is self-referential for God (Assumption 2.8: it
includes God-independent goodness). -/
def selfRef : St → Bool
  | .ideal => true
  | .outcome _ => false

/-- God can bring about the outcome of each option, and not the ideal world. -/
def canBring : St → Bool
  | .ideal => false
  | .outcome _ => true

/-- Levels of good (Assumption 4.1: release realizes the independent good). -/
def good : St → Nat
  | .outcome .determine => 1
  | .outcome .release => 3
  | .outcome .thwart => 1
  | .ideal => 3

/-- Levels of evil. -/
def evil : St → Nat
  | .outcome .release => 1
  | _ => 0

/-- Definition 2.9. An option is wrong if another option has less evil and
no less good. -/
def Wrong (o : Opt) : Prop :=
  ∃ o', evil (.outcome o') < evil (.outcome o) ∧ good (.outcome o) ≤ good (.outcome o')

/-- Theorem 4.2 (consistency). In the model God is omnipotent in the
stratified sense, choosing release is not wrong, evil exists in the
resulting world, and the ideal world is possible and evil-free. -/
theorem consistency :
    (∀ s, possible s = true → selfRef s = false → canBring s = true) ∧
    ¬ Wrong .release ∧
    evil (.outcome .release) > 0 ∧
    (possible .ideal = true ∧ evil .ideal = 0 ∧
      good .ideal = good (.outcome .release)) := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · intro s _ hs
    cases s with
    | ideal => simp [selfRef] at hs
    | outcome o => rfl
  · intro ⟨o', h1, h2⟩
    cases o' <;> simp [good, evil] at h1 h2

/-- Proposition 4.3. Release also maximizes the balance of good over evil. -/
theorem release_best (o : Opt) :
    good (.outcome o) - evil (.outcome o) ≤
      good (.outcome .release) - evil (.outcome .release) := by
  cases o <;> decide

end Model

/-! ## The evidential problem (Section 6) -/

/-- Theorem 6.3 (detection threshold). Probabilities are multiples of
`1/N`: `P(¬D | G) = (N - k)/N` with detection `δ = k/N` (Definition 6.1,
Assumption 6.2), and `P(¬D | ¬G) = m/N` with `m ≤ N`. From even priors,
posterior odds of at least `r` to 1 against theism (`r * (N - k) ≤ m`)
require `r * N ≤ N + r * k`, that is, `δ ≥ (r - 1)/r`. -/
theorem detection_threshold (N k m r : Nat) (hk : k ≤ N) (hm : m ≤ N)
    (h : r * (N - k) ≤ m) : r * N ≤ N + r * k := by
  have e : r * (N - k) + r * k = r * N := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hk]
  omega

/-- Corollary 6.4. With zero detection, posterior odds against theism of
`r` to 1 from even priors require `r ≤ 1`. -/
theorem no_detection_no_confirmation (N m r : Nat) (hN : 0 < N) (hm : m ≤ N)
    (h : r * (N - 0) ≤ m) : r ≤ 1 := by
  have h2 := detection_threshold N 0 m r (Nat.zero_le N) hm h
  rw [Nat.mul_zero, Nat.add_zero] at h2
  rcases Nat.lt_or_ge 1 r with hr | hr
  · have h3 : 2 * N ≤ r * N := Nat.mul_le_mul_right N hr
    omega
  · exact hr

/-- Example: odds of 9 to 1 against theism from parity require detection of
at least 8/9. -/
theorem nine_to_one (N k m : Nat) (hk : k ≤ N) (hm : m ≤ N)
    (h : 9 * (N - k) ≤ m) : 8 * N ≤ 9 * k := by
  have := detection_threshold N k m 9 hk hm h
  omega

end Philosophy.REL_02

#print axioms Philosophy.REL_02.mackie_valid
#print axioms Philosophy.REL_02.structure_of_logical_space
#print axioms Philosophy.REL_02.ideal_unavailable
#print axioms Philosophy.REL_02.stratified_limits
#print axioms Philosophy.REL_02.Model.consistency
#print axioms Philosophy.REL_02.Model.release_best
#print axioms Philosophy.REL_02.detection_threshold
#print axioms Philosophy.REL_02.no_detection_no_confirmation
