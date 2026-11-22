/-
MET-04 · Causation as Counterfactual Dependence Plus Normality
Formalization of Definitions 2.1–2.7, Principles P1 and P2, Lemmas 3.1
and 3.2, Theorems 3.3–3.6 and Propositions 3.7, 3.8 and 6.1.

A causal model has finitely many Boolean variables, numbered in a causal
order; each variable has a structural equation that reads only earlier
variables (exogenous variables have constant equations). Some variables
carry a default value fixed by a norm (statistical, prescriptive or
functional). Sets of variables are coded as bit masks.

A set C of variables is a de facto difference-maker for the actual value
of Y if setting the variables in C to non-actual values, while holding
some set of other variables fixed at their actual values, changes the
value of Y. It is a normal difference-maker if this can be done in a
witness world that is at least as normal as the actual world, and no
proper subset of C will do (Definition 2.7). The analysis of causation is
stated as two axioms (Principles P1 and P2) about a primitive relation
`Causes`, so that the philosophical thesis is visible as a premise.

What this file establishes. Every cause is a de facto difference-maker;
no variable at its default value is a cause or part of a cause; and, in
six small models, the analysis delivers the standard verdicts: late
preemption, symmetric overdetermination, omission (the gardener and the
Queen), norm violation (the pen case), bogus prevention and the switch.
In the petition model (REL-12-a) the request is neither a cause nor part
of a cause of the outcome, while the dependence clause alone would count
it as part of a cause. It also shows that neither clause can be dropped.

What it does not establish. It does not establish Principles P1 and P2,
that the models are apt, or that the norms assigned are the correct ones.
-/

namespace Philosophy.MET_04

/-- Worlds: assignments of truth values to variables. -/
abbrev World := Nat → Bool

/-- Interventions: some variables are set to a value, others left free. -/
abbrev Intervention := Nat → Option Bool

/-- Definition 2.1 (causal model). `n` variables numbered in causal order;
`eqn i w` is the value of variable `i` given the values `w` of earlier
variables; `norm i` is the default value of `i`, if any (Definition 2.4). -/
structure Model where
  n : Nat
  eqn : Nat → World → Bool
  norm : Nat → Option Bool

/-- Definition 2.2 (solution under an intervention), computed stage by
stage in the causal order. -/
def stage (M : Model) (iv : Intervention) : Nat → World
  | 0 => fun _ => false
  | k + 1 =>
    let w := stage M iv k
    let v := match iv k with
      | some b => b
      | none => M.eqn k w
    fun j => if j = k then v else w j

def solve (M : Model) (iv : Intervention) : World := stage M iv M.n

/-- The actual world: the solution under the null intervention. -/
def actual (M : Model) : World := solve M (fun _ => none)

/-- Membership of variable `j` in the set coded by the mask `s`. -/
def mem (s j : Nat) : Bool := Nat.testBit s j

/-- Definition 2.3 (witness world). The variables in `c` are set to their
non-actual values and those in `h` are held at their actual values. -/
def witnessIv (M : Model) (c h : Nat) : Intervention := fun j =>
  if mem c j then some (!(actual M j))
  else if mem h j then some (actual M j) else none

def witness (M : Model) (c h : Nat) : World := solve M (witnessIv M c h)

/-- Definition 2.5 (at least as normal). `w` is at least as normal as `v`
if `w` agrees with the default wherever `v` does. -/
def atLeastAsNormal (M : Model) (w v : World) : Bool :=
  (List.range M.n).all fun i =>
    match M.norm i with
    | none => true
    | some d => !(v i == d) || (w i == d)

/-- Definition 2.6 (de facto dependence). The value of `y` depends on the
set `c` holding fixed some set of variables at their actual values. -/
def dependsB (M : Model) (c y : Nat) : Bool :=
  (List.range (2 ^ M.n)).any fun h => witness M c h y != actual M y

/-- Dependence in a witness world at least as normal as the actual one. -/
def normalDependsB (M : Model) (c y : Nat) : Bool :=
  (List.range (2 ^ M.n)).any fun h =>
    (witness M c h y != actual M y) &&
      atLeastAsNormal M (witness M c h) (actual M)

/-- `c'` is a non-empty proper subset of `c` (proper subsets are smaller). -/
def properSub (c' c : Nat) : Bool := c' != 0 && (c' &&& c) == c'

/-- Definition 2.6 (de facto difference-maker): non-empty, dependent, and
minimal. -/
def dfMakerB (M : Model) (c y : Nat) : Bool :=
  c != 0 && decide (c < 2 ^ M.n) && dependsB M c y &&
    (List.range c).all fun c' => !(properSub c' c) || !(dependsB M c' y)

/-- Definition 2.7 (normal difference-maker): non-empty, dependent in a
witness world at least as normal as the actual world, and minimal. -/
def normalMakerB (M : Model) (c y : Nat) : Bool :=
  c != 0 && decide (c < 2 ^ M.n) && normalDependsB M c y &&
    (List.range c).all fun c' => !(properSub c' c) || !(normalDependsB M c' y)

/-- Part of a normal difference-maker. -/
def partB (M : Model) (x y : Nat) : Bool :=
  (List.range (2 ^ M.n)).any fun c => mem c x && normalMakerB M c y

/-- Part of a de facto difference-maker. -/
def dfPartB (M : Model) (x y : Nat) : Bool :=
  (List.range (2 ^ M.n)).any fun c => mem c x && dfMakerB M c y

/-- Primitive: in the (apt) model `M`, the actual values of the variables
in `c` are jointly a cause of the actual value of `y`. -/
axiom Causes : Model → Nat → Nat → Prop

/-- Principle P1 (dependence plus default, necessity). Every cause is a
normal difference-maker. -/
axiom principle_P1 : ∀ M c y, Causes M c y → normalMakerB M c y = true

/-- Principle P2 (dependence plus default, sufficiency). In an apt model
(Assumption 2.8, not formalized: the models below are taken as apt), every
normal difference-maker is a cause. -/
axiom principle_P2 : ∀ M c y, normalMakerB M c y = true → Causes M c y

/-- Being part of a cause. -/
def PartOfCause (M : Model) (x y : Nat) : Prop := ∃ c, mem c x = true ∧ Causes M c y

/-- The singleton set `{x}`. -/
def single (x : Nat) : Nat := 2 ^ x

/-! ### General results -/

/-- A variable set by an intervention takes the value set. -/
theorem stage_set (M : Model) (iv : Intervention) (x : Nat) (b : Bool)
    (hb : iv x = some b) : ∀ k, x < k → stage M iv k x = b := by
  intro k
  induction k with
  | zero => intro h; exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    intro hk
    by_cases hx : x = k
    · subst hx; simp [stage, hb]
    · have : x < k := by omega
      simp [stage, hx, ih this]

/-- Lemma 3.1. Every cause is a de facto difference-maker: dependence is
necessary for causation. -/
theorem lemma_3_1 (M : Model) (c y : Nat) (h : Causes M c y) :
    dependsB M c y = true := by
  have hn := principle_P1 M c y h
  simp only [normalMakerB, Bool.and_eq_true] at hn
  obtain ⟨⟨⟨_, _⟩, hd⟩, _⟩ := hn
  simp only [normalDependsB, List.any_eq_true, Bool.and_eq_true] at hd
  obtain ⟨h', hm, hw, _⟩ := hd
  simp only [dependsB, List.any_eq_true]
  exact ⟨h', hm, hw⟩

/-- A set containing a variable at its default value has no normal witness. -/
theorem default_blocks (M : Model) (c y x : Nat) (hx : x < M.n)
    (hc : mem c x = true) (hd : M.norm x = some (actual M x)) :
    normalDependsB M c y = false := by
  unfold normalDependsB
  rw [List.any_eq_false]
  intro h _ hcon
  simp only [Bool.and_eq_true] at hcon
  obtain ⟨_, hnorm⟩ := hcon
  rw [atLeastAsNormal, List.all_eq_true] at hnorm
  have hi := hnorm x (List.mem_range.2 hx)
  have hw : witness M c h x = !(actual M x) :=
    stage_set M _ x _ (by simp [witnessIv, hc]) M.n hx
  rw [hd, hw] at hi
  cases actual M x <;> simp at hi

/-- Lemma 3.2 (defaults are conditions). No variable at its default value
is a cause or part of a cause. -/
theorem lemma_3_2 (M : Model) (x y : Nat) (hx : x < M.n)
    (hd : M.norm x = some (actual M x)) : ¬ PartOfCause M x y := by
  intro ⟨c, hc, hcause⟩
  have hn := principle_P1 M c y hcause
  simp [normalMakerB, default_blocks M c y x hx hc hd] at hn

/-- Bridge: what the enumeration `partB` rules out is not part of a cause. -/
theorem not_part (M : Model) (x y : Nat) (h : partB M x y = false) :
    ¬ PartOfCause M x y := by
  intro ⟨c, hc, hcause⟩
  have hn := principle_P1 M c y hcause
  have hlt : c < 2 ^ M.n := by
    simp only [normalMakerB, Bool.and_eq_true, decide_eq_true_eq] at hn
    exact hn.1.1.2
  rw [partB, List.any_eq_false] at h
  exact h c (List.mem_range.2 hlt) (by simp [hc, hn])

/-! ### Models -/

/-- Late preemption: 0 Suzy throws, 1 Billy throws, 2 Suzy's rock hits,
3 Billy's rock hits, 4 the bottle shatters. Throwing is a deviation. -/
def preemption : Model where
  n := 5
  eqn := fun i w => match i with
    | 0 => true
    | 1 => true
    | 2 => w 0
    | 3 => w 1 && !(w 2)
    | _ => w 2 || w 3
  norm := fun i => match i with
    | 0 => some false
    | 1 => some false
    | _ => none

/-- Symmetric overdetermination: 0 Suzy throws, 1 Billy throws, 2 the
bottle shatters; both rocks arrive together. -/
def overdetermination : Model where
  n := 3
  eqn := fun i w => match i with
    | 0 => true
    | 1 => true
    | _ => w 0 || w 1
  norm := fun i => match i with
    | 2 => none
    | _ => some false

/-- The gardener: 0 the gardener waters, 1 the Queen waters, 2 the plant
dies. The gardener is supposed to water; the Queen is not. -/
def gardener : Model where
  n := 3
  eqn := fun i w => match i with
    | 0 => false
    | 1 => false
    | _ => !(w 0) && !(w 1)
  norm := fun i => match i with
    | 0 => some true
    | 1 => some false
    | _ => none

/-- The pen case: 0 the professor takes a pen (forbidden), 1 the assistant
takes a pen (permitted), 2 the receptionist is left without pens. -/
def pens : Model where
  n := 3
  eqn := fun i w => match i with
    | 0 => true
    | 1 => true
    | _ => w 0 && w 1
  norm := fun i => match i with
    | 0 => some false
    | 1 => some true
    | _ => none

/-- Bogus prevention: 0 the assassin poisons (he does not), 1 the bodyguard
gives the antidote, 2 the victim survives. -/
def bogus : Model where
  n := 3
  eqn := fun i w => match i with
    | 0 => false
    | 1 => true
    | _ => !(w 0) || w 1
  norm := fun i => match i with
    | 0 => some false
    | _ => none

/-- The switch: 0 the switch is flipped, 1 the train takes the left-hand
track (rather than the right-hand one), 2 the train arrives; both tracks
lead to the station. -/
def switch : Model where
  n := 3
  eqn := fun i w => match i with
    | 0 => true
    | 1 => w 0
    | _ => w 1 || !(w 1)
  norm := fun _ => none

/-- Petition (REL-12-a): 0 the request is made, 1 God has the good-making
reason for the outcome (the default, since God is perfectly good), 2 God
wills the outcome, 3 the outcome occurs. Either reason suffices. -/
def petition : Model where
  n := 4
  eqn := fun i w => match i with
    | 0 => true
    | 1 => true
    | 2 => w 0 || w 1
    | _ => w 2
  norm := fun i => match i with
    | 1 => some true
    | _ => none

/-- Theorem 3.3 (preemption). Suzy's throw is a cause of the shattering;
Billy's throw is neither a cause nor part of a cause. -/
theorem theorem_3_3 :
    Causes preemption (single 0) 4 ∧ ¬ PartOfCause preemption 1 4 :=
  ⟨principle_P2 _ _ _ (by decide), not_part _ _ _ (by decide)⟩

/-- Theorem 3.4 (symmetric overdetermination). Neither throw alone is a
cause; the two throws together are a cause, so each is part of a cause. -/
theorem theorem_3_4 :
    ¬ Causes overdetermination (single 0) 2 ∧
    ¬ Causes overdetermination (single 1) 2 ∧
    Causes overdetermination 3 2 ∧
    PartOfCause overdetermination 0 2 ∧ PartOfCause overdetermination 1 2 := by
  have hj : Causes overdetermination 3 2 := principle_P2 _ _ _ (by decide)
  refine ⟨fun h => ?_, fun h => ?_, hj, ⟨3, by decide, hj⟩, ⟨3, by decide, hj⟩⟩
  · have := principle_P1 _ _ _ h; revert this; decide
  · have := principle_P1 _ _ _ h; revert this; decide

/-- Theorem 3.5 (omission). The gardener's failure to water is a cause of
the death; the Queen's failure to water is not part of a cause. -/
theorem theorem_3_5 :
    Causes gardener (single 0) 2 ∧ ¬ PartOfCause gardener 1 2 :=
  ⟨principle_P2 _ _ _ (by decide), not_part _ _ _ (by decide)⟩

/-- Theorem 3.6 (norm violation, bogus prevention, switching). The
professor's taking a pen is a cause and the assistant's is not part of a
cause; the antidote is not part of a cause of survival; flipping the
switch is not part of a cause of the arrival. -/
theorem theorem_3_6 :
    (Causes pens (single 0) 2 ∧ ¬ PartOfCause pens 1 2) ∧
    ¬ PartOfCause bogus 1 2 ∧ ¬ PartOfCause switch 0 2 :=
  ⟨⟨principle_P2 _ _ _ (by decide), not_part _ _ _ (by decide)⟩,
   not_part _ _ _ (by decide), not_part _ _ _ (by decide)⟩

/-- Proposition 3.7 (dependence alone does not select). On the
dependence clause alone, the gardener's and the Queen's omissions are
both difference-makers, so are the professor's and the assistant's taking
of pens, and the antidote in bogus prevention and the request in the
petition model are each part of a difference-maker. -/
theorem proposition_3_7 :
    (dfMakerB gardener (single 0) 2 = true ∧ dfMakerB gardener (single 1) 2 = true) ∧
    (dfMakerB pens (single 0) 2 = true ∧ dfMakerB pens (single 1) 2 = true) ∧
    dfPartB bogus 1 2 = true ∧ dfPartB petition 0 3 = true := by decide

/-- Proposition 3.8 (default alone does not select). Billy's throw deviates
from its default, as Suzy's does, yet it is not part of a cause. -/
theorem proposition_3_8 :
    preemption.norm 1 = some false ∧ actual preemption 1 = true ∧
    ¬ PartOfCause preemption 1 4 :=
  ⟨rfl, by decide, theorem_3_3.2⟩

/-- Proposition 6.1 (petition). The request is neither a cause nor part
of a cause of the outcome; God's willing is a cause. -/
theorem proposition_6_1 :
    ¬ PartOfCause petition 0 3 ∧ Causes petition (single 2) 3 :=
  ⟨not_part _ _ _ (by decide), principle_P2 _ _ _ (by decide)⟩

end Philosophy.MET_04

#print axioms Philosophy.MET_04.lemma_3_2
#print axioms Philosophy.MET_04.theorem_3_3
#print axioms Philosophy.MET_04.theorem_3_5
#print axioms Philosophy.MET_04.proposition_6_1
