/-
LNG-01 · On Meaning
Formalization of Definition 3.1, Propositions 3.2, 3.4 and 3.5,
Theorem 3.3, Theorem 3.6 and Corollary 3.7.

The logical constants are the test case of the manuscript. The use of a
binary connective is represented by the soundness condition its
introduction and elimination rules impose on a bivalent truth function
(Definition 3.1, local reading). A truth function is admissible for a rule
set if the rules are truth-preserving for it.

What this file establishes. No truth function is admissible for Prior's
tonk; the standard rules for conjunction, disjunction, the conditional and
negation each admit exactly one truth function, the classical one; the
introduction rule or the elimination rule for conjunction alone admits more
than one; and a sentence-level valuation that makes every sentence true
respects every rule whose conclusion is a sentence, yet is induced by no
admissible truth function for negation (Carnap's problem). Given Principles
P2 and P3, stated as axioms about an arbitrary connective, a connective
whose rules admit exactly one truth function means that function, and a
connective whose rules admit none means nothing.

What it does not establish. It does not formalize Principle P1 (that
meaning is fixed by use) beyond the fact that the axioms make a
connective's meaning depend on nothing but its rules; it does not treat
non-logical vocabulary (Section 4), and it assumes bivalence.
-/

namespace Philosophy.LNG_01

/-- Bivalent truth functions for binary connectives (Definition 2.2). -/
abbrev TF := Bool → Bool → Bool

/-- A rule set, represented by the condition it imposes on an assignment:
`R f` says that the rules are truth-preserving when the connective is
assigned `f` (Definitions 2.3 and 3.1). -/
abbrev RuleSet := TF → Prop

/-- Definition 3.1. Soundness conditions, local reading. -/
def AndI : RuleSet := fun f => ∀ a b, a = true → b = true → f a b = true
def AndE : RuleSet := fun f =>
  (∀ a b, f a b = true → a = true) ∧ (∀ a b, f a b = true → b = true)
def AndRules : RuleSet := fun f => AndI f ∧ AndE f
def OrRules : RuleSet := fun f =>
  (∀ a b, a = true → f a b = true) ∧ (∀ a b, b = true → f a b = true) ∧
  (∀ a b c, f a b = true → (a = true → c = true) → (b = true → c = true) → c = true)
def ImpRules : RuleSet := fun f =>
  (∀ a b, (a = true → b = true) → f a b = true) ∧
  (∀ a b, f a b = true → a = true → b = true)
def TonkRules : RuleSet := fun f =>
  (∀ a b, a = true → f a b = true) ∧ (∀ a b, f a b = true → b = true)
def NegRules (g : Bool → Bool) : Prop :=
  (∀ a, (a = true → False) → g a = true) ∧ (∀ a, g a = true → a = true → False)

/-- Proposition 3.2 (Prior's tonk). No truth function is admissible for tonk. -/
theorem tonk_inadmissible (f : TF) : ¬ TonkRules f := fun ⟨i, e⟩ =>
  Bool.noConfusion (e true false (i true false rfl))

theorem and_admissible : AndRules (fun a b => a && b) := by
  unfold AndRules AndI AndE; decide

theorem and_unique (f : TF) (h : AndRules f) : f = fun a b => a && b := by
  obtain ⟨i, e1, e2⟩ := h
  funext a b
  cases a <;> cases b
  · cases hf : f false false
    · rfl
    · exact absurd (e1 _ _ hf) (by decide)
  · cases hf : f false true
    · rfl
    · exact absurd (e1 _ _ hf) (by decide)
  · cases hf : f true false
    · rfl
    · exact absurd (e2 _ _ hf) (by decide)
  · exact i _ _ rfl rfl

theorem or_admissible : OrRules (fun a b => a || b) := by
  refine ⟨by decide, by decide, fun a b c h ha hb => ?_⟩
  cases a
  · cases b
    · exact absurd h (by decide)
    · exact hb rfl
  · exact ha rfl

theorem or_unique (f : TF) (h : OrRules f) : f = fun a b => a || b := by
  obtain ⟨i1, i2, e⟩ := h
  funext a b
  cases a <;> cases b
  · cases hf : f false false
    · rfl
    · exact (Bool.noConfusion (e false false false hf (fun h => h) (fun h => h)) : False).elim
  · exact i2 _ _ rfl
  · exact i1 _ _ rfl
  · exact i1 _ _ rfl

theorem imp_admissible : ImpRules (fun a b => !a || b) := by
  unfold ImpRules; decide

theorem imp_unique (f : TF) (h : ImpRules f) : f = fun a b => !a || b := by
  obtain ⟨i, e⟩ := h
  funext a b
  cases a <;> cases b
  · exact i _ _ (fun h => h)
  · exact i _ _ (fun _ => rfl)
  · cases hf : f true false
    · rfl
    · exact (Bool.noConfusion (e _ _ hf rfl) : False).elim
  · exact i _ _ (fun _ => rfl)

theorem neg_admissible : NegRules (fun a => !a) := by
  refine ⟨fun a h => ?_, fun a h ha => ?_⟩
  · cases a
    · rfl
    · exact absurd rfl h
  · cases a
    · exact Bool.noConfusion ha
    · exact Bool.noConfusion h

theorem neg_unique (g : Bool → Bool) (h : NegRules g) : g = fun a => !a := by
  obtain ⟨i, e⟩ := h
  funext a
  cases a
  · exact i _ (fun h => Bool.noConfusion h)
  · cases hg : g true
    · rfl
    · exact (e _ hg rfl).elim

/-- Theorem 3.3 (determination). The standard rules for conjunction,
disjunction, the conditional and negation each admit exactly one truth
function, the classical one. -/
theorem determination :
    (∀ f, AndRules f ↔ f = fun a b => a && b) ∧
    (∀ f, OrRules f ↔ f = fun a b => a || b) ∧
    (∀ f, ImpRules f ↔ f = fun a b => !a || b) ∧
    (∀ g, NegRules g ↔ g = fun a => !a) :=
  ⟨fun f => ⟨and_unique f, fun h => h ▸ and_admissible⟩,
   fun f => ⟨or_unique f, fun h => h ▸ or_admissible⟩,
   fun f => ⟨imp_unique f, fun h => h ▸ imp_admissible⟩,
   fun g => ⟨neg_unique g, fun h => h ▸ neg_admissible⟩⟩

/-- Proposition 3.4 (harmony). The introduction rule for conjunction alone
admits conjunction, disjunction and the constantly true function; the
elimination rules alone admit conjunction and the constantly false
function. -/
theorem harmony :
    AndI (fun a b => a && b) ∧ AndI (fun a b => a || b) ∧ AndI (fun _ _ => true) ∧
    AndE (fun a b => a && b) ∧ AndE (fun _ _ => false) ∧
    (fun a b => a && b) ≠ (fun a b => a || b) ∧
    (fun a b => a && b) ≠ (fun _ _ : Bool => false) := by
  refine ⟨by unfold AndI; decide, by unfold AndI; decide, by unfold AndI; decide,
    by unfold AndE; decide, by unfold AndE; decide, fun h => ?_, fun h => ?_⟩
  · have := congrFun (congrFun h true) false
    exact Bool.noConfusion this
  · have := congrFun (congrFun h true) true
    exact Bool.noConfusion this

/-- Sentences of a propositional language with negation and conjunction. -/
inductive Fml where
  | atom : Nat → Fml
  | neg : Fml → Fml
  | conj : Fml → Fml → Fml

/-- The trivial valuation of Carnap's problem: every sentence is true. -/
def trivialVal : Fml → Bool := fun _ => true

/-- Proposition 3.5 (Carnap's problem). The trivial valuation preserves
truth across every rule whatever (since every conclusion is true), yet it
makes a sentence and its negation both true, so it is induced by no truth
function admissible for the negation rules. -/
theorem carnap :
    (∀ (premises : List Fml) (concl : Fml),
      (∀ p ∈ premises, trivialVal p = true) → trivialVal concl = true) ∧
    trivialVal (Fml.atom 0) = true ∧ trivialVal (Fml.neg (Fml.atom 0)) = true ∧
    ¬ ∃ g : Bool → Bool, NegRules g ∧
      ∀ φ, trivialVal (Fml.neg φ) = g (trivialVal φ) := by
  refine ⟨fun _ _ _ => rfl, rfl, rfl, fun ⟨g, hg, hv⟩ => ?_⟩
  have h1 := hv (Fml.atom 0)
  rw [neg_unique g hg] at h1
  exact Bool.noConfusion h1

/-! The axiomatic layer: Principles P2 and P3 about an arbitrary connective. -/

/-- Connectives of a language. -/
axiom Conn : Type

/-- The rule set governing a connective in use (Definition 2.1). -/
axiom rules : Conn → RuleSet

/-- `Means c f`: the connective `c` contributes the truth function `f` to
the truth-conditions of sentences containing it. -/
axiom Means : Conn → TF → Prop

/-- Principle P2 (truth-conditional constraint). A connective contributes a
truth function only if its rules are truth-preserving for it. -/
axiom principle_P2 : ∀ c f, Means c f → rules c f

/-- Principle P3 (determination). If exactly one truth function is
admissible for a connective's rules, the connective contributes it. -/
axiom principle_P3 : ∀ c f, rules c f → (∀ g, rules c g → g = f) → Means c f

/-- Theorem 3.6 (reconciliation). If the rules of a connective admit
exactly one truth function, the connective means that function and no
other; if they admit none, it means nothing. -/
theorem reconciliation (c : Conn) :
    (∀ f, rules c f → (∀ g, rules c g → g = f) → ∀ g, Means c g ↔ g = f) ∧
    ((∀ f, ¬ rules c f) → ∀ f, ¬ Means c f) := by
  refine ⟨fun f hf hu g => ⟨fun hm => hu g (principle_P2 c g hm), fun h => ?_⟩,
    fun hn f hm => hn f (principle_P2 c f hm)⟩
  subst h
  exact principle_P3 c g hf hu

/-- Corollary 3.7. A connective used with the conjunction rules means
classical conjunction; a connective used with the tonk rules means
nothing. -/
theorem conjunction_and_tonk (c d : Conn)
    (hc : rules c = AndRules) (hd : rules d = TonkRules) :
    (∀ f, Means c f ↔ f = fun a b => a && b) ∧ (∀ f, ¬ Means d f) := by
  refine ⟨fun f => ?_, (reconciliation d).2 (fun f h => tonk_inadmissible f (hd ▸ h))⟩
  have hadm : rules c (fun a b => a && b) := hc ▸ and_admissible
  exact (reconciliation c).1 _ hadm (fun g hg => and_unique g (hc ▸ hg)) f

end Philosophy.LNG_01

#print axioms Philosophy.LNG_01.determination
#print axioms Philosophy.LNG_01.carnap
#print axioms Philosophy.LNG_01.reconciliation
#print axioms Philosophy.LNG_01.conjunction_and_tonk
