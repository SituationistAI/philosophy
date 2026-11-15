/-
LOG-02 · Logical Monism
Formalization of Lemma 4.1, Theorem 4.2, Theorem 4.4, Corollaries 4.5 and
4.6, Theorem 5.2, Corollary 5.3 and Proposition 5.4.

The language is propositional: atoms indexed by natural numbers, falsum,
negation, conjunction, disjunction and the (material) conditional
(Definition 3.1). Classical valuations assign Booleans to atoms
(Definition 3.2). Interpretations are a primitive type; truth in an
interpretation is a primitive predicate constrained by the classical
truth clauses (Assumption 3.4) and by the freedom of atoms
(Assumption 3.5). Consequence is truth-preservation in every
interpretation (Definition 3.6).

What this file establishes. Given the classical clauses and the freedom of
atoms, truth-preservation coincides with classical consequence; classical
propositional logic has no consistent proper extension closed under
substitution and modus ponens (Post); hence any correct, non-trivial logic
of the language containing the tautologies is classical logic, and two
relations that both coincide with truth-preservation coincide with each
other. Separately, every many-valued semantics whose connectives agree
with the classical ones on the classical values (Łukasiewicz, strong
Kleene) is conservative over classical logic on classically valued atoms,
and the Łukasiewicz conditional contracts on classical values.

What it does not establish. It does not establish the classical clauses,
which are the substantive premise of the manuscript (Section 3), nor the
identification of consequence with truth-preservation, which is the thesis
of LOG-06. It treats only the propositional fragment; the extension to
quantifiers is discussed in Section 8 of the manuscript. It says nothing
formal about intuitionistic or relevant logics (Sections 5.1 and 5.2).
-/

namespace Philosophy.LOG_02

/-- Definition 3.1. Sentences of the propositional language. -/
inductive Formula where
  | atom : Nat → Formula
  | bot : Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | imp : Formula → Formula → Formula

open Formula

/-- Definition 3.2. Classical evaluation under a Boolean valuation. -/
def eval (v : Nat → Bool) : Formula → Bool
  | atom n => v n
  | bot => false
  | neg A => !(eval v A)
  | conj A B => eval v A && eval v B
  | disj A B => eval v A || eval v B
  | imp A B => !(eval v A) || eval v B

/-- Definition 3.2. Tautologies. -/
def Taut (A : Formula) : Prop := ∀ v, eval v A = true

/-- Definition 3.2. Classical consequence from a set of premises. -/
def ClassCons (G : Formula → Prop) (A : Formula) : Prop :=
  ∀ v, (∀ B, G B → eval v B = true) → eval v A = true

/-- Definition 3.3. Interpretations (primitive). -/
axiom Interp : Type

/-- Definition 3.3. Truth of a sentence in an interpretation (primitive). -/
axiom TrueIn : Interp → Formula → Prop

/-- Assumption 3.4 (classical clauses), falsum. -/
axiom clause_bot : ∀ I, ¬ TrueIn I bot
/-- Assumption 3.4 (classical clauses), negation. -/
axiom clause_neg : ∀ I A, TrueIn I (neg A) ↔ ¬ TrueIn I A
/-- Assumption 3.4 (classical clauses), conjunction. -/
axiom clause_conj : ∀ I A B, TrueIn I (conj A B) ↔ (TrueIn I A ∧ TrueIn I B)
/-- Assumption 3.4 (classical clauses), disjunction. -/
axiom clause_disj : ∀ I A B, TrueIn I (disj A B) ↔ (TrueIn I A ∨ TrueIn I B)
/-- Assumption 3.4 (classical clauses), the material conditional. -/
axiom clause_imp : ∀ I A B, TrueIn I (imp A B) ↔ (TrueIn I A → TrueIn I B)

/-- Assumption 3.5 (freedom of atoms). Every distribution of truth values
over the atomic sentences is realized by some interpretation. -/
axiom freedom : ∀ v : Nat → Bool, ∃ I, ∀ n, TrueIn I (atom n) ↔ v n = true

/-- Definition 3.6. Consequence as truth-preservation in every interpretation. -/
def Conseq (G : Formula → Prop) (A : Formula) : Prop :=
  ∀ I, (∀ B, G B → TrueIn I B) → TrueIn I A

/-- Lemma 4.1 (truth lemma). If a valuation agrees with an interpretation on
the atoms, it agrees with it on every sentence. -/
theorem truth_lemma (I : Interp) (v : Nat → Bool)
    (h : ∀ n, TrueIn I (atom n) ↔ v n = true) :
    ∀ A, TrueIn I A ↔ eval v A = true := by
  intro A
  induction A with
  | atom n => simp only [eval]; exact h n
  | bot => simp only [eval]; exact ⟨fun hb => absurd hb (clause_bot I), fun hf => by cases hf⟩
  | neg A ih =>
    rw [clause_neg, ih]; simp only [eval]
    cases eval v A <;> simp
  | conj A B ihA ihB =>
    rw [clause_conj, ihA, ihB]; simp only [eval]
    cases eval v A <;> cases eval v B <;> simp
  | disj A B ihA ihB =>
    rw [clause_disj, ihA, ihB]; simp only [eval]
    cases eval v A <;> cases eval v B <;> simp
  | imp A B ihA ihB =>
    rw [clause_imp, ihA, ihB]; simp only [eval]
    cases eval v A <;> cases eval v B <;> simp

/-- Every interpretation induces a valuation agreeing with it on the atoms. -/
theorem induced_valuation (I : Interp) :
    ∃ v : Nat → Bool, ∀ n, TrueIn I (atom n) ↔ v n = true := by
  refine ⟨fun n => @decide (TrueIn I (atom n)) (Classical.propDecidable _), ?_⟩
  intro n
  simp

/-- Theorem 4.2 (classicality). Truth-preservation coincides with classical
consequence. -/
theorem classicality (G : Formula → Prop) (A : Formula) :
    Conseq G A ↔ ClassCons G A := by
  constructor
  · intro hC v hv
    obtain ⟨I, hI⟩ := freedom v
    have hT := truth_lemma I v hI
    exact (hT A).mp (hC I (fun B hB => (hT B).mpr (hv B hB)))
  · intro hK I hI
    obtain ⟨v, hv⟩ := induced_valuation I
    have hT := truth_lemma I v hv
    exact (hT A).mpr (hK v (fun B hB => (hT B).mp (hI B hB)))

/-- Definition 4.3. Uniform substitution of sentences for atoms. -/
def subst (σ : Nat → Formula) : Formula → Formula
  | atom n => σ n
  | bot => bot
  | neg A => neg (subst σ A)
  | conj A B => conj (subst σ A) (subst σ B)
  | disj A B => disj (subst σ A) (subst σ B)
  | imp A B => imp (subst σ A) (subst σ B)

/-- Definition 4.3. A logic is a set of sentences closed under uniform
substitution and modus ponens. -/
structure IsLogic (S : Formula → Prop) : Prop where
  subst_closed : ∀ σ A, S A → S (subst σ A)
  mp_closed : ∀ A B, S (imp A B) → S A → S B

/-- The constant substitution determined by a valuation: verum for true
atoms, falsum for false ones. -/
def constSubst (v : Nat → Bool) : Nat → Formula :=
  fun n => if v n then imp bot bot else bot

theorem eval_constSubst (v w : Nat → Bool) :
    ∀ A, eval w (subst (constSubst v) A) = eval v A := by
  intro A
  induction A with
  | atom n =>
    simp only [subst, constSubst, eval]
    cases v n <;> simp [eval]
  | bot => rfl
  | neg A ih => simp only [subst, eval, ih]
  | conj A B ihA ihB => simp only [subst, eval, ihA, ihB]
  | disj A B ihA ihB => simp only [subst, eval, ihA, ihB]
  | imp A B ihA ihB => simp only [subst, eval, ihA, ihB]

/-- Theorem 4.4 (Post maximality). A logic that contains every tautology
and some non-tautology contains every sentence. -/
theorem post_maximality (S : Formula → Prop) (hS : IsLogic S)
    (htaut : ∀ A, Taut A → S A) (A : Formula) (hA : S A) (hnt : ¬ Taut A) :
    ∀ B, S B := by
  intro B
  have ⟨v, hv⟩ : ∃ v, eval v A = false := by
    apply Classical.byContradiction
    intro hne
    apply hnt
    intro v
    cases h : eval v A
    · exact absurd ⟨v, h⟩ hne
    · rfl
  have hA' : S (subst (constSubst v) A) := hS.subst_closed _ _ hA
  have hImp : Taut (imp (subst (constSubst v) A) B) := by
    intro w
    simp only [eval, eval_constSubst, hv]
    rfl
  exact hS.mp_closed _ _ (htaut _ hImp) hA'

/-- Corollary 4.5. A non-trivial logic that contains every tautology
has exactly the tautologies as theorems. -/
theorem nontrivial_extension_is_classical (S : Formula → Prop) (hS : IsLogic S)
    (htaut : ∀ A, Taut A → S A) (hnt : ∃ B, ¬ S B) :
    ∀ A, S A ↔ Taut A := by
  intro A
  constructor
  · intro hA
    apply Classical.byContradiction
    intro hnA
    obtain ⟨B, hB⟩ := hnt
    exact hB (post_maximality S hS htaut A hA hnA B)
  · exact htaut A

/-- Corollary 4.6 (collapse). Any two relations that coincide with
truth-preservation coincide with classical consequence, and so with each
other. -/
theorem collapse (R₀ R₁ : (Formula → Prop) → Formula → Prop)
    (h₀ : ∀ G A, R₀ G A ↔ Conseq G A) (h₁ : ∀ G A, R₁ G A ↔ Conseq G A) :
    ∀ G A, (R₀ G A ↔ ClassCons G A) ∧ (R₀ G A ↔ R₁ G A) := by
  intro G A
  exact ⟨(h₀ G A).trans (classicality G A), (h₀ G A).trans (h₁ G A).symm⟩

/-- Definition 5.1. A many-valued semantics on the values 0, …, k, with
0 as falsity and k as full truth. -/
structure MVSemantics where
  k : Nat
  mneg : Nat → Nat
  mconj : Nat → Nat → Nat
  mdisj : Nat → Nat → Nat
  mimp : Nat → Nat → Nat

/-- Definition 5.1. Evaluation in a many-valued semantics. -/
def mval (M : MVSemantics) (u : Nat → Nat) : Formula → Nat
  | atom n => u n
  | bot => 0
  | neg A => M.mneg (mval M u A)
  | conj A B => M.mconj (mval M u A) (mval M u B)
  | disj A B => M.mdisj (mval M u A) (mval M u B)
  | imp A B => M.mimp (mval M u A) (mval M u B)

/-- The classical value corresponding to a Boolean. -/
def cl (k : Nat) (b : Bool) : Nat := if b then k else 0

/-- Definition 5.1. A semantics is regular if its connectives agree with
the classical ones on the classical values. -/
def Regular (M : MVSemantics) : Prop :=
  (∀ a, M.mneg (cl M.k a) = cl M.k (!a)) ∧
  (∀ a b, M.mconj (cl M.k a) (cl M.k b) = cl M.k (a && b)) ∧
  (∀ a b, M.mdisj (cl M.k a) (cl M.k b) = cl M.k (a || b)) ∧
  (∀ a b, M.mimp (cl M.k a) (cl M.k b) = cl M.k (!a || b))

/-- Theorem 5.2 (conservativeness). In a regular semantics, a sentence whose
atoms receive classical values receives the classical value of its
classical evaluation. -/
theorem conservativeness (M : MVSemantics) (hM : Regular M) (v : Nat → Bool) :
    ∀ A, mval M (fun n => cl M.k (v n)) A = cl M.k (eval v A) := by
  obtain ⟨hn, hc, hd, hi⟩ := hM
  intro A
  induction A with
  | atom n => rfl
  | bot => simp [mval, eval, cl]
  | neg A ih => simp only [mval, eval, ih, hn]
  | conj A B ihA ihB => simp only [mval, eval, ihA, ihB, hc]
  | disj A B ihA ihB => simp only [mval, eval, ihA, ihB, hd]
  | imp A B ihA ihB => simp only [mval, eval, ihA, ihB, hi]

/-- Corollary 5.3. On classically valued atoms, consequence in a regular
semantics with k > 0 designating k coincides with classical consequence. -/
theorem conservative_consequence (M : MVSemantics) (hM : Regular M) (hk : 0 < M.k)
    (G : Formula → Prop) (A : Formula) :
    (∀ v : Nat → Bool, (∀ B, G B → mval M (fun n => cl M.k (v n)) B = M.k) →
        mval M (fun n => cl M.k (v n)) A = M.k) ↔ ClassCons G A := by
  have key : ∀ (v : Nat → Bool) (C : Formula),
      mval M (fun n => cl M.k (v n)) C = M.k ↔ eval v C = true := by
    intro v C
    rw [conservativeness M hM v C]
    cases eval v C <;> simp [cl] <;> omega
  constructor
  · intro h v hv
    exact (key v A).mp (h v (fun B hB => (key v B).mpr (hv B hB)))
  · intro h v hv
    exact (key v A).mpr (h v (fun B hB => (key v B).mp (hv B hB)))

/-- Definition 5.1. The Łukasiewicz semantics on 0, …, k (as in LOG-01). -/
def luk (k : Nat) : MVSemantics :=
  ⟨k, fun x => k - x, fun x y => min x y, fun x y => max x y,
    fun x y => min k (k - x + y)⟩

/-- Definition 5.1. The strong Kleene semantics on 0, …, k (as in LOG-03,
with k = 2), with the conditional defined as ¬A ∨ B. -/
def kleene (k : Nat) : MVSemantics :=
  ⟨k, fun x => k - x, fun x y => min x y, fun x y => max x y,
    fun x y => max (k - x) y⟩

/-- Corollary 5.3. The Łukasiewicz semantics is regular. -/
theorem luk_regular (k : Nat) : Regular (luk k) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp only [luk, cl] <;> split <;> (try split) <;> simp_all <;> omega

/-- Corollary 5.3. The strong Kleene semantics is regular. -/
theorem kleene_regular (k : Nat) : Regular (kleene k) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp only [kleene, cl] <;> split <;> (try split) <;> simp_all <;> omega

/-- Proposition 5.4. The Łukasiewicz conditional contracts on classical
values: on 0 and k, A → (A → B) and A → B have the same value. -/
theorem contraction_on_classical (k : Nat) (a b : Bool) :
    (luk k).mimp (cl k a) ((luk k).mimp (cl k a) (cl k b)) =
      (luk k).mimp (cl k a) (cl k b) := by
  cases a <;> cases b <;> simp [luk, cl] <;> omega

end Philosophy.LOG_02

#print axioms Philosophy.LOG_02.classicality
#print axioms Philosophy.LOG_02.post_maximality
#print axioms Philosophy.LOG_02.nontrivial_extension_is_classical
#print axioms Philosophy.LOG_02.conservative_consequence
