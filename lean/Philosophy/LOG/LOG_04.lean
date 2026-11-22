/-
LOG-04 · Curry's Paradox and the Failure of Contraction
Formalization of Lemma 3.1, Propositions 3.2–3.4, Theorem 3.5, Lemma 4.1,
Theorems 4.2 and 4.3, and Corollary 4.4.

Truth values are those of the (k+1)-valued Łukasiewicz logic L_k, as in
LOG-01: the natural numbers 0, …, k, with the conditional
`min k (k - x + y)` (Definition 2.1). The n-fold conditional `x →^n y`
nests n copies of the antecedent (Definition 2.2).

The consequence relation of the logic is an opaque relation `Proves`
between lists of premises and conclusions. It is assumed to contain the
rule of assumption, modus ponens and conjunction elimination
(Assumption 2.4) and to be sound for full truth in every L_k
(Assumption 2.5). These assumptions are jointly consistent: semantic
consequence in the L_k satisfies all of them.

What this file establishes. Every finite form of contraction fails in some
L_k; the Curry sentence and its n-fold variants have values short of full
truth; a logic with contraction, modus ponens and conjunction elimination
proves anything from Curry's biconditional; and a logic that is sound for
the L_k does not, so contraction is not one of its rules. It does not
establish the theory of naive truth with quantifiers, nor that soundness
for the Łukasiewicz valuations is the right constraint on the conditional,
which Section 2 of the manuscript defends.
-/

namespace Philosophy.LOG_04

/-- Definition 2.1. The Łukasiewicz conditional on L_k. -/
def imp (k x y : Nat) : Nat := min k (k - x + y)

/-- Definition 2.2. The n-fold conditional x →^n y. -/
def impIter (k x y : Nat) : Nat → Nat
  | 0 => y
  | n + 1 => imp k x (impIter k x y n)

/-- Lemma 3.1. x →^n 0 has the value min(k, n(k - x)). -/
theorem impIter_zero (k x : Nat) : ∀ n, impIter k x 0 n = min k (n * (k - x)) := by
  intro n
  induction n with
  | zero => simp [impIter]
  | succ n ih =>
    simp only [impIter, imp, ih, Nat.succ_mul]
    generalize n * (k - x) = m
    omega

/-- Proposition 3.2. Curry's sentence C, equivalent to C → ⊥, has an
acceptable value iff 2x = k: the liar's value (LOG-01). -/
theorem curry_value (k x : Nat) (hx : x ≤ k) : imp k x 0 = x ↔ 2 * x = k := by
  simp only [imp]; omega

/-- Proposition 3.3. Contraction fails: with k = 2, x = 1, y = 0,
x → (x → y) is fully true and x → y is not. -/
theorem contraction_fails : imp 2 1 (imp 2 1 0) = 2 ∧ imp 2 1 0 = 1 := by decide

/-- Proposition 3.4. Modus ponens preserves full truth. -/
theorem mp_preserves (k x y : Nat) (hy : y ≤ k) (hx : x = k) (h : imp k x y = k) :
    y = k := by
  simp only [imp] at h; omega

/-- Theorem 3.5. For every n, (n+1)-fold contraction fails in L_{n+1}:
x →^(n+1) ⊥ is fully true at x = n while x →^n ⊥ has the value n. -/
theorem n_contraction_fails (n : Nat) :
    impIter (n + 1) n 0 (n + 1) = n + 1 ∧ impIter (n + 1) n 0 n = n := by
  rw [impIter_zero, impIter_zero]
  have h : n + 1 - n = 1 := by omega
  rw [h, Nat.mul_one, Nat.mul_one]
  omega

/-- Theorem 4.3 (part). The n-fold Curry sentence C ≡ C →^n ⊥ has the
acceptable value n in L_{n+1}, which is short of full truth. -/
theorem n_curry_value (n : Nat) :
    impIter (n + 1) n 0 n = n ∧ n < n + 1 :=
  ⟨(n_contraction_fails n).2, Nat.lt_succ_self n⟩

/-- Definition 2.3. Formulas. -/
inductive Formula where
  | atom : Nat → Formula
  | bot : Formula
  | imp : Formula → Formula → Formula
  | conj : Formula → Formula → Formula

/-- Definition 2.3. Evaluation in L_k. -/
def eval (k : Nat) (v : Nat → Nat) : Formula → Nat
  | .atom n => min k (v n)
  | .bot => 0
  | .imp A B => imp k (eval k v A) (eval k v B)
  | .conj A B => min (eval k v A) (eval k v B)

/-- The biconditional. -/
def bic (A B : Formula) : Formula := .conj (.imp A B) (.imp B A)

/-- Curry's biconditional for the atom c and the conclusion b:
c ↔ (c → b). -/
def curry (c b : Nat) : Formula := bic (.atom c) (.imp (.atom c) (.atom b))

/-- The consequence relation of the logic of the conditional. -/
axiom Proves : List Formula → Formula → Prop

/-- Assumption 2.4 (a). Premises are derivable. -/
axiom hyp : ∀ {Γ : List Formula} {A : Formula}, A ∈ Γ → Proves Γ A

/-- Assumption 2.4 (b). Modus ponens. -/
axiom mp : ∀ {Γ : List Formula} {A B : Formula},
  Proves Γ A → Proves Γ (.imp A B) → Proves Γ B

/-- Assumption 2.4 (c). Conjunction elimination. -/
axiom andL : ∀ {Γ : List Formula} {A B : Formula}, Proves Γ (.conj A B) → Proves Γ A
axiom andR : ∀ {Γ : List Formula} {A B : Formula}, Proves Γ (.conj A B) → Proves Γ B

/-- Assumption 2.5 (Soundness). Whatever the logic proves from premises is
fully true in every L_k valuation that makes the premises fully true. -/
axiom sound : ∀ {Γ : List Formula} {A : Formula}, Proves Γ A →
  ∀ (k : Nat) (v : Nat → Nat), (∀ g, g ∈ Γ → eval k v g = k) → eval k v A = k

/-- Contraction, as a rule of the logic. -/
def Contraction : Prop :=
  ∀ (Γ : List Formula) (A B : Formula), Proves Γ (.imp A (.imp A B)) → Proves Γ (.imp A B)

/-- Lemma 4.1 (Curry's derivation). With contraction, Curry's biconditional
proves an arbitrary sentence. -/
theorem curry_with_contraction (contr : Contraction) (c b : Nat) :
    Proves [curry c b] (.atom b) := by
  have h0 : Proves [curry c b] (curry c b) := hyp (List.mem_singleton_self _)
  have h1 := andL h0
  have h2 := contr _ _ _ h1
  have h3 := andR h0
  have h4 := mp h2 h3
  exact mp h4 h2

/-- Theorem 4.2. Curry's sentence proves nothing: for distinct atoms c and b,
Curry's biconditional does not prove b. -/
theorem curry_proves_nothing (c b : Nat) (hcb : c ≠ b) :
    ¬ Proves [curry c b] (.atom b) := by
  intro hp
  have hs := sound hp 2 (fun n => if n = c then 1 else 0)
  have hprem : ∀ g, g ∈ [curry c b] → eval 2 (fun n => if n = c then 1 else 0) g = 2 := by
    intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    simp [curry, bic, eval, imp, Ne.symm hcb]
    decide
  have := hs hprem
  simp [eval, Ne.symm hcb] at this

/-- Theorem 4.3 (part). The n-fold Curry sentence C ≡ C →^n ⊥ is not fully
true in L_{n+1}, so it proves nothing. Same as `n_curry_value`. -/
theorem n_curry_proves_nothing (n : Nat) : impIter (n + 1) n 0 n ≠ n + 1 := by
  rw [(n_contraction_fails n).2]; omega

/-- Corollary 4.4. Contraction is not a rule of any logic satisfying
Assumptions 2.4 and 2.5. -/
theorem no_contraction : ¬ Contraction := fun contr =>
  curry_proves_nothing 0 1 (by decide) (curry_with_contraction contr 0 1)

end Philosophy.LOG_04

#print axioms Philosophy.LOG_04.curry_proves_nothing
#print axioms Philosophy.LOG_04.no_contraction
#print axioms Philosophy.LOG_04.n_contraction_fails
