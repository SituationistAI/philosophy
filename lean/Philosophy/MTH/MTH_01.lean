/-
MTH-01 · On the Existence of Numbers
Formalization of the logical skeleton of Theorem 5.2, Proposition 5.3, Lemma 5.1,
Corollary 5.4 and Proposition 5.7, and a fragment of the dependency computation of
Appendices B and E.

What this file establishes. From weak holism (Principle P1), the regimentation principle
(Principle P2) and Assumptions 4.5–4.7, belief in the existence of numbers, and in their
abstractness, is justified; and, separately, from inference to the best explanation and
Baker's premises without weak holism, belief in the existence of natural numbers is
justified. It also verifies by `decide`, for sixteen structures, the presupposition
closures used in Remark 5.6 and Proposition 6.2 (vii).

What it does not establish. The premises are axioms: their defence is the manuscript's
(Sections 4 and 6–12). Degrees of justification are not modelled; weak holism is stated in
its qualitative consequence. Cantor's theorem on the cardinality of the reals is not
formalized. The full inventory is computed by the Python generator, not here.
-/

namespace Philosophy.MTH_01

/-! ## Part 1. The argument -/

/-- Primitive: theories (regimented, Definition 4.1). -/
axiom Theory : Type
/-- Primitive: kinds of entity. -/
axiom Kind : Type
/-- Primitive: hypotheses. -/
axiom Hyp : Type

/-- The conjunction of our best physical theories. -/
axiom physics : Theory
/-- The kind number (the five number systems of Assumption 4.6). -/
axiom numbers : Kind
/-- The kind real number. -/
axiom reals : Kind
/-- The hypothesis that things of a kind exist. -/
axiom exists_ : Kind → Hyp
/-- The hypothesis that things of a kind are abstract (Definition 3.1). -/
axiom abstract_ : Kind → Hyp

/-- Confirmation relative to available rivals. -/
axiom Confirmed : Theory → Prop
/-- Definition 4.1: the theory quantifies over the kind. -/
axiom quantifies : Theory → Kind → Prop
/-- Definition 4.3 (with Definition 4.2): some reformulation retaining the theory's virtues does not quantify over the kind. -/
axiom Dispensable : Theory → Kind → Prop
/-- Definition 4.4: the hypothesis is an ineliminable part of the theory. -/
axiom Ineliminable : Theory → Hyp → Prop
/-- Justified belief (to a degree not less than in the relevant theory). -/
axiom Justified : Hyp → Prop
/-- The theory assigns the kind a spatiotemporal location or a causal role. -/
axiom locatedOrCausal : Theory → Kind → Prop

/-- Definition 4.3: indispensability. -/
def Indispensable (T : Theory) (k : Kind) : Prop := quantifies T k ∧ ¬ Dispensable T k

/-- Principle P1 (weak holism). -/
axiom principle_weak_holism :
  ∀ (T : Theory) (h : Hyp), Confirmed T → Ineliminable T h → Justified h

/-- Principle P2 (regimentation, Quine's criterion for kinds). -/
axiom principle_regimentation :
  ∀ (T : Theory) (k : Kind), Indispensable T k → Ineliminable T (exists_ k)

/-- Assumption 4.5 (confirmation). -/
axiom assumption_confirmation : Confirmed physics

/-- Assumption 4.6 (indispensability of numbers, the reals among them). -/
axiom assumption_indispensability : Indispensable physics numbers ∧ Indispensable physics reals

/-- Assumption 4.7 (non-location). -/
axiom assumption_nonlocation : ¬ locatedOrCausal physics numbers

/-- The step in the proof of Proposition 5.3: what is indispensable to a confirmed theory
that assigns it no location or causal role is justifiably believed abstract. -/
axiom abstract_transfer :
  ∀ (T : Theory) (k : Kind), Confirmed T → Indispensable T k → ¬ locatedOrCausal T k →
    Justified (abstract_ k)

/-- Lemma 5.1 (commitment). -/
theorem commitment (T : Theory) (k : Kind) (hc : Confirmed T) (hi : Indispensable T k) :
    Justified (exists_ k) :=
  principle_weak_holism T (exists_ k) hc (principle_regimentation T k hi)

/-- Theorem 5.2 (existence of numbers). -/
theorem numbers_exist : Justified (exists_ numbers) :=
  commitment physics numbers assumption_confirmation assumption_indispensability.1

/-- Proposition 5.3 (abstractness). -/
theorem numbers_abstract : Justified (abstract_ numbers) :=
  abstract_transfer physics numbers assumption_confirmation
    assumption_indispensability.1 assumption_nonlocation

/-- Theorem 5.2 with Proposition 5.3: the conclusion of MTH-01. -/
theorem numbers_exist_and_abstract :
    Justified (exists_ numbers) ∧ Justified (abstract_ numbers) :=
  ⟨numbers_exist, numbers_abstract⟩

/-- Corollary 5.4 (the reals; existence part). -/
theorem reals_exist : Justified (exists_ reals) :=
  commitment physics reals assumption_confirmation assumption_indispensability.2

/-! ### The explanatory route (Proposition 5.7) -/

/-- Primitive: explanations. -/
axiom Explanation : Type
/-- The kind natural number. -/
axiom naturals : Kind
/-- Baker's explanation of the prime life cycles of periodical cicadas. -/
axiom cicada : Explanation
/-- Being the best available explanation of a physical phenomenon. -/
axiom Best : Explanation → Prop
/-- The explanation quantifies essentially over the kind. -/
axiom EssentialIn : Explanation → Kind → Prop

/-- Inference to the best explanation, with Principle P2 applied to explanations. -/
axiom ibe : ∀ (e : Explanation) (k : Kind), Best e → EssentialIn e k → Justified (exists_ k)
/-- Baker's first premise: the number-theoretic explanation is the best available. -/
axiom baker_best : Best cicada
/-- Baker's second premise: it quantifies essentially over natural numbers. -/
axiom baker_essential : EssentialIn cicada naturals

/-- Proposition 5.7 (explanatory route): no use of Principle P1. -/
theorem explanatory_route : Justified (exists_ naturals) :=
  ibe cicada naturals baker_best baker_essential

/-! ## Part 2. A fragment of the dependency computation (Appendices B and E) -/

/-- Sixteen structures of the register (Appendix B); `Sq` is the structure of sequences. -/
inductive Str where
  | N | Z | Q | Sq | R | C | Vc | Top | Hil | Bor | Meas | Op | PR | Leb | Lmeas | L2
  deriving DecidableEq, Repr

open Str

/-- Direct presuppositions, as in the register of Appendix B. -/
def deps : Str → List Str
  | N => [] | Z => [N] | Q => [Z] | Sq => [N] | R => [Q, Sq] | C => [R]
  | Vc => [C] | Top => [R] | Hil => [Vc, Sq, Top] | Bor => [Top] | Meas => [Bor, R]
  | Op => [Hil, Bor, Meas] | PR => [R] | Leb => [Bor, PR] | Lmeas => [Leb, R]
  | L2 => [Lmeas, Hil, C]

/-- Reachability in at most `n` presupposition steps. -/
def reach : Nat → Str → Str → Bool
  | 0, a, b => a == b
  | n + 1, a, b => a == b || (deps a).any (fun c => reach n c b)

/-- Membership in the closure (the graph has fewer than twelve levels). -/
def inCl (a b : Str) : Bool := reach 12 a b

def allStr : List Str := [N, Z, Q, Sq, R, C, Vc, Top, Hil, Bor, Meas, Op, PR, Leb, Lmeas, L2]
def numberSystems : List Str := [N, Z, Q, R, C]

/-- Remark 5.6 and Proposition 6.2: the number systems presupposed by `L2` are exactly ℕ, ℤ, ℚ, ℝ, ℂ. -/
theorem l2_numbers : numberSystems.filter (inCl L2) = [N, Z, Q, R, C] := by decide

/-- Proposition 6.2 (vii): the Lebesgue σ-algebra (cardinality 2^𝔠) is reached through `L2`,
not through the abstract Hilbert space or its operators. -/
theorem lebesgue_via_l2 : inCl L2 Leb = true ∧ inCl Hil Leb = false ∧ inCl Op Leb = false := by
  decide

/-- Appendix E: the closure of the operators. -/
theorem op_closure :
    allStr.filter (inCl Op) = [N, Z, Q, Sq, R, C, Vc, Top, Hil, Bor, Meas, Op] := by decide

end Philosophy.MTH_01

#print axioms Philosophy.MTH_01.numbers_exist_and_abstract
#print axioms Philosophy.MTH_01.explanatory_route
#print axioms Philosophy.MTH_01.l2_numbers
