/-
PHE-22 · On the Impossibility of Machine Epoché
Formalization of Lemma 2.4 and Theorem 2.6.

What this file establishes. Given that no act of suspension suspends itself
(Assumption 2.3), every system that suspends commitments performs an operation
it does not suspend; and given that nothing is given to a machine in
reflection as its own act (Assumption 2.5), a machine does not perform the
epoché. It does not establish Assumption 2.5, which is the substantive premise.
-/

namespace Philosophy.PHE_22

/-- Systems: subjects and machines. -/
axiom System : Type

/-- Operations a system may perform. -/
axiom Operation : Type

/-- `Performs s o`: system `s` performs operation `o`. -/
axiom Performs : System → Operation → Prop

/-- `Suspends b o`: operation `b` suspends (brackets) operation `o`. -/
axiom Suspends : Operation → Operation → Prop

/-- `GivenInReflection s o`: `o` is given to `s` in reflection as its own act. -/
axiom GivenInReflection : System → Operation → Prop

/-- Machines. -/
axiom Machine : System → Prop

/-- Assumption 2.3 (residue). No act of suspension suspends itself. -/
axiom residue : ∀ b, ¬ Suspends b b

/-- Assumption 2.5. Nothing is given to a machine in reflection as its own act. -/
axiom machine_no_reflection : ∀ s o, Machine s → ¬ GivenInReflection s o

/-- Definition 2.2. `s` performs the epoché by the operation `b`. -/
def PerformsEpoche (s : System) (b : Operation) : Prop :=
  Performs s b ∧ GivenInReflection s b

/-- Lemma 2.4. A system that suspends by `b` performs an operation that `b`
does not suspend, namely `b` itself. -/
theorem remains (s : System) (b : Operation) (h : Performs s b) :
    ∃ o, Performs s o ∧ ¬ Suspends b o :=
  ⟨b, h, residue b⟩

/-- Theorem 2.6. A machine does not perform the epoché. -/
theorem no_machine_epoche (s : System) (hm : Machine s) (b : Operation) :
    ¬ PerformsEpoche s b :=
  fun ⟨_, hg⟩ => machine_no_reflection s b hm hg

end Philosophy.PHE_22

#print axioms Philosophy.PHE_22.no_machine_epoche
