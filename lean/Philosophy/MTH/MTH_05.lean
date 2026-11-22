/-
MTH-05 · Gödel's Theorem and the Mechanist Thesis
Formalization of Theorem 3.1 and Corollaries 3.2 to 3.4.

What this file establishes. Suppose that the arithmetical sentences a mind
can come to know are exactly the theorems of a formal system S (the
mechanist hypothesis, Definition 2.3) and that S is consistent. Then the
mind cannot know the Gödel sentence of S, nor the consistency sentence of
S, nor that it is S and S is sound: it stands to its own Gödel sentence as
S does (Theorem 3.1, Corollaries 3.3 and 3.4). Lucas's premise, that the mind knows
the Gödel sentence of every consistent system, is therefore equivalent to
the denial of mechanism for consistent systems and cannot be used to
establish that denial without begging the question (Corollary 3.2).

What it does not establish. It does not prove Gödel's theorems, which are
taken as Assumption 2.2; it does not show that the mind is a machine, nor
that a mind that is not a machine can know its own consistency.
-/

namespace Philosophy.MTH_05

/-- Formal systems: effectively axiomatized, containing elementary
arithmetic. -/
axiom System : Type

/-- Arithmetical sentences. -/
axiom Sentence : Type

/-- Minds, idealized as knowers of arithmetical sentences. -/
axiom Mind : Type

/-- `Prov S φ`: the system `S` proves `φ`. -/
axiom Prov : System → Sentence → Prop

/-- `Consistent S`: the system `S` is consistent. -/
axiom Consistent : System → Prop

/-- Definition 2.1. The Gödel sentence `G_S` of a system. -/
axiom godel : System → Sentence

/-- Definition 2.1. The consistency sentence `Con_S` of a system. -/
axiom con : System → Sentence

/-- `Knows m φ`: the mind `m` can come to know the arithmetical sentence `φ`. -/
axiom Knows : Mind → Sentence → Prop

/-- `KnowsSelf m S`: `m` knows that its arithmetical knowledge is that of `S`
and that `S` is sound (the premise of Penrose's argument). -/
axiom KnowsSelf : Mind → System → Prop

/-- Assumption 2.2 (Gödel's first incompleteness theorem). A consistent
system does not prove its Gödel sentence. -/
axiom first_incompleteness : ∀ S, Consistent S → ¬ Prov S (godel S)

/-- Definition 2.3 (mechanist hypothesis for `m` and `S`). The arithmetical
sentences `m` can know are exactly the theorems of `S`. -/
def Mechanical (m : Mind) (S : System) : Prop := ∀ p, Knows m p ↔ Prov S p

/-- Assumption 2.4 (closure). A mind that knows `Con_S` knows `G_S`, since it
knows the formalized first incompleteness theorem and can apply modus
ponens. -/
axiom closure : ∀ m S, Knows m (con S) → Knows m (godel S)

/-- Assumption 2.5 (Penrose's route). A mind that knows that it is `S` and
that `S` is sound knows `Con_S`. -/
axiom self_knowledge_gives_con : ∀ m S, KnowsSelf m S → Knows m (con S)

/-- Definition 2.6 (Lucas's premise). `m` knows the Gödel sentence of every
consistent system. -/
def Lucasian (m : Mind) : Prop := ∀ S, Consistent S → Knows m (godel S)

/-- Theorem 3.1 (parity). If `m` is mechanical with respect to a consistent
`S`, then `m` knows `G_S` exactly when `S` proves it, and neither `G_S` nor
`Con_S` is known by `m`. -/
theorem parity (m : Mind) (S : System) (hM : Mechanical m S)
    (hC : Consistent S) :
    (Knows m (godel S) ↔ Prov S (godel S)) ∧
      ¬ Knows m (godel S) ∧ ¬ Knows m (con S) := by
  have hG : ¬ Knows m (godel S) := fun h =>
    first_incompleteness S hC ((hM (godel S)).mp h)
  exact ⟨hM (godel S), hG, fun h => hG (closure m S h)⟩

/-- Corollary 3.2 (Lucas's premise is anti-mechanism). A Lucasian mind is
mechanical with respect to no consistent system. -/
theorem lucas_premise_denies_mechanism (m : Mind) (hL : Lucasian m) :
    ∀ S, Consistent S → ¬ Mechanical m S :=
  fun S hC hM => (parity m S hM hC).2.1 (hL S hC)

/-- Corollary 3.3 (Gödel's disjunction). For every mind and consistent
system, either the mind is not mechanical with respect to the system or it
cannot know the system's Gödel sentence. -/
theorem disjunction (m : Mind) (S : System) (hC : Consistent S) :
    ¬ Mechanical m S ∨ ¬ Knows m (godel S) :=
  Classical.byCases
    (fun hM : Mechanical m S => Or.inr (parity m S hM hC).2.1)
    (fun hM => Or.inl hM)

/-- Corollary 3.4 (Penrose's premise). A mind mechanical with respect to a
consistent system cannot know that it is that system and that the system is
sound. -/
theorem no_self_knowledge (m : Mind) (S : System) (hM : Mechanical m S)
    (hC : Consistent S) : ¬ KnowsSelf m S :=
  fun h => (parity m S hM hC).2.2 (self_knowledge_gives_con m S h)

end Philosophy.MTH_05

#print axioms Philosophy.MTH_05.parity
#print axioms Philosophy.MTH_05.lucas_premise_denies_mechanism
#print axioms Philosophy.MTH_05.no_self_knowledge
