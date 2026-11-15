/-
MTE-01 · Moral Realism Established
Formalization of Lemma 4.1, Theorems 4.2 and 4.3, Propositions 5.2 and 5.4,
Theorem 6.2 and Corollary 6.3.

Moral terms refer by role (Principle P1): "wrong" refers to the property that
realizes the wrongness role (Definition 3.4). The role has five clauses. The
property of idealized disapproval (Definition 3.5), on which the idealized
reactions of all agents converge, satisfies each clause; the role has a
unique realizer up to coextension (Assumption 3.6); idealized reactions are
natural facts and natural facts are closed under quantification over agents
(Assumptions 3.7, 3.8); and idealized reactions converge on some act
(Assumption 3.9).

What this file establishes.
* Wrongness is coextensive with idealized disapproval (Theorem 4.2).
* Some act is wrong, and every fact of the form "a is wrong" is a natural
  fact (Theorem 4.3).
* The open question argument is invalid: its premises are jointly
  satisfiable together with the coreference of "good" and a descriptive
  concept (Proposition 5.2), and Moore's bridge principle from openness to
  distinctness of reference is false given the a posteriori identity of
  water and H2O (Assumption 5.3, Proposition 5.4).
* In a modal extension, moral facts supervene on the natures of agents and
  the natural circumstances of acts, so that worlds differing only in the
  actual attitudes of agents do not differ morally (Theorem 6.2,
  Corollary 6.3).

What it does not establish. It does not establish the premises: that the
role clauses hold of idealized disapproval (defended in Section 4), the
uniqueness of the realizer (Section 4), the naturalness of idealized
reactions (Section 3), the convergence of idealized reactions on any act
(Section 7), or the dependence assumption of Section 6. Facts are
individuated coarsely, as propositions, so the module cannot distinguish
necessarily coextensive properties (see Section 9 of the manuscript).
-/

namespace Philosophy.MTE_01

/-! ## Sections 3 and 4: the identification of wrongness -/

/-- Acts, the objects of moral assessment. -/
axiom Act : Type

/-- Agents, each considered under idealization (Definition 3.3). -/
axiom Agent : Type

/-- Definition 3.3. `disapproves i a`: the idealized reaction of agent `i`
to act `a` is disapproval. -/
axiom disapproves : Agent → Act → Prop

/-- Definition 3.2. Natural facts, as a predicate on propositions. -/
axiom NaturalFact : Prop → Prop

/-- Wrongness: the property to which the predicate "wrong" refers. -/
axiom wrong : Act → Prop

/-- Definition 3.4, clause (a): the property supervenes on natural features. -/
axiom Supervenient : (Act → Prop) → Prop
/-- Definition 3.4, clause (b): the property bears on what rational agents
are disposed to do (practical authority). -/
axiom Authoritative : (Act → Prop) → Prop
/-- Definition 3.4, clause (c): the property is what moral inquiry under
improving conditions tends toward. -/
axiom InquiryTarget : (Act → Prop) → Prop
/-- Definition 3.4, clause (d): the property concerns how an act bears on
everyone affected. -/
axiom Impartial : (Act → Prop) → Prop
/-- Definition 3.4, clause (e): any actual agent or community can be
mistaken about which acts have the property. -/
axiom Fallible : (Act → Prop) → Prop

/-- Definition 3.4. The wrongness role. -/
def WrongRole (P : Act → Prop) : Prop :=
  Supervenient P ∧ Authoritative P ∧ InquiryTarget P ∧ Impartial P ∧ Fallible P

/-- Definition 3.5. Idealized disapproval: the idealized reactions of all
agents converge on disapproval. -/
def IdealDisapproval (a : Act) : Prop := ∀ i, disapproves i a

/-- Principle P1 (reference by role). "Wrong" refers to a property that
realizes the wrongness role. -/
axiom p1_reference_by_role : WrongRole wrong

/-- Assumption 3.6 (uniqueness). Any two realizers of the wrongness role are
coextensive. -/
axiom assumption_3_6 :
  ∀ P Q : Act → Prop, WrongRole P → WrongRole Q → ∀ a, (P a ↔ Q a)

/-- Assumption 3.7 (naturalness). Facts about idealized reactions are
natural facts. -/
axiom assumption_3_7 : ∀ i a, NaturalFact (disapproves i a)

/-- Assumption 3.8 (closure). A universal quantification over agents of
natural facts is a natural fact. -/
axiom assumption_3_8 :
  ∀ P : Agent → Prop, (∀ i, NaturalFact (P i)) → NaturalFact (∀ i, P i)

/-- Assumption 3.9 (convergence on core cases). Idealized reactions
converge on disapproval of at least one act. -/
axiom assumption_3_9 : ∃ a, ∀ i, disapproves i a

/-- Lemma 4.1, clause (a), as argued in Section 4. -/
axiom lemma_4_1_a : Supervenient IdealDisapproval
/-- Lemma 4.1, clause (b), as argued in Section 4 (with MTE-07). -/
axiom lemma_4_1_b : Authoritative IdealDisapproval
/-- Lemma 4.1, clause (c), as argued in Section 4. -/
axiom lemma_4_1_c : InquiryTarget IdealDisapproval
/-- Lemma 4.1, clause (d), as argued in Section 4. -/
axiom lemma_4_1_d : Impartial IdealDisapproval
/-- Lemma 4.1, clause (e), as argued in Section 4. -/
axiom lemma_4_1_e : Fallible IdealDisapproval

/-- Lemma 4.1. Idealized disapproval realizes the wrongness role. -/
theorem lemma_4_1 : WrongRole IdealDisapproval :=
  ⟨lemma_4_1_a, lemma_4_1_b, lemma_4_1_c, lemma_4_1_d, lemma_4_1_e⟩

/-- Theorem 4.2 (identification). Wrongness is coextensive with idealized
disapproval. -/
theorem identification : ∀ a, wrong a ↔ IdealDisapproval a :=
  assumption_3_6 wrong IdealDisapproval p1_reference_by_role lemma_4_1

/-- Theorem 4.3 (moral realism). Some act is wrong, and every fact of the
form "a is wrong" is a natural fact. -/
theorem realism : (∃ a, wrong a) ∧ (∀ a, NaturalFact (wrong a)) := by
  constructor
  · obtain ⟨a, h⟩ := assumption_3_9
    exact ⟨a, (identification a).mpr h⟩
  · intro a
    have h : wrong a = IdealDisapproval a := propext (identification a)
    rw [h]
    exact assumption_3_8 (fun i => disapproves i a) (fun i => assumption_3_7 i a)

/-! ## Section 5: the open question argument -/

/-- An interpretation of the vocabulary of the open question
argument: concepts, their referents, the relation of a question's being open
to competent speakers (Definition 5.1), and synonymy. -/
structure OQInterp where
  Concept : Type
  Referent : Type
  ref : Concept → Referent
  Open : Concept → Concept → Prop
  Syn : Concept → Concept → Prop
  good : Concept

/-- Moore's premises in an interpretation: every question "is a thing that is
C good?" is open, for C other than "good" itself, and openness excludes
synonymy. -/
def MoorePremises (I : OQInterp) : Prop :=
  (∀ c, c ≠ I.good → I.Open c I.good) ∧ (∀ c d, I.Open c d → ¬ I.Syn c d)

/-- Proposition 5.2 (invalidity). Moore's premises are satisfiable together
with the coreference of "good" and a distinct concept. -/
theorem oqa_invalid :
    ∃ I : OQInterp, MoorePremises I ∧ ∃ n, n ≠ I.good ∧ I.ref n = I.ref I.good := by
  refine ⟨⟨Bool, Unit, fun _ => (), fun c d => c ≠ d, fun c d => c = d, true⟩,
    ⟨fun c h => h, fun _ _ h => h⟩, false, by decide, rfl⟩

/-- Concepts, for the actual case of Proposition 5.4. -/
axiom Concept : Type
/-- Properties, the referents of predicative concepts. -/
axiom Property : Type
/-- Reference. -/
axiom refersTo : Concept → Property
/-- Openness to competent speakers (Definition 5.1). -/
axiom Open : Concept → Concept → Prop
/-- The concepts water and H2O. -/
axiom waterC : Concept
axiom h2oC : Concept

/-- Principle P2 (Moore's bridge principle). Openness entails distinctness of
reference. -/
def P2 : Prop := ∀ c d, Open c d → refersTo c ≠ refersTo d

/-- Assumption 5.3 (the a posteriori identity), first part. The question
whether water is H2O is open to competent speakers. -/
axiom assumption_5_3_open : Open waterC h2oC
/-- Assumption 5.3, second part. The concepts water and H2O corefer. -/
axiom assumption_5_3_coref : refersTo waterC = refersTo h2oC

/-- Proposition 5.4. Moore's bridge principle is false. -/
theorem p2_false : ¬ P2 :=
  fun h => h waterC h2oC assumption_5_3_open assumption_5_3_coref

/-! ## Section 6: supervenience and attitude-independence -/

/-- Possible worlds. -/
axiom World : Type
/-- Natures of agents: their stable constitution and capacities. -/
axiom Nature : Type
/-- Natural circumstances of acts. -/
axiom Circ : Type
/-- The nature of an agent at a world. -/
axiom natureAt : World → Agent → Nature
/-- The natural circumstances of an act at a world. -/
axiom circAt : World → Act → Circ
/-- The actual (non-idealized) attitude of an agent to an act at a world. -/
axiom attitudeAt : World → Agent → Act → Prop
/-- The idealized reaction of an agent to an act at a world (Definition 3.3,
relativized to worlds). -/
axiom disapprovesAt : World → Agent → Act → Prop

/-- Definition 3.5, relativized to worlds. -/
def WrongAt (w : World) (a : Act) : Prop := ∀ i, disapprovesAt w i a

/-- Assumption 6.1 (dependence). An agent's idealized reaction to an act
depends only on the agent's nature and the act's natural circumstances. -/
axiom assumption_6_1 : ∀ w v i a, natureAt w i = natureAt v i →
  circAt w a = circAt v a → (disapprovesAt w i a ↔ disapprovesAt v i a)

/-- Theorem 6.2 (supervenience). Worlds alike in the natures of agents and in
the natural circumstances of an act are alike in whether it is wrong. -/
theorem supervenience (w v : World) (a : Act)
    (hn : ∀ i, natureAt w i = natureAt v i) (hc : circAt w a = circAt v a) :
    WrongAt w a ↔ WrongAt v a :=
  ⟨fun h i => (assumption_6_1 w v i a (hn i) hc).mp (h i),
   fun h i => (assumption_6_1 w v i a (hn i) hc).mpr (h i)⟩

/-- Corollary 6.3 (attitude-independence). However the actual attitudes of
agents differ between two worlds, if natures and circumstances agree, the
moral facts agree. -/
theorem attitude_independence (w v : World) (a : Act)
    (_hatt : ¬ (∀ i b, attitudeAt w i b ↔ attitudeAt v i b))
    (hn : ∀ i, natureAt w i = natureAt v i) (hc : circAt w a = circAt v a) :
    WrongAt w a ↔ WrongAt v a :=
  supervenience w v a hn hc

end Philosophy.MTE_01

#print axioms Philosophy.MTE_01.identification
#print axioms Philosophy.MTE_01.realism
#print axioms Philosophy.MTE_01.oqa_invalid
#print axioms Philosophy.MTE_01.p2_false
#print axioms Philosophy.MTE_01.attitude_independence
