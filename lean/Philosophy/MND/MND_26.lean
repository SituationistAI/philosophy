/-
MND-26 · The Mind-Body Problem: A Synthesis
Formalization of Theorem 3.1 of MND-26-a.

What this file establishes. Given the results of MND-01 to MND-25, taken as
atomic propositions (Assumption 2.3, clauses (a)-(g)), the mind-body problem
is solved in outline in the sense of Definition 2.2: each of the seven
component questions of Definition 2.1 has the answer those results give
(Theorem 3.1). The proposition `Details`, standing for the detailed account
of grounding deferred to MND-01, is declared and not assumed; that the main
theorem does not depend on it is the formal content of Corollary 3.2.

What it does not establish. It does not establish any family result, and it
does not check the consistency of the results, which depends on their
content and is argued in the proof of Theorem 3.1 in prose.
-/

namespace Philosophy.MND_26


/-- Result of MND-01: consciousness is the intrinsic nature of physical structure; the gap is between modes of presentation. -/
axiom R01 : Prop

/-- Result of MND-02: physicalism is true (current physics and foreseeable extensions). -/
axiom R02 : Prop

/-- Result of MND-03: bat experience is largely, not wholly, structurally specifiable. -/
axiom R03 : Prop

/-- Result of MND-04: Mary learns no new fact. -/
axiom R04 : Prop

/-- Result of MND-05: zombies are conceivable but impossible. -/
axiom R05 : Prop

/-- Result of MND-06: other minds are known by inference to the best explanation. -/
axiom R06 : Prop

/-- Result of MND-07: the system in the Chinese Room understands. -/
axiom R07 : Prop

/-- Result of MND-08: thinking is a functional property machines can have. -/
axiom R08 : Prop

/-- Result of MND-09: cognition extends into reliably coupled resources. -/
axiom R09 : Prop

/-- Result of MND-10: qualia exist and are intrinsic, with relational structure. -/
axiom R10 : Prop

/-- Result of MND-11: mental causes are proportional causes. -/
axiom R11 : Prop

/-- Result of MND-12: aboutness is primitive; teleosemantics explains its distribution. -/
axiom R12 : Prop

/-- Result of MND-13: beliefs exist. -/
axiom R13 : Prop

/-- Result of MND-14: higher-order theories of consciousness fail. -/
axiom R14 : Prop

/-- Result of MND-15: consciousness is unified; split-brain cases show partial unity. -/
axiom R15 : Prop

/-- Result of MND-16: perception is direct. -/
axiom R16 : Prop

/-- Result of MND-17: emotions represent evaluative properties. -/
axiom R17 : Prop

/-- Result of MND-18: panpsychism is false; intrinsic natures are protophenomenal. -/
axiom R18 : Prop

/-- Result of MND-19: there is cognitive phenomenology. -/
axiom R19 : Prop

/-- Result of MND-20: introspection is reliable about current phenomenal states only. -/
axiom R20 : Prop

/-- Result of MND-21: the mind computes but is not a single computer. -/
axiom R21 : Prop

/-- Result of MND-22: inverted spectrum possible, undetectable, no consequence for functionalism. -/
axiom R22 : Prop

/-- Result of MND-23: mammals and birds conscious, cephalopods probably, insects undetermined. -/
axiom R23 : Prop

/-- Result of MND-24: consciousness extends beyond attention. -/
axiom R24 : Prop

/-- Result of MND-25: dreams are conscious experiences. -/
axiom R25 : Prop

/-- Assumption 2.3(a): the result of MND-01 holds. -/
axiom r01 : R01

/-- Assumption 2.3(a): the result of MND-02 holds. -/
axiom r02 : R02

/-- Assumption 2.3(f): the result of MND-03 holds. -/
axiom r03 : R03

/-- Assumption 2.3(b): the result of MND-04 holds. -/
axiom r04 : R04

/-- Assumption 2.3(b): the result of MND-05 holds. -/
axiom r05 : R05

/-- Assumption 2.3(g): the result of MND-06 holds. -/
axiom r06 : R06

/-- Assumption 2.3(e): the result of MND-07 holds. -/
axiom r07 : R07

/-- Assumption 2.3(e): the result of MND-08 holds. -/
axiom r08 : R08

/-- Assumption 2.3(e): the result of MND-09 holds. -/
axiom r09 : R09

/-- Assumption 2.3(f): the result of MND-10 holds. -/
axiom r10 : R10

/-- Assumption 2.3(c): the result of MND-11 holds. -/
axiom r11 : R11

/-- Assumption 2.3(d): the result of MND-12 holds. -/
axiom r12 : R12

/-- Assumption 2.3(d): the result of MND-13 holds. -/
axiom r13 : R13

/-- Assumption 2.3(f): the result of MND-14 holds. -/
axiom r14 : R14

/-- Assumption 2.3(f): the result of MND-15 holds. -/
axiom r15 : R15

/-- Assumption 2.3(f): the result of MND-16 holds. -/
axiom r16 : R16

/-- Assumption 2.3(d): the result of MND-17 holds. -/
axiom r17 : R17

/-- Assumption 2.3(a): the result of MND-18 holds. -/
axiom r18 : R18

/-- Assumption 2.3(f): the result of MND-19 holds. -/
axiom r19 : R19

/-- Assumption 2.3(f): the result of MND-20 holds. -/
axiom r20 : R20

/-- Assumption 2.3(e): the result of MND-21 holds. -/
axiom r21 : R21

/-- Assumption 2.3(f): the result of MND-22 holds. -/
axiom r22 : R22

/-- Assumption 2.3(g): the result of MND-23 holds. -/
axiom r23 : R23

/-- Assumption 2.3(f): the result of MND-24 holds. -/
axiom r24 : R24

/-- Assumption 2.3(f): the result of MND-25 holds. -/
axiom r25 : R25

/-- The detailed account of grounding, deferred to MND-01 (Definition 2.2). Not assumed. -/
axiom Details : Prop

/-- Definition 2.1, Q1: the answer given by the results listed for it. -/
def Ontology : Prop := R02 ∧ R01 ∧ R18

/-- Definition 2.1, Q2: the answer given by the results listed for it. -/
def Gap : Prop := R04 ∧ R05

/-- Definition 2.1, Q3: the answer given by the results listed for it. -/
def Causation : Prop := R11

/-- Definition 2.1, Q4: the answer given by the results listed for it. -/
def Content : Prop := R12 ∧ R13 ∧ R17

/-- Definition 2.1, Q5: the answer given by the results listed for it. -/
def Organization : Prop := R08 ∧ R07 ∧ R21 ∧ R09

/-- Definition 2.1, Q6: the answer given by the results listed for it. -/
def Consciousness : Prop := R10 ∧ R22 ∧ R03 ∧ R14 ∧ R15 ∧ R16 ∧ R19 ∧ R20 ∧ R24 ∧ R25

/-- Definition 2.1, Q7: the answer given by the results listed for it. -/
def OtherMinds : Prop := R06 ∧ R23

/-- Definition 2.2. Solved in outline: every component question answered. -/
def SolvedInOutline : Prop :=
  Ontology ∧ Gap ∧ Causation ∧ Content ∧ Organization ∧ Consciousness ∧ OtherMinds

/-- Theorem 3.1. The mind-body problem is solved in outline. -/
theorem theorem_3_1 : SolvedInOutline :=
  ⟨⟨r02, r01, r18⟩, ⟨r04, r05⟩, r11, ⟨r12, r13, r17⟩, ⟨r08, r07, r21, r09⟩, ⟨r10, r22, r03, r14, r15, r16, r19, r20, r24, r25⟩, ⟨r06, r23⟩⟩

end Philosophy.MND_26

#print axioms Philosophy.MND_26.theorem_3_1
