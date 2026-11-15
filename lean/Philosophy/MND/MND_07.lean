/-
MND-07 · The Systems Reply Vindicated
Formalization of Theorem 4.2.

What this file establishes. Under the functionalist premise (Assumption 4.1)
and the description of the case, the room system understands Chinese. The
derivation does not use the man's lack of understanding, which is stated as
an axiom and is consistent with the conclusion. The file does not establish
the functionalist premise, which is what Searle denies.
-/

namespace Philosophy.MND_07

/-- Entities: agents, systems and their components. -/
axiom Entity : Type

/-- Programs. -/
axiom Program : Type

/-- Definition 2.1: `Executes x p`, `x` carries out the operations of `p`. -/
axiom Executes : Entity → Program → Prop

/-- Definition 2.2: `Runs x p`, the states of `x` realize the functional
organization of `p`. -/
axiom Runs : Entity → Program → Prop

/-- `CompetentSpeaker p`: `p` realizes the functional organization of a
competent speaker of Chinese. -/
axiom CompetentSpeaker : Program → Prop

/-- Understanding Chinese. -/
axiom Understands : Entity → Prop

/-- The man and the room system. -/
axiom man : Entity
axiom room : Entity

/-- The rule book. -/
axiom chineseProgram : Program

/-- The case: the rule book realizes a competent speaker. -/
axiom competent : CompetentSpeaker chineseProgram

/-- The case: the man executes the program. -/
axiom man_executes : Executes man chineseProgram

/-- The case: the room system runs the program (Section 2). -/
axiom room_runs : Runs room chineseProgram

/-- The case, premise (S2): the man does not understand Chinese. -/
axiom man_does_not_understand : ¬ Understands man

/-- Assumption 4.1 (functionalism about understanding). -/
axiom functionalism :
  ∀ x p, CompetentSpeaker p → Runs x p → Understands x

/-- Theorem 4.2. The room system understands Chinese. -/
theorem system_understands : Understands room :=
  functionalism room chineseProgram competent room_runs

/-- Proposition 3.1 (formal part). Searle's conclusion about the system
follows from the man's lack of understanding only with the downward transfer
principle (Principle P1); with that principle and the axioms above, the
theory is inconsistent. -/
theorem transfer_inconsistent
    (transfer : ∀ x y p, Executes x p → Runs y p → ¬ Understands x → ¬ Understands y) :
    False :=
  transfer man room chineseProgram man_executes room_runs man_does_not_understand
    system_understands

end Philosophy.MND_07

#print axioms Philosophy.MND_07.system_understands
#print axioms Philosophy.MND_07.transfer_inconsistent
