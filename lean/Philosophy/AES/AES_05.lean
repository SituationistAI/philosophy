/-
AES-05 · Quasi-Emotions and the Paradox of Fiction
Formalization of Proposition 3.1, Theorem 3.4 and Corollary 3.5.

What this file establishes. (1) The three claims of the paradox of fiction,
that appreciators fear objects they know to be fictional (R), that fear
requires belief that its object exists and threatens (B), and that one who
knows an object to be fictional does not believe this (D), are jointly
inconsistent (Proposition 3.1; a theorem of pure logic, stated for
arbitrary predicates). (2) Given (B) as Principle P1, (D) as Principle P2,
and the observation that appreciators show the physiological profile of
fear (Assumption 2.3), an appreciator who knows the object to be fictional
quasi-fears it and does not fear it (Theorem 3.4). (3) Given that protective
motivation depends on belief in a threat (Assumption 2.4), quasi-fear of a
known fiction motivates no protective action (Corollary 3.5).

What it does not establish. Which member of the triad to reject. Logic
leaves the choice open; the arguments against rejecting (B) or (D)
(Lemmas 3.2 and 3.3) are philosophical and are not formalized.
-/

namespace Philosophy.AES_05

/-- Proposition 3.1. The triad is inconsistent: if fear requires belief in
a threat (B) and knowing an object to be fictional excludes that belief (D),
no one fears an object she knows to be fictional, so (R) fails. -/
theorem triad_inconsistent {S O : Type}
    (Fears Believes KnowsFictional : S → O → Prop)
    (hB : ∀ x o, Fears x o → Believes x o)
    (hD : ∀ x o, KnowsFictional x o → ¬ Believes x o) :
    ¬ ∃ x o, KnowsFictional x o ∧ Fears x o :=
  fun ⟨x, o, hk, hf⟩ => hD x o hk (hB x o hf)

/-- Appreciators. -/
axiom Subject : Type

/-- Objects of emotional response, fictional or real. -/
axiom Object : Type

/-- `Fears x o`: `x` fears `o`. -/
axiom Fears : Subject → Object → Prop

/-- `BelievesThreat x o`: `x` believes that `o` exists and threatens. -/
axiom BelievesThreat : Subject → Object → Prop

/-- `KnowsFictional x o`: `x` knows that `o` is fictional. -/
axiom KnowsFictional : Subject → Object → Prop

/-- Definition 2.1. `x` exhibits the physiological profile of fear directed
at `o`. -/
axiom FearProfile : Subject → Object → Prop

/-- `ProtectiveMotive x o`: `x` is motivated to protective action (flight,
warning, defence) with respect to `o`. -/
axiom ProtectiveMotive : Subject → Object → Prop

/-- Principle P1 (belief condition). Fear requires the belief that its
object exists and threatens. -/
axiom belief_condition : ∀ x o, Fears x o → BelievesThreat x o

/-- Principle P2 (disbelief). One who knows an object to be fictional does
not believe that it exists and threatens. -/
axiom disbelief : ∀ x o, KnowsFictional x o → ¬ BelievesThreat x o

/-- Definition 2.2. Quasi-fear: the physiological profile of fear without
the belief that fear requires. -/
def QuasiFears (x : Subject) (o : Object) : Prop :=
  FearProfile x o ∧ ¬ BelievesThreat x o

/-- Assumption 2.4 (motivational dependence). Protective motivation toward
an object requires the belief that it exists and threatens. -/
axiom motivation_needs_belief :
  ∀ x o, ProtectiveMotive x o → BelievesThreat x o

/-- Theorem 3.4 (resolution). An appreciator who knows `o` to be fictional
and exhibits the profile of fear toward it (Assumption 2.3, as hypothesis)
quasi-fears `o` and does not fear it. -/
theorem resolution (x : Subject) (o : Object)
    (hk : KnowsFictional x o) (hp : FearProfile x o) :
    QuasiFears x o ∧ ¬ Fears x o :=
  ⟨⟨hp, disbelief x o hk⟩,
   fun hf => disbelief x o hk (belief_condition x o hf)⟩

/-- Corollary 3.5 (boundedness). Quasi-fear of a known fiction motivates no
protective action toward it. -/
theorem no_protective_motive (x : Subject) (o : Object)
    (hk : KnowsFictional x o) : ¬ ProtectiveMotive x o :=
  fun hm => disbelief x o hk (motivation_needs_belief x o hm)

end Philosophy.AES_05

#print axioms Philosophy.AES_05.triad_inconsistent
#print axioms Philosophy.AES_05.resolution
#print axioms Philosophy.AES_05.no_protective_motive
