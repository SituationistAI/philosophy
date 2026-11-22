/-
PHE-18 · Philosophy as Rigorous Science, Circularly Grounded
Formalization of Theorem 3.1, Lemma 3.2, Proposition 3.3, Theorem 3.4 and
Proposition 3.5.

What this file establishes. With rigour defined phenomenologically
(Definition 2.3: every claim a discipline asserts is evident and
re-verifiable), and given that the definition is itself a phenomenological
claim (Assumption 2.4), that phenomenology's claims are evident and
re-verifiable (Assumption 2.5) and that some discipline asserts a
non-evident claim (Assumption 2.6): phenomenology is rigorous, its rigour
depends on the evidence of its own definition of rigour, the definition
discriminates, and the resulting circle is virtuous in the sense of
Definition 2.7. It also shows that the rival definition "rigorous = agrees
with phenomenology" is satisfied by phenomenology with no premise at all
(Proposition 3.5), which is the mark of a vicious circle.

What it does not establish. It does not establish Assumptions 2.4-2.6, in
particular that phenomenological claims are in fact evident; nor that the
phenomenological definition of rigour is the correct one.
-/

namespace Philosophy.PHE_18

/-- Disciplines. -/
axiom Discipline : Type
/-- Claims. -/
axiom Claim : Type
/-- `Asserts d c`: discipline `d` asserts claim `c`. -/
axiom Asserts : Discipline → Claim → Prop

/-- Definition 2.1. `Evident c`: `c` is given in a fulfilling intuition. -/
axiom Evident : Claim → Prop

/-- Definition 2.2. `ReVerifiable c`: the evidence of `c` can be regained on
re-entering the reflective attitude. -/
axiom ReVerifiable : Claim → Prop

/-- Definition 2.3. A discipline is rigorous if every claim it asserts is
evident and re-verifiable. -/
def Rigorous (d : Discipline) : Prop :=
  ∀ c, Asserts d c → Evident c ∧ ReVerifiable c

/-- Phenomenology. -/
axiom phen : Discipline
/-- The claim stated in Definition 2.3. -/
axiom rigourDef : Claim

/-- Assumption 2.4. The definition of rigour is a phenomenological claim. -/
axiom def_is_phen : Asserts phen rigourDef

/-- Assumption 2.5. Every claim phenomenology asserts is evident and
re-verifiable. -/
axiom phen_evident : ∀ c, Asserts phen c → Evident c ∧ ReVerifiable c

/-- Assumption 2.6. Some discipline asserts a claim that is not evident. -/
axiom discriminating : ∃ d c, Asserts d c ∧ ¬ Evident c

/-- Theorem 3.1. Phenomenology is rigorous. -/
theorem phen_rigorous : Rigorous phen := phen_evident

/-- Lemma 3.2 (the self-application is a test). If the definition of rigour
were not evident, phenomenology would not be rigorous. -/
theorem self_test : ¬ Evident rigourDef → ¬ Rigorous phen :=
  fun hne hr => hne (hr rigourDef def_is_phen).1

/-- Proposition 3.3. Not every discipline is rigorous. -/
theorem not_all_rigorous : ∃ d, ¬ Rigorous d :=
  match discriminating with
  | ⟨d, c, ha, hne⟩ => ⟨d, fun hr => hne (hr c ha).1⟩

/-- Definition 2.7. A discipline `p` that asserts a definition `δ` of a
property `R` stands in a virtuous circle if `p` has `R`, `R` discriminates,
and `p`'s having `R` would fail were `δ` not evident. -/
def VirtuousCircle (R : Discipline → Prop) (p : Discipline) (δ : Claim) : Prop :=
  Asserts p δ ∧ R p ∧ (∃ d, ¬ R d) ∧ (¬ Evident δ → ¬ R p)

/-- Theorem 3.4 (main result). Phenomenology, with its definition of rigour,
stands in a virtuous circle. -/
theorem virtuous : VirtuousCircle Rigorous phen rigourDef :=
  ⟨def_is_phen, phen_rigorous, not_all_rigorous, self_test⟩

/-- Proposition 3.5 (a vicious alternative). If rigour is defined as
asserting only what phenomenology asserts, phenomenology is rigorous with no
premise at all: the self-application can never fail. -/
def RigorousByFiat (d : Discipline) : Prop := ∀ c, Asserts d c → Asserts phen c

theorem by_fiat_trivial : RigorousByFiat phen := fun _ h => h

end Philosophy.PHE_18

#print axioms Philosophy.PHE_18.virtuous
#print axioms Philosophy.PHE_18.by_fiat_trivial
