/-
MTH-09 · What Is a Proof?
Formalization of Theorem 3.1, Corollary 3.2 and Propositions 3.3 and 3.4.

What this file establishes. With a proof defined as a derivation acceptable
to a competent community (Definition 2.4), and acceptability as
certification by a method the community is warranted in using
(Definition 2.3): every formally verified derivation is a proof, whether or
not it has been surveyed (Theorem 3.1, Corollary 3.2); every proof is valid
(Proposition 3.3); and if some verified derivation has not been surveyed,
surveyability is not a necessary condition of proof (Proposition 3.4).

What it does not establish. It does not establish the soundness of any
actual checking kernel (Assumption 2.6 is a premise, not a result), nor
anything about whether a proof explains its conclusion (MTH-08).
-/

namespace Philosophy.MTH_09

/-- Definition 2.1. Derivations: finite sequences of formulas, each an axiom
or obtained from earlier ones by a rule. -/
axiom Derivation : Type

/-- Definition 2.1. `Valid d`: every step of `d` is correct by the rules. -/
axiom Valid : Derivation → Prop

/-- Communities of mathematical practitioners. -/
axiom Community : Type

/-- Definition 2.2. `Competent c`: `c` is a competent community. -/
axiom Competent : Community → Prop

/-- Methods of checking derivations (surveying by a reader, checking by a
proof kernel, and others). -/
axiom Method : Type

/-- `Warranted c μ`: community `c` is warranted in relying on method `μ`. -/
axiom Warranted : Community → Method → Prop

/-- `Certifies μ d`: method `μ`, applied to `d`, certifies every step. -/
axiom Certifies : Method → Derivation → Prop

/-- The method of checking by a small proof-checking kernel. -/
axiom kernel : Method

/-- `Surveyed d`: some human reader has checked every step of `d`. -/
axiom Surveyed : Derivation → Prop

/-- Definition 2.3. `d` is acceptable to `c` if some method `c` is warranted
in using certifies `d`. -/
def Acceptable (c : Community) (d : Derivation) : Prop :=
  ∃ m, Warranted c m ∧ Certifies m d

/-- Definition 2.4. A proof is a derivation acceptable to a competent
community. -/
def Proof (d : Derivation) : Prop := ∃ c, Competent c ∧ Acceptable c d

/-- Assumption 2.5 (answerability). A method a competent community is
warranted in using certifies only valid derivations. -/
axiom warranted_sound :
  ∀ c μ d, Competent c → Warranted c μ → Certifies μ d → Valid d

/-- Assumption 2.6 (de Bruijn condition). Some competent community is
warranted in relying on the kernel. -/
axiom kernel_warranted : ∃ c, Competent c ∧ Warranted c kernel

/-- Definition 2.7. `d` is formally verified if the kernel certifies it. -/
def Verified (d : Derivation) : Prop := Certifies kernel d

/-- Theorem 3.1. Every formally verified derivation is a proof. -/
theorem verified_is_proof (d : Derivation) (h : Verified d) : Proof d :=
  match kernel_warranted with
  | ⟨c, hc, hw⟩ => ⟨c, hc, kernel, hw, h⟩

/-- Corollary 3.2. A formally verified derivation is a proof whether or not
it is surveyed. -/
theorem proof_without_survey (d : Derivation) (h : Verified d) :
    (Surveyed d → Proof d) ∧ (¬ Surveyed d → Proof d) :=
  ⟨fun _ => verified_is_proof d h, fun _ => verified_is_proof d h⟩

/-- Proposition 3.3. Every proof is valid. -/
theorem proof_valid (d : Derivation) (h : Proof d) : Valid d :=
  match h with
  | ⟨c, hc, m, hw, hcert⟩ => warranted_sound c m d hc hw hcert

/-- Proposition 3.4. If some formally verified derivation is unsurveyed,
not every proof is surveyed. -/
theorem survey_not_necessary
    (h : ∃ d, Verified d ∧ ¬ Surveyed d) : ¬ ∀ d, Proof d → Surveyed d :=
  fun hall => match h with
  | ⟨d, hv, hs⟩ => hs (hall d (verified_is_proof d hv))

end Philosophy.MTH_09

#print axioms Philosophy.MTH_09.proof_without_survey
#print axioms Philosophy.MTH_09.proof_valid
#print axioms Philosophy.MTH_09.survey_not_necessary
