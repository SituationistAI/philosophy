/-
SCI-02 · Scientific Realism Defended
Formalization of Lemma 4.1, Theorem 4.2, Proposition 4.3, Proposition 4.4
and Corollary 4.5.

Theories assert claims. A novel success of a theory is a phenomenon that
the theory predicted without having been built to accommodate it, and that
obtained (Definition 3.1). A claim is an essential posit of a theory if it
is used ineliminably in deriving one of the theory's novel successes
(Definition 3.2). A theory is approximately true if all its essential
posits are true (Definition 3.3), and mature if it has at least one novel
success (Definition 3.4). A theory is false if it asserts at least one
false claim.

What this file establishes. Given the no-miracles premise (Assumption 3.6)
and inference to the best explanation (Assumption 3.7), every mature theory
is approximately true and has true essential content (Theorem 4.2). The
historical premise of the pessimistic meta-induction, that a theory is
false, does not entail that it is not approximately true (Proposition 4.3,
proved without axioms by a two-claim model). If each theory in a sequence
retains the essential content of its predecessor (Definition 3.8),
approximate truth of a later theory transfers to every earlier one
(Proposition 4.4, Corollary 4.5).

What it does not establish. It does not establish Assumptions 3.5-3.7,
which are defended in the manuscript, nor that any particular theory has a
novel success, nor that the historical record satisfies the retention
condition; these are matters of argument and of the history of science.
-/

namespace Philosophy.SCI_02

/-- Theories. -/
axiom Theory : Type
/-- Claims (propositions a theory may assert). -/
axiom Claim : Type
/-- Phenomena (possible observable outcomes). -/
axiom Phenomenon : Type

/-- Truth of a claim. -/
axiom Tru : Claim → Prop
/-- `Asserts T c`: theory `T` asserts claim `c`. -/
axiom Asserts : Theory → Claim → Prop
/-- `Obtains p`: phenomenon `p` actually occurs. -/
axiom Obtains : Phenomenon → Prop
/-- Definition 3.1 (primitive). `NovelSuccess T p`: `T` predicted `p`,
`p` was not used in constructing `T`, and `p` obtained. -/
axiom NovelSuccess : Theory → Phenomenon → Prop
/-- `Uses T c p`: claim `c` is used ineliminably in the derivation of `p`
from `T`. -/
axiom Uses : Theory → Claim → Phenomenon → Prop
/-- `BestExplanation c p`: the truth of `c` is part of the best available
explanation of `p`. -/
axiom BestExplanation : Claim → Phenomenon → Prop

/-- Definition 3.1 (the success clause). A novel success obtains. -/
axiom success_obtains : ∀ T p, NovelSuccess T p → Obtains p

/-- Definition 3.2. Essential posits. -/
def Essential (T : Theory) (c : Claim) : Prop :=
  ∃ p, NovelSuccess T p ∧ Uses T c p

/-- Definition 3.3. Approximate truth: every essential posit is true. -/
def ApproxTrue (T : Theory) : Prop := ∀ c, Essential T c → Tru c

/-- Definition 3.4. Maturity: at least one novel success. -/
def Mature (T : Theory) : Prop := ∃ p, NovelSuccess T p

/-- A theory is false if it asserts a false claim. -/
def FalseTheory (T : Theory) : Prop := ∃ c, Asserts T c ∧ ¬ Tru c

/-- Assumption 3.5 (use), first clause. What a derivation from a theory
uses, the theory asserts. -/
axiom uses_asserted : ∀ T c p, Uses T c p → Asserts T c

/-- Assumption 3.5 (use), second clause. In the derivation of every novel
success, some claim of the theory is used ineliminably. -/
axiom success_uses : ∀ T p, NovelSuccess T p → ∃ c, Uses T c p

/-- Assumption 3.6 (no miracles). If a claim is used ineliminably in
deriving a novel success, its truth is part of the best explanation of
that success. -/
axiom no_miracles : ∀ T c p, NovelSuccess T p → Uses T c p → BestExplanation c p

/-- Assumption 3.7 (inference to the best explanation). What is part of
the best explanation of a phenomenon that obtains is true. -/
axiom ibe : ∀ c p, BestExplanation c p → Obtains p → Tru c

/-- Lemma 4.1. Every essential posit is true. -/
theorem essential_true (T : Theory) (c : Claim) (h : Essential T c) : Tru c := by
  obtain ⟨p, hs, hu⟩ := h
  exact ibe c p (no_miracles T c p hs hu) (success_obtains T p hs)

/-- Theorem 4.2 (realism). A mature theory is approximately true and has
true essential content. -/
theorem realism (T : Theory) (hm : Mature T) :
    ApproxTrue T ∧ ∃ c, Asserts T c ∧ Essential T c ∧ Tru c := by
  refine ⟨essential_true T, ?_⟩
  obtain ⟨p, hs⟩ := hm
  obtain ⟨c, hu⟩ := success_uses T p hs
  exact ⟨c, uses_asserted T c p hu, ⟨p, hs, hu⟩, essential_true T c ⟨p, hs, hu⟩⟩

/-- Proposition 4.3 (the meta-induction's premise does not yield its
conclusion). It is not the case that, for every way of assigning claims,
essential posits and truth values, a false theory fails to be
approximately true. Witness: a theory asserting a true essential claim
(transverse waves) and a false idle one (the elastic ether). -/
theorem pmi_invalid :
    ¬ ∀ (C : Type) (asserts essential tru : C → Prop),
        (∀ c, essential c → asserts c) →
        (∃ c, asserts c ∧ ¬ tru c) → ¬ ∀ c, essential c → tru c := by
  intro h
  exact h Bool (fun _ => True) (fun c => c = true) (fun c => c = true)
    (fun _ _ => trivial) ⟨false, trivial, by decide⟩ (fun _ hc => hc)

/-- Definition 3.8. `S` retains the essential content of `P` if every
essential posit of `P` is implied by the truth of some essential posit
of `S`. -/
def Retains (P S : Theory) : Prop :=
  ∀ c, Essential P c → ∃ d, Essential S d ∧ (Tru d → Tru c)

/-- Proposition 4.4. If `S` retains the essential content of `P` and `S` is
approximately true, so is `P`. -/
theorem retention_transfers (P S : Theory) (hr : Retains P S)
    (hs : ApproxTrue S) : ApproxTrue P := by
  intro c hc
  obtain ⟨d, hd, himp⟩ := hr c hc
  exact himp (hs d hd)

/-- Corollary 4.5. In a sequence of theories each of which retains the
essential content of its predecessor, approximate truth of a later theory
transfers to every earlier one. -/
theorem retention_chain (seq : Nat → Theory)
    (hr : ∀ n, Retains (seq n) (seq (n + 1))) :
    ∀ k n, ApproxTrue (seq (n + k)) → ApproxTrue (seq n) := by
  intro k
  induction k with
  | zero => intro n h; simpa using h
  | succ k ih =>
    intro n h
    apply ih n
    have h' : ApproxTrue (seq (n + k + 1)) := by
      simpa [Nat.add_assoc] using h
    exact retention_transfers _ _ (hr (n + k)) h'

end Philosophy.SCI_02

#print axioms Philosophy.SCI_02.realism
#print axioms Philosophy.SCI_02.pmi_invalid
#print axioms Philosophy.SCI_02.retention_chain
