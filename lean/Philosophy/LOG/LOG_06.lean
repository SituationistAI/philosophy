/-
LOG-06 · Logical Consequence and the Actual World
Formalization of Theorem 4.1, Corollary 4.2, Propositions 4.3 and 4.4 and
Theorem 4.5.

Models, sentences and satisfaction are primitives (Definition 3.1).
Satisfaction is invariant under isomorphism (Assumption 3.2). Each world
has a structure, and truth at a world is satisfaction in that structure
(Definition 3.3). An argument is valid relative to a class of models if
every model in the class that satisfies the premises satisfies the
conclusion (Definition 3.4). A class is anchored if it contains a model
isomorphic to the structure of the actual world, and modally anchored if
it contains one isomorphic to the structure of each world (Definition 3.5).

What this file establishes. Validity relative to an anchored class
guarantees actual truth-preservation, and validity relative to a modally
anchored class guarantees necessary truth-preservation. Validity is
antitone in the class. Without the anchoring proviso, validity can
overgenerate: for every finite size of the actual domain there is a class of
models, all smaller, relative to which a sentence false at the actual world
is valid. Finally, if derivability is sound for intuitive validity,
intuitive validity entails validity relative to a class, and that class is
complete for derivability, the three notions coincide (Kreisel).

What it does not establish. It does not establish isomorphism invariance
for any particular language, the existence of a model isomorphic to the
actual world (Section 6 of the manuscript), or the completeness premise of
Theorem 4.5, which holds for first-order logic (Gödel) and fails for
second-order logic.
-/

namespace Philosophy.LOG_06

/-- Definition 3.1. Models (primitive). -/
axiom Model : Type
/-- Definition 3.1. Sentences (primitive). -/
axiom Sentence : Type
/-- Definition 3.1. Satisfaction (primitive). -/
axiom Sat : Model → Sentence → Prop
/-- Definition 3.1. Isomorphism between models (primitive). -/
axiom Iso : Model → Model → Prop

/-- Assumption 3.2 (isomorphism invariance). Isomorphic models satisfy the
same sentences. -/
axiom iso_invariance : ∀ M N A, Iso M N → (Sat M A ↔ Sat N A)

/-- Definition 3.3. Possible worlds (primitive). -/
axiom World : Type
/-- Definition 3.3. The structure of a world: its domain, with the
extensions the non-logical vocabulary has there. -/
axiom structureOf : World → Model
/-- Definition 3.3. The actual world. -/
axiom actual : World

/-- Definition 3.3. Truth at a world is satisfaction in its structure. -/
def TrueAt (w : World) (A : Sentence) : Prop := Sat (structureOf w) A

/-- Definition 3.4. Validity relative to a class of models. -/
def ValidIn (K : Model → Prop) (G : Sentence → Prop) (A : Sentence) : Prop :=
  ∀ M, K M → (∀ B, G B → Sat M B) → Sat M A

/-- Truth-preservation at a world. -/
def PreservesAt (w : World) (G : Sentence → Prop) (A : Sentence) : Prop :=
  (∀ B, G B → TrueAt w B) → TrueAt w A

/-- Definition 3.5. A class is anchored if it contains a model isomorphic
to the structure of the actual world. -/
def Anchored (K : Model → Prop) : Prop :=
  ∃ M, K M ∧ Iso M (structureOf actual)

/-- Definition 3.5. A class is modally anchored if it contains a model
isomorphic to the structure of each world. -/
def ModallyAnchored (K : Model → Prop) : Prop :=
  ∀ w, ∃ M, K M ∧ Iso M (structureOf w)

/-- Theorem 4.1 (reliability). Validity relative to an anchored class
guarantees actual truth-preservation. -/
theorem reliability (K : Model → Prop) (hK : Anchored K)
    (G : Sentence → Prop) (A : Sentence) (hv : ValidIn K G A) :
    PreservesAt actual G A := by
  obtain ⟨M, hM, hiso⟩ := hK
  intro hprem
  have hsat : Sat M A :=
    hv M hM (fun B hB => (iso_invariance M _ B hiso).mpr (hprem B hB))
  exact (iso_invariance M _ A hiso).mp hsat

/-- Corollary 4.2 (necessity). Validity relative to a modally anchored
class guarantees truth-preservation at every world. -/
theorem necessity (K : Model → Prop) (hK : ModallyAnchored K)
    (G : Sentence → Prop) (A : Sentence) (hv : ValidIn K G A) :
    ∀ w, PreservesAt w G A := by
  intro w hprem
  obtain ⟨M, hM, hiso⟩ := hK w
  have hsat : Sat M A :=
    hv M hM (fun B hB => (iso_invariance M _ B hiso).mpr (hprem B hB))
  exact (iso_invariance M _ A hiso).mp hsat

/-- Proposition 4.3 (antitonicity). Enlarging the class of models can only
remove valid arguments. -/
theorem antitone (K K' : Model → Prop) (hsub : ∀ M, K M → K' M)
    (G : Sentence → Prop) (A : Sentence) (hv : ValidIn K' G A) :
    ValidIn K G A :=
  fun M hM hprem => hv M (hsub M hM) hprem

/-- Proposition 4.4 setting. A pure-identity language whose models are
finite domain sizes: `atLeast n` says that there are at least n things. -/
inductive CSentence where
  | atLeast : Nat → CSentence
  | neg : CSentence → CSentence

/-- Satisfaction in a domain of size m. -/
def csat (m : Nat) : CSentence → Prop
  | .atLeast n => n ≤ m
  | .neg A => ¬ csat m A

/-- Proposition 4.4 (overgeneration without the proviso). If the actual
domain has a finite size a, the class of all smaller domains makes valid
a sentence that is false at the actual world, and that class does not
contain the actual size. -/
theorem overgeneration (a : Nat) :
    ∃ K : Nat → Prop, ∃ A : CSentence,
      (∀ m, K m → csat m A) ∧ ¬ csat a A ∧ ¬ K a := by
  refine ⟨fun m => m < a, .neg (.atLeast a), ?_, ?_, ?_⟩
  · intro m hm
    simp only [csat]
    omega
  · simp [csat]
  · simp

/-- Proposition 4.4, second part. Adding the actual size to any class
blocks every such case. -/
theorem anchoring_blocks (a : Nat) (K : Nat → Prop) (hK : K a) (A : CSentence)
    (hv : ∀ m, K m → csat m A) : csat a A :=
  hv a hK

/-- Theorem 4.5 (squeezing). If derivability is sound for intuitive
validity, intuitive validity entails validity in the class, and validity in
the class entails derivability, the three relations coincide. -/
theorem squeeze (Der Int Val : (Sentence → Prop) → Sentence → Prop)
    (sound : ∀ G A, Der G A → Int G A)
    (adequate : ∀ G A, Int G A → Val G A)
    (complete : ∀ G A, Val G A → Der G A) :
    ∀ G A, (Int G A ↔ Val G A) ∧ (Int G A ↔ Der G A) := by
  intro G A
  exact ⟨⟨adequate G A, fun h => sound G A (complete G A h)⟩,
         ⟨fun h => complete G A (adequate G A h), sound G A⟩⟩

end Philosophy.LOG_06

#print axioms Philosophy.LOG_06.reliability
#print axioms Philosophy.LOG_06.necessity
#print axioms Philosophy.LOG_06.overgeneration
#print axioms Philosophy.LOG_06.squeeze
