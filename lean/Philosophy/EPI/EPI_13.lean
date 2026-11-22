/-
EPI-13 · Contextualism and Scepticism
Formalization of Lemmas 3.1 and 3.2, Theorems 3.3 and 3.5 and Corollaries
3.4 and 3.6.

Knowledge is justified safe belief (EPI-01), and the closeness relation on
which safety depends is indexed to contexts of attribution (Definitions 2.1
and 2.3). Belief, justification and truth are not indexed to contexts.

What this file establishes. Knowledge is factive (Lemma 3.1) and closed (Lemma 3.2) within each context.
Given Moore's situation (Assumption 2.8), the rule of attention (Assumption
2.9), the inattention premise (Assumption 2.10) and the raising of
hypotheses (Assumption 2.11), the subject knows that she has hands by the
standards of the ordinary context and fails to know it by the standards of
the context created by raising a sceptical hypothesis (Theorem 3.3), so that
"know" is context-sensitive in the sense of Definition 2.4 (Corollary 3.4).
In every context, she fails to know that she has hands exactly when some
sceptical hypothesis is attended to (Theorem 3.5); a sceptical argument is
sound in a context only if that context attends to a sceptical hypothesis,
and it is sound in the context its own first premise creates (Corollary 3.6).

What it does not establish. The inattention premise, which is a contingent
claim about the actual world; that attention is the only mechanism by which
standards rise; or anything about the linguistic mechanism of the shift.
-/

namespace Philosophy.EPI_13

/-- Possible worlds. -/
axiom World : Type
/-- Bases on which beliefs are held. -/
axiom Basis : Type
/-- Contexts of attribution. -/
axiom Context : Type

/-- Propositions as sets of worlds. -/
abbrev Proposition := World → Prop

/-- Definition 2.1 (contextual closeness). `Close c w v`: by the standards of
`c`, `v` is close to `w`. -/
axiom Close : Context → World → World → Prop
/-- `Believes p m w`: at `w` the subject believes `p` on basis `m`. -/
axiom Believes : Proposition → Basis → World → Prop
/-- `Justified p m w`: at `w` the subject is justified in believing `p` on `m`.
Not indexed to contexts. -/
axiom Justified : Proposition → Basis → World → Prop

/-- Assumption 2.2 (centring). -/
axiom centring : ∀ c w, Close c w w

/-- Definition 2.3 (safety in a context). -/
def Safe (c : Context) (p : Proposition) (m : Basis) (w : World) : Prop :=
  ∀ v, Close c w v → Believes p m v → p v

/-- Definition 2.3 (knowledge in a context). -/
def Knows (c : Context) (p : Proposition) (w : World) : Prop :=
  ∃ m, Believes p m w ∧ Justified p m w ∧ Safe c p m w

/-- Definition 2.4 (context-sensitivity of "know"). -/
def ContextSensitive : Prop :=
  ∃ (c c' : Context) (p : Proposition) (w : World), Knows c p w ∧ ¬ Knows c' p w

/-- Competent deduction of `q` on `m'` from the belief in `p` on `m`. -/
def Deduces (p : Proposition) (m : Basis) (q : Proposition) (m' : Basis) : Prop :=
  (∀ v, p v → q v) ∧ (∀ v, Believes q m' v → Believes p m v)

/-- Assumption 2.5 (justification is closed under competent deduction). -/
axiom justification_closure :
  ∀ (p q : Proposition) (m m' : Basis) (w : World),
    Justified p m w → Deduces p m q m' → Believes q m' w → Justified q m' w

/-- Lemma 3.1 (factivity in every context). -/
theorem factive {c : Context} {p : Proposition} {w : World} (h : Knows c p w) : p w := by
  obtain ⟨m, hb, _, hs⟩ := h
  exact hs w (centring c w) hb

/-- Lemma 3.2 (closure within each context). -/
theorem closure {c : Context} {p q : Proposition} {m m' : Basis} {w : World}
    (hj : Justified p m w) (hs : Safe c p m w)
    (hd : Deduces p m q m') (hq : Believes q m' w) : Knows c q w :=
  ⟨m', hq, justification_closure p q m m' w hj hd hq,
    fun v hc hbv => hd.1 v (hs v hc (hd.2 v hbv))⟩

/-- `Hands`: the subject has hands. -/
axiom Hands : Proposition

/-- Envatted counterparts: `counterpart X w m` is an `X`-world at which the
subject believes on `m` whatever she believes on `m` at `w`. -/
axiom counterpart : Proposition → World → Basis → World

/-- Definition 2.6 (sceptical hypothesis for `Hands`). `X` entails that the
subject lacks hands, and every world and basis has an `X`-counterpart. -/
def Sceptical (X : Proposition) : Prop :=
  (∀ v, X v → ¬ Hands v) ∧
  (∀ w m, X (counterpart X w m)) ∧
  (∀ w m (p : Proposition), Believes p m w → Believes p m (counterpart X w m))

/-- Definition 2.7 (attention). `Attends c X`: in `c`, the hypothesis `X` is
attended to as a possibility to be ruled out. -/
axiom Attends : Context → Proposition → Prop

/-- The actual world, the basis of perception, and the deductive bases. -/
axiom actual : World
axiom perception : Basis
axiom deduction : Proposition → Basis

/-- Assumption 2.8 (Moore's situation): belief in `Hands` by perception. -/
axiom believes_hands : Believes Hands perception actual
/-- Assumption 2.8: justified (EPI-19). -/
axiom justified_hands : Justified Hands perception actual
/-- Assumption 2.8: the denial of each hypothesis is believed by deduction. -/
axiom believes_denial : ∀ X : Proposition, Believes (fun v => ¬ X v) (deduction X) actual
/-- Assumption 2.8: the deductive basis depends on the perceptual belief. -/
axiom deduced_denial :
  ∀ (X : Proposition) v, Believes (fun v => ¬ X v) (deduction X) v →
    Believes Hands perception v

/-- Assumption 2.9 (rule of attention). A context that attends to a sceptical
hypothesis counts the hypothesis's counterparts as close. -/
axiom attention :
  ∀ c X w m, Sceptical X → Attends c X → Close c w (counterpart X w m)

/-- Assumption 2.10 (inattention). In a context that attends to no sceptical
hypothesis, the perceptual belief that one has hands is safe at the actual
world. -/
axiom inattention :
  ∀ c, (∀ X, Sceptical X → ¬ Attends c X) → Safe c Hands perception actual

/-- Assumption 2.11 (raising). Asserting the first premise of the sceptical
argument for `X` in `c` produces a context that attends to `X`. -/
axiom raise : Context → Proposition → Context
axiom raise_attends : ∀ c X, Attends (raise c X) X

/-- The ordinary context attends to no sceptical hypothesis. -/
axiom ordinary : Context
axiom ordinary_inattentive : ∀ X, Sceptical X → ¬ Attends ordinary X

/-- Knowledge of the denial of a hypothesis, by deduction, in a context in
which the perceptual belief is safe. -/
theorem knows_denial {c : Context} (X : Proposition) (hX : Sceptical X)
    (hs : Safe c Hands perception actual) : Knows c (fun v => ¬ X v) actual :=
  closure justified_hands hs
    ⟨fun v h hv => hX.1 v hv h, deduced_denial X⟩ (believes_denial X)

/-- In a context attending to `X`, no belief that is false at every
`X`-world is safe, on any basis. -/
theorem attended_unsafe {c : Context} {X : Proposition} (hX : Sceptical X)
    (ha : Attends c X) (p : Proposition) (hp : ∀ v, X v → ¬ p v) (w : World) :
    ¬ Knows c p w := by
  intro ⟨m, hb, _, hs⟩
  exact hp _ (hX.2.1 w m)
    (hs (counterpart X w m) (attention c X w m hX ha) (hX.2.2 w m p hb))

/-- Theorem 3.3 (shift). For any sceptical hypothesis `X`, the subject knows
that she has hands in the ordinary context and does not know it in the
context created by raising `X`. -/
theorem shift (X : Proposition) (hX : Sceptical X) :
    Knows ordinary Hands actual ∧ ¬ Knows (raise ordinary X) Hands actual :=
  ⟨⟨perception, believes_hands, justified_hands,
      inattention ordinary ordinary_inattentive⟩,
    attended_unsafe hX (raise_attends ordinary X) Hands hX.1 actual⟩

/-- Corollary 3.4. If there is a sceptical hypothesis, "know" is
context-sensitive. -/
theorem context_sensitive (h : ∃ X, Sceptical X) : ContextSensitive := by
  obtain ⟨X, hX⟩ := h
  exact ⟨ordinary, raise ordinary X, Hands, actual, shift X hX⟩

/-- Theorem 3.5 (characterization). In every context, the subject fails to
know that she has hands exactly when the context attends to some sceptical
hypothesis. -/
theorem characterization (c : Context) :
    ¬ Knows c Hands actual ↔ ∃ X, Sceptical X ∧ Attends c X := by
  constructor
  · intro hn
    apply Classical.byContradiction
    intro hno
    apply hn
    refine ⟨perception, believes_hands, justified_hands, inattention c ?_⟩
    intro X hX ha
    exact hno ⟨X, hX, ha⟩
  · intro ⟨X, hX, ha⟩
    exact attended_unsafe hX ha Hands hX.1 actual

/-- The sceptical argument from `X`, evaluated in context `c`: its first
premise, its closure premise and its conclusion are all true. -/
def Sound (c : Context) (X : Proposition) : Prop :=
  ¬ Knows c (fun v => ¬ X v) actual ∧
  (Knows c Hands actual → Knows c (fun v => ¬ X v) actual) ∧
  ¬ Knows c Hands actual

/-- Corollary 3.6 (the sceptic's success is self-created). The sceptical
argument from `X` is sound in a context only if that context attends to some
sceptical hypothesis; it is sound in the context created by raising `X`; and
it is unsound in the ordinary context, where its first premise is false. -/
theorem self_created (X : Proposition) (hX : Sceptical X) :
    (∀ c, Sound c X → ∃ Y, Sceptical Y ∧ Attends c Y) ∧
    (∀ c, Sound (raise c X) X) ∧
    Knows ordinary (fun v => ¬ X v) actual := by
  refine ⟨fun c hs => (characterization c).1 hs.2.2, fun c => ?_, ?_⟩
  · have hnot : ¬ Knows (raise c X) (fun v => ¬ X v) actual :=
      attended_unsafe hX (raise_attends c X) _ (fun v hv h => h hv) actual
    exact ⟨hnot, fun hk => absurd hk
        (attended_unsafe hX (raise_attends c X) Hands hX.1 actual),
      attended_unsafe hX (raise_attends c X) Hands hX.1 actual⟩
  · exact knows_denial X hX (inattention ordinary ordinary_inattentive)

end Philosophy.EPI_13

#print axioms Philosophy.EPI_13.shift
#print axioms Philosophy.EPI_13.characterization
#print axioms Philosophy.EPI_13.self_created
