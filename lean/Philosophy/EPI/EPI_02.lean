/-
EPI-02 · A Defence of Moore's Proof
Formalization of Proposition 3.1, Theorems 3.2 and 3.4 and Corollaries 3.3
and 3.5.

Knowledge is justified safe belief (EPI-01), with closeness indexed to
contexts of attribution (Definitions 2.1 and 2.3).

What this file establishes. In the ordinary context, given Moore's situation
(Assumption 2.5) and ordinary closeness (Assumption 2.6), the subject knows
that she has hands, that there are external things and that she is not a
handless brain in a vat (Theorem 3.2), so the sceptic's first premise is false
there while the closure premise is true (Corollary 3.3). In the sceptical
context, given envatted counterparts (Assumption 2.7) and attention
(Assumption 2.8), she knows neither (Theorem 3.4). The two results are
compatible (Corollary 3.5).

What it does not establish. Assumption 2.6, which is a contingent claim about
the actual world defended in Section 4 of the manuscript; nor that the
ordinary context is the one in which scepticism must be assessed.
-/

namespace Philosophy.EPI_02

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
/-- `Justified p m w`: at `w` the subject is justified in believing `p` on `m`. -/
axiom Justified : Proposition → Basis → World → Prop

/-- Assumption 2.2 (centring). -/
axiom centring : ∀ c w, Close c w w

/-- Definition 2.3 (safety in a context). -/
def Safe (c : Context) (p : Proposition) (m : Basis) (w : World) : Prop :=
  ∀ v, Close c w v → Believes p m v → p v

/-- Definition 2.3 (knowledge in a context). -/
def Knows (c : Context) (p : Proposition) (w : World) : Prop :=
  ∃ m, Believes p m w ∧ Justified p m w ∧ Safe c p m w

/-- `m'` is a basis of competent deduction of `q` from the belief in `p` on `m`. -/
def Deduces (p : Proposition) (m : Basis) (q : Proposition) (m' : Basis) : Prop :=
  (∀ v, p v → q v) ∧ (∀ v, Believes q m' v → Believes p m v)

/-- Assumption 2.4 (justification is closed under competent deduction). -/
axiom justification_closure :
  ∀ (p q : Proposition) (m m' : Basis) (w : World),
    Justified p m w → Deduces p m q m' → Believes q m' w → Justified q m' w

/-- Closure of knowledge in every context (EPI-20, Theorem 3.2, relativized). -/
theorem closure {c : Context} {p q : Proposition} {m m' : Basis} {w : World}
    (hj : Justified p m w) (hs : Safe c p m w)
    (hd : Deduces p m q m') (hq : Believes q m' w) : Knows c q w :=
  ⟨m', hq, justification_closure p q m m' w hj hd hq,
    fun v hc hbv => hd.1 v (hs v hc (hd.2 v hbv))⟩

/-- `Hands`: the subject has hands. -/
axiom Hands : Proposition
/-- `External`: there are external things. -/
axiom External : Proposition
/-- `Vat`: the subject is a handless brain in a vat. -/
axiom Vat : Proposition
/-- Not envatted. -/
def NotVat : Proposition := fun v => ¬ Vat v

/-- Hands are external things: `Hands` entails `External`. -/
axiom hands_external : ∀ v, Hands v → External v
/-- The envatted subject is handless: `Vat` entails `¬ Hands`. -/
axiom vat_handless : ∀ v, Vat v → ¬ Hands v

/-- The actual world. -/
axiom actual : World
/-- The ordinary and the sceptical contexts. -/
axiom ordinary : Context
axiom sceptical : Context
/-- Perception and the two deductive bases. -/
axiom perception : Basis
axiom deductionE : Basis
axiom deductionV : Basis

/-- Assumption 2.5 (Moore's situation): belief in `Hands` by perception. -/
axiom believes_hands : Believes Hands perception actual
/-- Assumption 2.5: justified (EPI-19). -/
axiom justified_hands : Justified Hands perception actual
/-- Assumption 2.5: the conclusions are believed on their deductive bases. -/
axiom believes_conclusions :
  Believes External deductionE actual ∧ Believes NotVat deductionV actual
/-- Assumption 2.5: the basis for `External` is a deduction from `Hands`. -/
axiom deduced_external : ∀ v, Believes External deductionE v → Believes Hands perception v
/-- Assumption 2.5: the basis for `NotVat` is a deduction from `Hands`. -/
axiom deduced_notvat : ∀ v, Believes NotVat deductionV v → Believes Hands perception v

/-- Assumption 2.6 (ordinary closeness). -/
axiom ordinary_closeness :
  ∀ v, Close ordinary actual v → Believes Hands perception v → Hands v

/-- Assumption 2.7 (envatted counterparts). -/
axiom counterpart : World → Basis → World
axiom counterpart_vat : ∀ w m, Vat (counterpart w m)
axiom counterpart_beliefs :
  ∀ w m (p : Proposition), Believes p m w → Believes p m (counterpart w m)

/-- Assumption 2.8 (attention). In the sceptical context envatted counterparts
are close. -/
axiom attention : ∀ w m, Close sceptical w (counterpart w m)

/-- Proposition 3.1 (Moore's proof is sound). -/
theorem moore_sound : Hands actual ∧ External actual ∧ (∀ v, Hands v → External v) := by
  have h : Hands actual := ordinary_closeness actual (centring _ _) believes_hands
  exact ⟨h, hands_external _ h, hands_external⟩

/-- Theorem 3.2 (Moore knows). -/
theorem moore_knows :
    Knows ordinary Hands actual ∧ Knows ordinary External actual ∧
    Knows ordinary NotVat actual := by
  have hs : Safe ordinary Hands perception actual := ordinary_closeness
  refine ⟨⟨perception, believes_hands, justified_hands, hs⟩, ?_, ?_⟩
  · exact closure justified_hands hs
      ⟨hands_external, deduced_external⟩ believes_conclusions.1
  · exact closure justified_hands hs
      ⟨fun v h hv => vat_handless v hv h, deduced_notvat⟩ believes_conclusions.2

/-- Corollary 3.3. In the ordinary context the premise (S1) is false, the
closure premise (S2) is true, and the conclusion (S3) is false. -/
theorem sceptic_premise_false :
    ¬ ¬ Knows ordinary NotVat actual ∧
    (Knows ordinary Hands actual → Knows ordinary NotVat actual) ∧
    ¬ ¬ Knows ordinary Hands actual :=
  ⟨fun h => h moore_knows.2.2, fun _ => moore_knows.2.2, fun h => h moore_knows.1⟩

/-- Theorem 3.4 (the sceptic's context). -/
theorem sceptic_context (w : World) :
    ¬ Knows sceptical NotVat w ∧ ¬ Knows sceptical Hands w := by
  constructor
  · intro ⟨m, hb, _, hs⟩
    exact hs (counterpart w m) (attention w m) (counterpart_beliefs w m _ hb)
      (counterpart_vat w m)
  · intro ⟨m, hb, _, hs⟩
    exact vat_handless _ (counterpart_vat w m)
      (hs (counterpart w m) (attention w m) (counterpart_beliefs w m _ hb))

/-- Corollary 3.5 (compatibility). -/
theorem compatibility :
    Knows ordinary Hands actual ∧ ¬ Knows sceptical Hands actual :=
  ⟨moore_knows.1, (sceptic_context actual).2⟩

end Philosophy.EPI_02

#print axioms Philosophy.EPI_02.moore_knows
#print axioms Philosophy.EPI_02.sceptic_context
#print axioms Philosophy.EPI_02.compatibility
