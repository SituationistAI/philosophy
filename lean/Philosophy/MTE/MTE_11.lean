/-
MTE-11 · Reasons First
Formalization of Definitions 3.2 to 3.6, Propositions 4.1 to 4.4,
Lemma 5.1, Proposition 5.2 and Theorem 5.6.

A reason profile assigns to each response (an act or an attitude) the
total strength of the reasons for it, in a given situation, for a given
agent. Reasons are the primitive (Assumption 3.1); ought, permission,
fittingness, goodness and betterness are defined from them
(Definitions 3.2 to 3.6).

What this file establishes. (i) The defined notions have the structure
that the corresponding pre-theoretic notions are agreed to have: ought
implies permission, oughts in a choice set are unique, a nonempty finite
choice set contains a permissible option, and ought is permission without
a permissible rival (Propositions 4.1 to 4.4). (ii) A version of Padoa's
method (Lemma 5.1): a notion is not definable from a base if two possible
situations agree on the base and differ on the notion. (iii) The ought,
permission and fittingness facts of a situation are invariant under a
uniform increase in the strength of the reasons for its options
(Proposition 5.2). (iv) Given the adequacy of the definitions
(Assumption 5.3) and two witness situations (Assumptions 5.4 and 5.5),
every notion of Definitions 3.2 to 3.6 is definable from reasons, while
the pro tanto reason facts are definable neither from the deontic and
fittingness facts nor from the evaluative facts (Theorem 5.6).

What it does not establish. It does not establish Assumptions 5.3 to 5.5,
which carry the philosophical weight; it does not model the relation
between reasons and the natural facts with which Section 6 of the
manuscript identifies them; and it does not model weighing beyond the
addition of strengths.
-/

namespace Philosophy.MTE_11

section Structure

variable {R O : Type}

/-- Assumption 3.1 (the primitive, in the model). A reason profile gives
the total strength of the reasons for each response. -/
abbrev Profile (R : Type) := R → Nat

/-- Definition 3.2. There is a (pro tanto) reason for `a`. -/
def HasReason (r : Profile R) (a : R) : Prop := 0 < r a

/-- Definition 3.3. In choice set `S`, `a` is what one ought to do: the
reasons for it are stronger than those for each alternative. -/
def Ought (r : Profile R) (S : List R) (a : R) : Prop :=
  a ∈ S ∧ ∀ b, b ∈ S → b ≠ a → r b < r a

/-- Definition 3.4. In choice set `S`, `a` is permissible: no option is
supported by stronger reasons. -/
def Permissible (r : Profile R) (S : List R) (a : R) : Prop :=
  a ∈ S ∧ ∀ b, b ∈ S → r b ≤ r a

/-- Definition 3.5. An attitude is fitting, among the attitudes in `S`,
if it is an attitude and the reasons for it are sufficient. -/
def Fitting (att : R → Prop) (r : Profile R) (S : List R) (a : R) : Prop :=
  att a ∧ Permissible r S a

/-- Definition 3.6 (buck-passing). An object is good if there is reason to
favor it, and better than another if the reasons to favor it are
stronger. -/
def Good (favor : O → R) (r : Profile R) (o : O) : Prop := 0 < r (favor o)

def Better (favor : O → R) (r : Profile R) (o p : O) : Prop :=
  r (favor p) < r (favor o)

/-- Proposition 4.1. Ought implies permissible. -/
theorem ought_permissible (r : Profile R) (S : List R) (a : R)
    (h : Ought r S a) : Permissible r S a := by
  refine ⟨h.1, fun b hb => ?_⟩
  rcases Classical.em (b = a) with e | e
  · rw [e]; exact Nat.le_refl _
  · exact Nat.le_of_lt (h.2 b hb e)

/-- Proposition 4.2. Deontic consistency: in a choice set there is at most
one option that one ought to choose. -/
theorem ought_unique (r : Profile R) (S : List R) (a b : R)
    (ha : Ought r S a) (hb : Ought r S b) : a = b :=
  Classical.byContradiction fun hne => by
    have h1 := ha.2 b hb.1 (fun e => hne e.symm)
    have h2 := hb.2 a ha.1 hne
    omega

/-- Lemma used in Proposition 4.3: a nonempty list has an element of
maximal strength. -/
theorem exists_max (r : Profile R) :
    ∀ S : List R, S ≠ [] → ∃ a, a ∈ S ∧ ∀ b, b ∈ S → r b ≤ r a
  | [], h => absurd rfl h
  | [x], _ => ⟨x, List.mem_singleton.mpr rfl, fun b hb => by
      rw [List.mem_singleton.mp hb]; exact Nat.le_refl _⟩
  | x :: y :: t, _ => by
      obtain ⟨a, ha, hmax⟩ := exists_max r (y :: t) (List.cons_ne_nil y t)
      rcases Nat.le_total (r x) (r a) with hle | hle
      · refine ⟨a, List.mem_cons_of_mem x ha, fun b hb => ?_⟩
        rcases List.mem_cons.mp hb with e | e
        · rw [e]; exact hle
        · exact hmax b e
      · refine ⟨x, List.mem_cons_self x _, fun b hb => ?_⟩
        rcases List.mem_cons.mp hb with e | e
        · rw [e]; exact Nat.le_refl _
        · exact Nat.le_trans (hmax b e) hle

/-- Proposition 4.3. Every nonempty finite choice set contains a
permissible option. -/
theorem permissible_exists (r : Profile R) (S : List R) (h : S ≠ []) :
    ∃ a, Permissible r S a :=
  exists_max r S h

/-- Proposition 4.4. One ought to choose `a` if and only if `a` is
permissible and no other option is. -/
theorem ought_iff (r : Profile R) (S : List R) (a : R) :
    Ought r S a ↔ Permissible r S a ∧ ∀ b, Permissible r S b → b = a := by
  constructor
  · intro h
    refine ⟨ought_permissible r S a h, fun b hb => ?_⟩
    exact Classical.byContradiction fun hne => by
      have h1 := h.2 b hb.1 hne
      have h2 := hb.2 a h.1
      omega
  · intro ⟨hp, huniq⟩
    refine ⟨hp.1, fun b hb hne => ?_⟩
    exact Classical.byContradiction fun hlt => by
      have hab : r a ≤ r b := Nat.le_of_not_lt hlt
      have pb : Permissible r S b :=
        ⟨hb, fun c hc => Nat.le_trans (hp.2 c hc) hab⟩
      exact hne (huniq b pb)

/-- Lemma 5.1 (Padoa's method). If two situations agree on the base and
differ on the target, the target is not definable from the base. -/
theorem padoa {M B T : Type} (base : M → B) (target : M → T) (m₁ m₂ : M)
    (hb : base m₁ = base m₂) (ht : target m₁ ≠ target m₂) :
    ¬ ∃ D : B → T, ∀ m, target m = D (base m) := by
  intro ⟨D, hD⟩
  exact ht (by rw [hD m₁, hD m₂, hb])

/-- Proposition 5.2 (shift invariance). If the reasons for every option in
`S` are increased by the same amount, the ought and permission facts in
`S` are unchanged. -/
theorem shift_ought (r r' : Profile R) (S : List R) (c : Nat)
    (h : ∀ b, b ∈ S → r' b = r b + c) (a : R) :
    Ought r S a ↔ Ought r' S a := by
  constructor
  · intro ⟨ha, hb⟩
    refine ⟨ha, fun b hbS hne => ?_⟩
    have := hb b hbS hne
    rw [h b hbS, h a ha]; omega
  · intro ⟨ha, hb⟩
    refine ⟨ha, fun b hbS hne => ?_⟩
    have := hb b hbS hne
    rw [h b hbS, h a ha] at this; omega

theorem shift_permissible (r r' : Profile R) (S : List R) (c : Nat)
    (h : ∀ b, b ∈ S → r' b = r b + c) (a : R) :
    Permissible r S a ↔ Permissible r' S a := by
  constructor
  · intro ⟨ha, hb⟩
    refine ⟨ha, fun b hbS => ?_⟩
    have := hb b hbS
    rw [h b hbS, h a ha]; omega
  · intro ⟨ha, hb⟩
    refine ⟨ha, fun b hbS => ?_⟩
    have := hb b hbS
    rw [h b hbS, h a ha] at this; omega

end Structure

/-! Situations, pre-theoretic normative facts, and the main theorem. -/

/-- Possible situations of a fixed agent. -/
axiom Sit : Type
/-- Responses: acts and attitudes. -/
axiom Resp : Type
/-- Objects of evaluation. -/
axiom Obj : Type
/-- The attitude of favoring an object. -/
axiom favor : Obj → Resp
/-- Which responses are attitudes. -/
axiom IsAttitude : Resp → Prop
/-- Assumption 3.1. The primitive: the strength of the reasons for each
response in each situation. -/
axiom strength : Sit → Resp → Nat
/-- The options open to the agent in a situation. -/
axiom options : Sit → List Resp

/-- The deontic, fittingness and evaluative facts, taken as given before
any definition. -/
axiom OughtFact : Sit → Resp → Prop
axiom PermFact : Sit → Resp → Prop
axiom FitFact : Sit → Resp → Prop
axiom GoodFact : Sit → Obj → Prop
axiom BetterFact : Sit → Obj → Obj → Prop

/-- Assumption 5.3 (adequacy of Definitions 3.3 to 3.6). -/
axiom ought_adequate : ∀ s a, OughtFact s a ↔ Ought (strength s) (options s) a
axiom perm_adequate : ∀ s a, PermFact s a ↔ Permissible (strength s) (options s) a
axiom fit_adequate : ∀ s a, FitFact s a ↔ Fitting IsAttitude (strength s) (options s) a
axiom good_adequate : ∀ s o, GoodFact s o ↔ Good favor (strength s) o
axiom better_adequate : ∀ s o p, BetterFact s o p ↔ Better favor (strength s) o p

/-- Assumption 5.4 (the two doors). There are situations with the same
options, one in which there is no reason for any of them and one in which
the reasons for each are increased by the same positive amount. -/
axiom two_doors : ∃ s t a c, options s = options t ∧ a ∈ options s ∧
  strength s a = 0 ∧ 0 < c ∧ ∀ b, b ∈ options s → strength t b = strength s b + c

/-- Assumption 5.5 (trivial evidence). There are situations with the same
evaluative facts that differ in whether there is a reason for some
response (a belief supported by evidence in one and not in the other). -/
axiom trivial_evidence : ∃ s t a, GoodFact s = GoodFact t ∧
  BetterFact s = BetterFact t ∧ 0 < strength s a ∧ strength t a = 0

/-- The deontic and fittingness base of a situation. -/
noncomputable def deonticBase (s : Sit) : List Resp × (Resp → Prop) × (Resp → Prop) × (Resp → Prop) :=
  (options s, OughtFact s, PermFact s, FitFact s)

/-- The evaluative base of a situation. -/
noncomputable def valueBase (s : Sit) : (Obj → Prop) × (Obj → Obj → Prop) :=
  (GoodFact s, BetterFact s)

/-- The pro tanto reason facts of a situation. -/
def reasonFacts (s : Sit) : Resp → Prop := fun a => HasReason (strength s) a

/-- Theorem 5.6 (reasons first). (a) The ought, permission, fittingness,
goodness and betterness facts are fixed by the reasons. (b) The pro tanto
reason facts are not definable from the deontic and fittingness facts.
(c) They are not definable from the evaluative facts. -/
theorem reasons_first :
    (∀ s, OughtFact s = Ought (strength s) (options s) ∧
          PermFact s = Permissible (strength s) (options s) ∧
          FitFact s = Fitting IsAttitude (strength s) (options s) ∧
          GoodFact s = Good favor (strength s) ∧
          BetterFact s = Better favor (strength s)) ∧
    (¬ ∃ D : List Resp × (Resp → Prop) × (Resp → Prop) × (Resp → Prop) → (Resp → Prop),
        ∀ s, reasonFacts s = D (deonticBase s)) ∧
    (¬ ∃ D : (Obj → Prop) × (Obj → Obj → Prop) → (Resp → Prop),
        ∀ s, reasonFacts s = D (valueBase s)) := by
  refine ⟨fun s => ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · funext a; exact propext (ought_adequate s a)
  · funext a; exact propext (perm_adequate s a)
  · funext a; exact propext (fit_adequate s a)
  · funext o; exact propext (good_adequate s o)
  · funext o p; exact propext (better_adequate s o p)
  · obtain ⟨s, t, a, c, hopt, ha, h0, hc, hshift⟩ := two_doors
    have hsh : ∀ b, b ∈ options s → strength t b = strength s b + c := hshift
    apply padoa deonticBase reasonFacts s t
    · have e1 : OughtFact s = OughtFact t := by
        funext b
        apply propext
        rw [ought_adequate, ought_adequate, ← hopt]
        exact shift_ought _ _ _ c hsh b
      have e2 : PermFact s = PermFact t := by
        funext b
        apply propext
        rw [perm_adequate, perm_adequate, ← hopt]
        exact shift_permissible _ _ _ c hsh b
      have e3 : FitFact s = FitFact t := by
        funext b
        apply propext
        rw [fit_adequate, fit_adequate, ← hopt]
        exact and_congr Iff.rfl (shift_permissible _ _ _ c hsh b)
      simp only [deonticBase, hopt, e1, e2, e3]
    · intro e
      have h1 : reasonFacts t a := by
        show 0 < strength t a
        rw [hsh a ha]; omega
      rw [← e] at h1
      have h2 : 0 < strength s a := h1
      omega
  · obtain ⟨s, t, a, hg, hb, hs, ht⟩ := trivial_evidence
    apply padoa valueBase reasonFacts s t
    · simp only [valueBase, hg, hb]
    · intro e
      have h1 : reasonFacts s a := hs
      rw [e] at h1
      have h2 : 0 < strength t a := h1
      omega

end Philosophy.MTE_11

#print axioms Philosophy.MTE_11.reasons_first
#print axioms Philosophy.MTE_11.ought_iff
#print axioms Philosophy.MTE_11.permissible_exists
