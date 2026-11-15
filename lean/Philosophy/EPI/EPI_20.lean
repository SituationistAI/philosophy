/-
EPI-20 · Closure Holds
Formalization of Lemma 3.1, Theorem 3.2, Corollary 3.4 and Proposition 3.5.

What this file establishes. With knowledge as justified safe belief
(Definitions 2.1 and 2.2, from EPI-01), safety is closed under competent
deduction (Definition 2.3, Lemma 3.1); given that justification is closed under
competent deduction (Assumption 2.4), knowledge is closed (Theorem 3.2). Given
an ordinary zoo (Assumption 3.3), the visitor who deduces that the animals are
not disguised mules knows that they are not (Corollary 3.4). A three-world model
shows that sensitivity is not closed while safety holds (Proposition 3.5).

What it does not establish. Assumption 2.4 or Assumption 3.3, which are
argued for in the manuscript; nor anything about which worlds are close.
-/

namespace Philosophy.EPI_20

/-- Possible worlds. -/
axiom World : Type
/-- Bases on which beliefs are held. -/
axiom Basis : Type

/-- Propositions as sets of worlds. -/
abbrev Proposition := World → Prop

/-- `Close w v`: `v` is close to `w`. -/
axiom Close : World → World → Prop
/-- `Believes p m w`: at `w` the subject believes `p` on basis `m`. -/
axiom Believes : Proposition → Basis → World → Prop
/-- `Justified p m w`: at `w` the subject is justified in believing `p` on `m`. -/
axiom Justified : Proposition → Basis → World → Prop

/-- Definition 2.1 (safety). -/
def Safe (p : Proposition) (m : Basis) (w : World) : Prop :=
  ∀ v, Close w v → Believes p m v → p v

/-- Definition 2.2 (knowledge). -/
def Knows (p : Proposition) (w : World) : Prop :=
  ∃ m, Believes p m w ∧ Justified p m w ∧ Safe p m w

/-- Definition 2.3 (competent deduction). -/
def CompetentDeduction (p : Proposition) (m : Basis) (q : Proposition) (m' : Basis) : Prop :=
  (∀ v, p v → q v) ∧ (∀ v, Believes q m' v → Believes p m v)

/-- Assumption 2.4 (justification is closed under competent deduction). -/
axiom justification_closure :
  ∀ (p q : Proposition) (m m' : Basis) (w : World),
    Justified p m w → CompetentDeduction p m q m' → Believes q m' w → Justified q m' w

/-- Lemma 3.1 (safety is closed; Proposition 6.1 of EPI-01). -/
theorem safety_closure {p q : Proposition} {m m' : Basis} {w : World}
    (hs : Safe p m w) (hd : CompetentDeduction p m q m') : Safe q m' w :=
  fun v hc hb => hd.1 v (hs v hc (hd.2 v hb))

/-- Theorem 3.2 (closure, Principle P1). -/
theorem closure {p q : Proposition} {m m' : Basis} {w : World}
    (hk : Believes p m w ∧ Justified p m w ∧ Safe p m w)
    (hd : CompetentDeduction p m q m') (hb : Believes q m' w) :
    Knows q w :=
  ⟨m', hb, justification_closure p q m m' w hk.2.1 hd hb, safety_closure hk.2.2 hd⟩

/-! The zoo. -/

/-- The animals in the pen are zebras. -/
axiom Zebra : Proposition
/-- The animals are not cleverly disguised mules. -/
axiom NotMule : Proposition
/-- Zebras are not mules: `Zebra` entails `NotMule` (Section 3). -/
axiom zebra_not_mule : ∀ v, Zebra v → NotMule v
/-- The actual world. -/
axiom actual : World
/-- The basis of looking. -/
axiom looking : Basis
/-- The deductive basis for the belief that the animals are not disguised mules. -/
axiom deduction : Basis

/-- Assumption 3.3, first clause: the visitor believes `Zebra` by looking. -/
axiom believes_zebra : Believes Zebra looking actual
/-- Assumption 3.3, first clause: and is justified. -/
axiom justified_zebra : Justified Zebra looking actual
/-- Assumption 3.3, second clause (an ordinary zoo). -/
axiom ordinary_zoo : ∀ v, Close actual v → Believes Zebra looking v → Zebra v

/-- Corollary 3.4 (the zebra). -/
theorem zebra (hb : Believes NotMule deduction actual)
    (hdep : ∀ v, Believes NotMule deduction v → Believes Zebra looking v) :
    Knows NotMule actual :=
  closure ⟨believes_zebra, justified_zebra, ordinary_zoo⟩ ⟨zebra_not_mule, hdep⟩ hb

/-! Proposition 3.5: a model in which sensitivity is not closed. -/

/-- The three worlds: actual (zebras), empty pen, disguised mules. -/
inductive W | at | empty | mules
  deriving DecidableEq

/-- Nearness rank to the actual world. -/
def rank : W → Nat
  | .at => 0 | .empty => 1 | .mules => 2

/-- Closeness to the actual world: rank at most 1. -/
def closeM (v : W) : Bool := decide (rank v ≤ 1)

def zebraM : W → Bool | .at => true | _ => false
def notMuleM : W → Bool | .mules => false | _ => true
/-- The visitor believes both propositions at `at` and `mules`, neither at `empty`. -/
def believesM : W → Bool | .empty => false | _ => true

def worlds : List W := [.at, .empty, .mules]

/-- Safety at the actual world in the model. -/
def safeM (p : W → Bool) : Bool :=
  worlds.all fun v => !(closeM v && believesM v) || p v

/-- Sensitivity at the actual world: at the nearest worlds where `p` is false,
the visitor does not believe `p`. -/
def sensitiveM (p : W → Bool) : Bool :=
  worlds.all fun v =>
    !(!p v && worlds.all (fun u => p u || decide (rank v ≤ rank u))) || !believesM v

/-- Proposition 3.5 (sensitivity is not closed). Both beliefs are safe; the
belief in `Zebra` is sensitive; the deduced belief in `NotMule` is not. -/
theorem sensitivity_not_closed :
    safeM zebraM = true ∧ safeM notMuleM = true ∧
    sensitiveM zebraM = true ∧ sensitiveM notMuleM = false ∧
    (∀ v : W, zebraM v = true → notMuleM v = true) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro v; cases v <;> decide

end Philosophy.EPI_20

#print axioms Philosophy.EPI_20.closure
#print axioms Philosophy.EPI_20.zebra
#print axioms Philosophy.EPI_20.sensitivity_not_closed
