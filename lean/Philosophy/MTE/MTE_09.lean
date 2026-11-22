/-
MTE-09 · Debunking the Debunkers
Formalization of Definitions 3.1 to 3.3, Assumptions 3.4 to 3.7,
Propositions 4.1 and 4.2, Lemma 4.3, Theorem 4.4 and Corollary 4.5.

A natural state of a situation fixes which reason-relevant features each
kind of consideration presents (harm, need, reciprocity, and so on). Which
reasons of a kind there are is a function of these features (Assumption
3.4, the naturalism of MTE-01). The evaluative faculty forms verdicts by a
single mechanism that responds to the features, whatever the kind
(Assumption 3.5). Selection favored the faculty because its verdicts were
correct for the kinds of reasons whose tracking enhanced fitness in the
ancestral environment (Assumption 3.6). Moral reasons are made by features
that were also presented in selected cases (Assumption 3.7, restricted to
the core domain).

What this file establishes. If the moral facts were unconnected to what
selection rewarded, no faculty would be guaranteed to be reliable about
them, and any faculty would be everywhere wrong relative to some
assignment of moral facts (Propositions 4.1 and 4.2: Street's first horn,
granted). Given Assumptions 3.4 to 3.7, the faculty is reliable about moral
reasons on the core domain (Theorem 4.4), its moral verdicts are sensitive
to the moral facts there (Lemma 4.3), and the debunker's insensitivity
premise is false for that domain (Corollary 4.5).

What it does not establish. It does not establish the four assumptions;
it says nothing about moral verdicts concerning features that were never
presented in selected cases, where reliability is not guaranteed; and it
does not model degrees of reliability.
-/

namespace Philosophy.MTE_09

section General

variable {X : Type}

/-- Definition 3.1. A verdict function `d` is reliable about the facts `m`
on a domain `D` if it agrees with them everywhere on `D`. -/
def ReliableOn (d m : X → Bool) (D : X → Prop) : Prop := ∀ x, D x → d x = m x

/-- Definition 3.2. `d` is sensitive to `m` on `D` if, for situations in
`D`, a difference in the facts makes a difference to the verdict. -/
def Sensitive (d m : X → Bool) (D : X → Prop) : Prop :=
  ∀ x y, D x → D y → m x ≠ m y → d x ≠ d y

/-- Definition 3.3. The debunker's insensitivity premise: on `D` the facts
vary while the verdicts do not. -/
def Insensitive (d m : X → Bool) (D : X → Prop) : Prop :=
  (∃ x y, D x ∧ D y ∧ m x ≠ m y) ∧ ∀ x y, D x → D y → d x = d y

/-- Proposition 4.1 (no guarantee without a link). For every verdict
function there is an assignment of facts relative to which it is wrong
everywhere. -/
theorem no_guarantee (d : X → Bool) : ∃ m : X → Bool, ∀ x, d x ≠ m x :=
  ⟨fun x => !d x, fun x => by
    show d x ≠ !d x
    cases d x <;> decide⟩

/-- Proposition 4.2 (coincidence). For every verdict function there is
also an assignment relative to which it is reliable everywhere; so, absent
a link, a faculty's reliability is a matter of which assignment obtains. -/
theorem coincidence (d : X → Bool) : ∃ m : X → Bool, ReliableOn d m (fun _ => True) :=
  ⟨d, fun _ _ => rfl⟩

/-- Lemma 4.3. Reliability on a domain implies sensitivity on it, and
excludes the debunker's insensitivity premise. -/
theorem reliable_sensitive (d m : X → Bool) (D : X → Prop) (h : ReliableOn d m D) :
    Sensitive d m D ∧ ¬ Insensitive d m D := by
  have hs : Sensitive d m D := fun x y hx hy hne e => by
    rw [h x hx, h y hy] at e; exact hne e
  refine ⟨hs, fun ⟨⟨x, y, hx, hy, hne⟩, hconst⟩ => hs x y hx hy hne (hconst x y hx hy)⟩

end General

/-- Situations, individuated by their natural states. -/
axiom State : Type
/-- Kinds of reasons (prudential, social, moral, ...). -/
axiom Kind : Type
/-- Reason-relevant natural features. -/
axiom Feature : Type
/-- The features that a situation presents with respect to a kind. -/
axiom feature : Kind → State → Feature

/-- Assumption 3.4 (naturalism, MTE-01). Which reasons there are depends
on the natural features alone: `makes f` says whether features `f` give a
reason (to the response at issue). -/
axiom makes : Feature → Bool
noncomputable def reason (k : Kind) (x : State) : Bool := makes (feature k x)

/-- Assumption 3.5 (unity of the capacity). The faculty forms its verdicts
by a single mechanism that responds to the features, whatever the kind. -/
axiom respond : Feature → Bool
noncomputable def verdict (k : Kind) (x : State) : Bool := respond (feature k x)

/-- The kinds of reasons whose tracking enhanced fitness, and the ancestral
situations. -/
axiom Selected : Kind → Prop
axiom Ancestral : State → Prop

/-- Assumption 3.6 (selection for tracking reasons). In ancestral
situations, the faculty's verdicts about selected kinds were correct. -/
axiom selection : ∀ k x, Selected k → Ancestral x → verdict k x = reason k x

/-- The moral kind. -/
axiom moralKind : Kind

/-- The core moral domain: situations whose morally relevant features were
also presented, with respect to some selected kind, in some ancestral
situation. -/
def Core (x : State) : Prop :=
  ∃ k y, Selected k ∧ Ancestral y ∧ feature k y = feature moralKind x

/-- Assumption 3.7 (continuity). The core domain is not empty: some morally
relevant features are features that selected kinds also present. -/
axiom continuity : ∃ x, Core x

/-- Theorem 4.4 (tracking). The faculty is reliable about moral reasons on
the core domain. -/
theorem tracking : ReliableOn (verdict moralKind) (reason moralKind) Core := by
  intro x ⟨k, y, hk, hy, hf⟩
  have h := selection k y hk hy
  simp only [verdict, reason] at h ⊢
  rw [← hf]; exact h

/-- Corollary 4.5. On the core domain, which is nonempty, the faculty's
moral verdicts are sensitive to the moral facts, and the debunker's
insensitivity premise is false. -/
theorem not_debunked :
    (∃ x, Core x) ∧ Sensitive (verdict moralKind) (reason moralKind) Core ∧
      ¬ Insensitive (verdict moralKind) (reason moralKind) Core :=
  ⟨continuity, reliable_sensitive _ _ _ tracking⟩

end Philosophy.MTE_09

#print axioms Philosophy.MTE_09.tracking
#print axioms Philosophy.MTE_09.not_debunked
#print axioms Philosophy.MTE_09.no_guarantee
