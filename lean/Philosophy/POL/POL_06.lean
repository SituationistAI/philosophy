/-
POL-06 · Property Is Not Theft
Formalization of Theorem 3.1 and Corollaries 3.2 and 3.3.

What this file establishes. Given that a theft is a holding that is not
rightful (Definition 2.2), that every theft is a theft of something to which
someone other than the thief has a right (Assumption 2.3), and that rightful
ownership is a form of holding (Assumption 2.4), Proudhon's thesis that every
property holding is a theft is false whenever there is any property holding
at all; and any theft entails that some holding is not a theft.

What it does not establish. It does not establish the three premises, which
are argued for informally in the manuscript, and it does not establish that
any actual holding is rightful, or that any particular distribution of
property is just (see POL-01 and POL-12).
-/

namespace Philosophy.POL_06

/-- Agents, individual or collective (Definition 2.1). -/
axiom Agent : Type

/-- Things that can be held. -/
axiom Thing : Type

/-- `Holds a t`: agent `a` holds `t` as property, rightfully or not
(Definition 2.1). -/
axiom Holds : Agent → Thing → Prop

/-- `Rightful a t`: agent `a` has a right to `t` (Definition 2.1). -/
axiom Rightful : Agent → Thing → Prop

/-- `Theft a t`: `a`'s holding of `t` is a theft. -/
axiom Theft : Agent → Thing → Prop

/-- Definition 2.2 (first clause). A theft is a holding. -/
axiom theft_is_holding : ∀ a t, Theft a t → Holds a t

/-- Definition 2.2 (second clause). A holding that is a theft is not
rightful. -/
axiom theft_not_rightful : ∀ a t, Theft a t → ¬ Rightful a t

/-- Assumption 2.3 (theft presupposes property). Whatever is stolen is
something to which someone other than the thief has a right. -/
axiom theft_presupposes_property :
  ∀ a t, Theft a t → ∃ b, b ≠ a ∧ Rightful b t

/-- Assumption 2.4. Rightful ownership is a form of holding. -/
axiom rightful_is_holding : ∀ b t, Rightful b t → Holds b t

/-- Proudhon's thesis (Definition 2.5): every property holding is a theft. -/
def ProudhonThesis : Prop := ∀ a t, Holds a t → Theft a t

/-- Theorem 3.1. If anyone holds anything as property, Proudhon's thesis is
false. -/
theorem proudhon_self_undermining
    (h : ∃ a t, Holds a t) : ¬ ProudhonThesis := by
  intro hp
  cases h with
  | intro a ha =>
    cases ha with
    | intro t hat =>
      cases theft_presupposes_property a t (hp a t hat) with
      | intro b hb =>
        exact theft_not_rightful b t
          (hp b t (rightful_is_holding b t hb.2)) hb.2

/-- Corollary 3.2. If there is any theft, some holding is not a theft. -/
theorem theft_entails_honest_holding
    (a : Agent) (t : Thing) (h : Theft a t) :
    ∃ b, Holds b t ∧ ¬ Theft b t := by
  cases theft_presupposes_property a t h with
  | intro b hb =>
    exact ⟨b, rightful_is_holding b t hb.2,
      fun hbt => theft_not_rightful b t hbt hb.2⟩

/-- Corollary 3.3. Proudhon's thesis is true only if there is no theft at
all. -/
theorem thesis_only_if_no_theft :
    ProudhonThesis → ∀ a t, ¬ Theft a t := by
  intro hp a t h
  exact proudhon_self_undermining ⟨a, t, theft_is_holding a t h⟩ hp

end Philosophy.POL_06

#print axioms Philosophy.POL_06.proudhon_self_undermining
#print axioms Philosophy.POL_06.thesis_only_if_no_theft
