/-
ETH-15 · There Are No Genuine Moral Dilemmas
Formalization of Lemma 3.1, Theorems 3.2, 3.3 and 3.4 and Corollary 3.5.

A choice situation has a finite, nonempty menu of available options
(Definition 2.1). Situations carry pro tanto requirements, each satisfied by
some options and not by others (Definition 2.2). An apparent dilemma is a
situation in which every available option fails some requirement and every
requirement can be met by some available option (Definition 2.3). A genuine
dilemma is a situation in which no available option is permissible all
things considered (Definition 2.4).

What this file establishes. From ought-implies-can (Principle P1), the
principle that an impermissible option ought not to be taken (Principle P2)
and the agglomeration of prohibitions (Principle P3), no situation is a
genuine dilemma (Theorem 3.2). From the balance principle, comparability in
apparent dilemmas and impartial tie-breaking (Assumptions 2.5, 2.6, 2.7), no
apparent dilemma has two permissible options (Theorem 3.3). Hence every
apparent dilemma has exactly one permissible option (Theorem 3.4), and that
option fails some requirement (Corollary 3.5).

What it does not establish. The six premises are axioms and are defended in
the manuscript, not here. Nothing in this file concerns what the agent knows:
the claim that the permissible option may be identifiable only in retrospect
(Section 4 of the manuscript) is not modelled.
-/

namespace Philosophy.ETH_15

/-- Situations. -/
axiom Sit : Type

/-- Options. -/
axiom Opt : Type

/-- Definition 2.1. The menu of available options in a situation. -/
axiom menu : Sit → List Opt

/-- Definition 2.1. Every menu is nonempty. -/
axiom menu_nonempty : ∀ s, menu s ≠ []

/-- Definition 2.2. Pro tanto requirements in force in a situation. -/
axiom Requirement : Type

/-- Definition 2.2. `InForce s r`: requirement `r` applies to the agent in `s`. -/
axiom InForce : Sit → Requirement → Prop

/-- Definition 2.2. `Sat r o`: option `o` satisfies requirement `r`; an option
that does not satisfy a requirement in force infringes it. -/
axiom Sat : Requirement → Opt → Prop

/-- Definition 2.3. An apparent dilemma: every available option infringes
some requirement in force, and every requirement in force can be satisfied
by some available option. -/
def ApparentDilemma (s : Sit) : Prop :=
  (∀ o, o ∈ menu s → ∃ r, InForce s r ∧ ¬ Sat r o) ∧
  (∀ r, InForce s r → ∃ o, o ∈ menu s ∧ Sat r o)

/-- All-things-considered permissibility. -/
axiom Permissible : Sit → Opt → Prop

/-- Definition 2.4. A genuine dilemma: no available option is permissible. -/
def GenuineDilemma (s : Sit) : Prop :=
  ∀ o, o ∈ menu s → ¬ Permissible s o

/-- `Ought s P`: all things considered, the agent in `s` ought to take an
option satisfying `P`. -/
axiom Ought : Sit → (Opt → Prop) → Prop

/-- Principle P1 (ought implies can). -/
axiom ought_implies_can : ∀ s P, Ought s P → ∃ o, o ∈ menu s ∧ P o

/-- Principle P2 (prohibition). An impermissible option ought not to be
taken. -/
axiom prohibition : ∀ s o, ¬ Permissible s o → Ought s (fun x => x ≠ o)

/-- Principle P3 (agglomeration of prohibitions). -/
axiom agglomeration : ∀ s (P Q : Opt → Prop),
  Ought s P → Ought s Q → Ought s (fun x => P x ∧ Q x)

/-- `Better s a b`: on the balance of reasons in `s`, `a` is better than `b`. -/
axiom Better : Sit → Opt → Opt → Prop

/-- `Tied s a b`: the reasons for `a` and for `b` are exactly balanced. -/
axiom Tied : Sit → Opt → Opt → Prop

/-- Assumption 2.5 (balance). No available option is better than a
permissible one. -/
axiom balance : ∀ s o, Permissible s o → ∀ o', o' ∈ menu s → ¬ Better s o' o

/-- Assumption 2.6 (comparability). In an apparent dilemma, of two distinct
available options one is better than the other or they are tied. -/
axiom comparability : ∀ s, ApparentDilemma s → ∀ a b, a ∈ menu s → b ∈ menu s →
  a ≠ b → Better s a b ∨ Better s b a ∨ Tied s a b

/-- Assumption 2.7 (impartial tie-breaking). In an apparent dilemma, if two
available options are tied, some available option is better than both. -/
axiom tie_breaking : ∀ s, ApparentDilemma s → ∀ a b, a ∈ menu s → b ∈ menu s →
  Tied s a b → ∃ c, c ∈ menu s ∧ Better s c a ∧ Better s c b

/-- Lemma 3.1 (agglomerated prohibition). If every option in a nonempty list
is impermissible, the agent ought to take an option outside the list. -/
theorem agglomerated (s : Sit) :
    ∀ (a : Opt) (t : List Opt), (∀ o, o ∈ a :: t → ¬ Permissible s o) →
      Ought s (fun x => ∀ o, o ∈ a :: t → x ≠ o)
  | a, [], h => by
    have h1 := prohibition s a (h a (List.mem_cons_self a []))
    have heq : (fun x => ∀ o, o ∈ [a] → x ≠ o) = (fun x => x ≠ a) := by
      funext x
      apply propext
      constructor
      · intro hx; exact hx a (List.mem_cons_self a [])
      · intro hx o ho
        cases ho with
        | head => exact hx
        | tail _ h' => cases h'
    rw [heq]; exact h1
  | a, b :: t, h => by
    have h1 := prohibition s a (h a (List.mem_cons_self a _))
    have h2 := agglomerated s b t (fun o ho => h o (List.mem_cons_of_mem a ho))
    have h3 := agglomeration s _ _ h1 h2
    have heq : (fun x => x ≠ a ∧ ∀ o, o ∈ b :: t → x ≠ o) =
        (fun x => ∀ o, o ∈ a :: b :: t → x ≠ o) := by
      funext x
      apply propext
      constructor
      · intro ⟨hxa, hxt⟩ o ho
        cases ho with
        | head => exact hxa
        | tail _ h' => exact hxt o h'
      · intro hx
        exact ⟨hx a (List.mem_cons_self a _),
          fun o ho => hx o (List.mem_cons_of_mem a ho)⟩
    rw [← heq]; exact h3

/-- Theorem 3.2 (no genuine dilemmas). No situation is a genuine dilemma. -/
theorem no_genuine_dilemma (s : Sit) : ¬ GenuineDilemma s := by
  intro hg
  cases hm : menu s with
  | nil => exact menu_nonempty s hm
  | cons a t =>
    have hall : ∀ o, o ∈ a :: t → ¬ Permissible s o := by
      intro o ho; rw [← hm] at ho; exact hg o ho
    obtain ⟨x, hx, hnot⟩ := ought_implies_can s _ (agglomerated s a t hall)
    rw [hm] at hx
    exact hnot x hx rfl

/-- Theorem 3.3 (uniqueness). In an apparent dilemma, no two distinct
available options are both permissible. -/
theorem at_most_one (s : Sit) (hd : ApparentDilemma s) (a b : Opt)
    (ha : a ∈ menu s) (hb : b ∈ menu s)
    (pa : Permissible s a) (pb : Permissible s b) : a = b :=
  Classical.byContradiction fun hne =>
    match comparability s hd a b ha hb hne with
    | Or.inl hab => balance s b pb a ha hab
    | Or.inr (Or.inl hba) => balance s a pa b hb hba
    | Or.inr (Or.inr ht) =>
      match tie_breaking s hd a b ha hb ht with
      | ⟨c, hc, hca, _⟩ => balance s a pa c hc hca

/-- Theorem 3.4 (main result). Every apparent dilemma has exactly one
permissible available option. -/
theorem unique_permissible (s : Sit) (hd : ApparentDilemma s) :
    ∃ o, o ∈ menu s ∧ Permissible s o ∧
      ∀ o', o' ∈ menu s → Permissible s o' → o' = o := by
  have h : ∃ o, o ∈ menu s ∧ Permissible s o :=
    Classical.byContradiction fun hn =>
      no_genuine_dilemma s (fun o ho hp => hn ⟨o, ho, hp⟩)
  obtain ⟨o, ho, hp⟩ := h
  exact ⟨o, ho, hp, fun o' ho' hp' => at_most_one s hd o' o ho' ho hp' hp⟩

/-- Corollary 3.5 (remainder). In an apparent dilemma, the permissible
option infringes some requirement in force. -/
theorem remainder (s : Sit) (hd : ApparentDilemma s) :
    ∃ o r, o ∈ menu s ∧ Permissible s o ∧ InForce s r ∧ ¬ Sat r o := by
  obtain ⟨o, ho, hp, _⟩ := unique_permissible s hd
  obtain ⟨r, hr, hns⟩ := hd.1 o ho
  exact ⟨o, r, ho, hp, hr, hns⟩

end Philosophy.ETH_15

#print axioms Philosophy.ETH_15.no_genuine_dilemma
#print axioms Philosophy.ETH_15.unique_permissible
#print axioms Philosophy.ETH_15.remainder
