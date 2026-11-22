/-
MTH-04 · Neo-Logicism Vindicated
Formalization of Lemmas 4.2-4.5, Propositions 5.2 and 5.3 and
Proposition 7.1.

Concepts on a domain `D` are predicates `D → Prop`. Equinumerosity is
Frege's one-one correlation by a relation (Definition 3.1). The number
operator `num` and Hume's principle (Definition 3.3) are axioms, so that
the dependence of the arithmetical results on Hume's principle is visible
in the `#print axioms` output.

What this file establishes. From Hume's principle alone, with the
definitions of zero and of the predecessor relation (Definition 3.4):
zero has no predecessor (Lemma 4.2); the predecessor relation is functional and
one-one (Lemmas 4.3 and 4.4); zero precedes one (Lemma 4.5). For an
arbitrary operator satisfying Hume's principle: the condition is preserved
by transport along any permutation (Proposition 5.2), and any two such
operators on one domain differ by a one-one relabeling (Proposition 5.3).
Basic Law V is inconsistent on every domain (Proposition 7.1).

What it does not establish. It does not formalize the ancestral, the
definition of natural number, the existence of successors for every
natural number or the induction axiom, and so not the whole of Frege's
theorem (Theorem 4.6); nor the stability of Hume's principle
(Proposition 5.4). It does not establish that Hume's principle is true or
logical: that is the philosophical argument of Sections 5 and 6.
-/

namespace Philosophy.MTH_04

/-- Definition 3.1. `F` and `G` are equinumerous if some relation
correlates the `F`s one-one with the `G`s. -/
def Equinum {D : Type} (F G : D → Prop) : Prop :=
  ∃ R : D → D → Prop,
    (∀ x, F x → ∃ y, G y ∧ R x y) ∧
    (∀ y, G y → ∃ x, F x ∧ R x y) ∧
    (∀ x y z, R x y → R x z → y = z) ∧
    (∀ x y z, R x z → R y z → x = y)

/-- Definition 3.2. An operator is an abstractor for Hume's principle on
`D` if it identifies exactly the equinumerous concepts. -/
def HPAbstractor {D : Type} (op : (D → Prop) → D) : Prop :=
  ∀ F G, op F = op G ↔ Equinum F G

/-- The domain of objects. -/
axiom D : Type

/-- The number operator: `num F` is the number of `F`s. -/
axiom num : (D → Prop) → D

/-- Definition 3.3 (Hume's principle). The number of `F`s is the number of
`G`s if and only if the `F`s and the `G`s are equinumerous. -/
axiom hume : ∀ F G : D → Prop, num F = num G ↔ Equinum F G

/-- Definition 3.4. Zero is the number of non-self-identical things. -/
noncomputable def zero : D := num (fun _ => False)

/-- Definition 3.4. One is the number of things identical with zero. -/
noncomputable def one : D := num (fun z => z = zero)

/-- Definition 3.4 (Frege). `Pred n m`: `n` immediately precedes `m`, i.e.
for some concept `F` and some `F` `x`, `m` is the number of `F`s and `n`
is the number of `F`s other than `x`. -/
def Pred (n m : D) : Prop :=
  ∃ F : D → Prop, ∃ x, F x ∧ num F = m ∧ num (fun z => F z ∧ z ≠ x) = n

/-- Lemma 4.2. Zero has no predecessor. -/
theorem zero_not_successor (n : D) : ¬ Pred n zero := by
  intro ⟨F, x, hx, hm, _⟩
  have ⟨_, h1, _⟩ := (hume F (fun _ => False)).mp hm
  have ⟨_, hf, _⟩ := h1 x hx
  exact hf

/-- Lemma 4.3. The predecessor relation is functional: a number has at most
one immediate successor. -/
theorem pred_functional (n m m' : D) (h1 : Pred n m) (h2 : Pred n m') :
    m = m' := by
  obtain ⟨F, x, hx, hm, hn⟩ := h1
  obtain ⟨G, y, hy, hm', hn'⟩ := h2
  have ⟨R, r1, r2, r3, r4⟩ :=
    (hume (fun z => F z ∧ z ≠ x) (fun z => G z ∧ z ≠ y)).mp (hn.trans hn'.symm)
  rw [← hm, ← hm']
  apply (hume F G).mpr
  refine ⟨fun u v => (F u ∧ u ≠ x ∧ G v ∧ v ≠ y ∧ R u v) ∨ (u = x ∧ v = y),
    ?_, ?_, ?_, ?_⟩
  · intro u hu
    by_cases hux : u = x
    · exact ⟨y, hy, Or.inr ⟨hux, rfl⟩⟩
    · obtain ⟨v, ⟨hv, hvy⟩, hr⟩ := r1 u ⟨hu, hux⟩
      exact ⟨v, hv, Or.inl ⟨hu, hux, hv, hvy, hr⟩⟩
  · intro v hv
    by_cases hvy : v = y
    · exact ⟨x, hx, Or.inr ⟨rfl, hvy⟩⟩
    · obtain ⟨u, ⟨hu, hux⟩, hr⟩ := r2 v ⟨hv, hvy⟩
      exact ⟨u, hu, Or.inl ⟨hu, hux, hv, hvy, hr⟩⟩
  · intro u v w h h'
    rcases h with ⟨_, hux, _, _, hr⟩ | ⟨hux, hvy⟩ <;>
      rcases h' with ⟨_, hux', _, _, hr'⟩ | ⟨hux', hwy⟩
    · exact r3 u v w hr hr'
    · exact absurd hux' hux
    · exact absurd hux hux'
    · rw [hvy, hwy]
  · intro u w v h h'
    rcases h with ⟨_, _, _, hvy, hr⟩ | ⟨hux, hvy⟩ <;>
      rcases h' with ⟨_, _, _, hvy', hr'⟩ | ⟨hwx, hvy'⟩
    · exact r4 u w v hr hr'
    · exact absurd hvy' hvy
    · exact absurd hvy hvy'
    · rw [hux, hwx]

/-- Lemma 4.4. The predecessor relation is one-one: a number has at most
one immediate predecessor. -/
theorem pred_injective (n n' m : D) (h1 : Pred n m) (h2 : Pred n' m) :
    n = n' := by
  obtain ⟨F, x, hx, hm, hn⟩ := h1
  obtain ⟨G, y, hy, hm', hn'⟩ := h2
  have ⟨R, r1, r2, r3, r4⟩ := (hume F G).mp (hm.trans hm'.symm)
  rw [← hn, ← hn']
  apply (hume _ _).mpr
  obtain ⟨a, ha, hxa⟩ := r1 x hx
  obtain ⟨b, hb, hby⟩ := r2 y hy
  refine ⟨fun u v => F u ∧ u ≠ x ∧ G v ∧ v ≠ y ∧ (R u v ∨ (R u y ∧ R x v)),
    ?_, ?_, ?_, ?_⟩
  · intro u ⟨hu, hux⟩
    obtain ⟨v, hv, huv⟩ := r1 u hu
    by_cases hvy : v = y
    · have hay : a ≠ y := by
        intro hay
        rw [hay] at hxa
        rw [hvy] at huv
        exact hux (r4 u x y huv hxa)
      rw [hvy] at huv
      exact ⟨a, ⟨ha, hay⟩, hu, hux, ha, hay, Or.inr ⟨huv, hxa⟩⟩
    · exact ⟨v, ⟨hv, hvy⟩, hu, hux, hv, hvy, Or.inl huv⟩
  · intro v ⟨hv, hvy⟩
    obtain ⟨u, hu, huv⟩ := r2 v hv
    by_cases hux : u = x
    · have hbx : b ≠ x := by
        intro hbx
        rw [hbx] at hby
        rw [hux] at huv
        exact hvy (r3 x v y huv hby)
      rw [hux] at huv
      exact ⟨b, ⟨hb, hbx⟩, hb, hbx, hv, hvy, Or.inr ⟨hby, huv⟩⟩
    · exact ⟨u, ⟨hu, hux⟩, hu, hux, hv, hvy, Or.inl huv⟩
  · intro u v w ⟨_, _, _, hvy, h⟩ ⟨_, _, _, hwy, h'⟩
    rcases h with hr | ⟨huy, hxv⟩ <;> rcases h' with hr' | ⟨huy', hxw⟩
    · exact r3 u v w hr hr'
    · exact absurd (r3 u v y hr huy') hvy
    · exact absurd (r3 u w y hr' huy) hwy
    · exact r3 x v w hxv hxw
  · intro u w v ⟨_, hux, _, _, h⟩ ⟨_, hwx, _, _, h'⟩
    rcases h with hr | ⟨huy, hxv⟩ <;> rcases h' with hr' | ⟨hwy, hxv'⟩
    · exact r4 u w v hr hr'
    · exact absurd (r4 u x v hr hxv') hux
    · exact absurd (r4 w x v hr' hxv) hwx
    · exact r4 u w y huy hwy

/-- Lemma 4.5. Zero immediately precedes one. -/
theorem zero_pred_one : Pred zero one := by
  refine ⟨fun z => z = zero, zero, rfl, rfl, ?_⟩
  apply (hume _ _).mpr
  refine ⟨fun _ _ => False, ?_, ?_, ?_, ?_⟩
  · intro u ⟨h1, h2⟩; exact absurd h1 h2
  · intro v hv; exact hv.elim
  · intro _ _ _ h; exact h.elim
  · intro _ _ _ h; exact h.elim

/-- Equinumerosity is preserved under composition with a bijection
(used in Proposition 5.2; cf. LOG-16-a). -/
theorem equinum_comp {E : Type} (π σ : E → E)
    (hσπ : ∀ x, σ (π x) = x) (hπσ : ∀ x, π (σ x) = x)
    (F G : E → Prop) (h : Equinum F G) :
    Equinum (fun z => F (π z)) (fun z => G (π z)) := by
  obtain ⟨R, r1, r2, r3, r4⟩ := h
  refine ⟨fun u v => R (π u) (π v), ?_, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨y, hy, hr⟩ := r1 (π u) hu
    refine ⟨σ y, ?_, ?_⟩ <;> simp only [hπσ] <;> assumption
  · intro v hv
    obtain ⟨x, hx, hr⟩ := r2 (π v) hv
    refine ⟨σ x, ?_, ?_⟩ <;> simp only [hπσ] <;> assumption
  · intro u v w h h'
    have := r3 _ _ _ h h'
    rw [← hσπ v, ← hσπ w, this]
  · intro u v w h h'
    have := r4 _ _ _ h h'
    rw [← hσπ u, ← hσπ v, this]

/-- Proposition 5.2 (transport). If `op` satisfies Hume's principle on a
domain, so does its transport along any permutation `π` (with inverse
`σ`): the condition Hume's principle imposes on the number operator is
permutation invariant. -/
theorem hp_transport {E : Type} (op : (E → Prop) → E) (hop : HPAbstractor op)
    (π σ : E → E) (hσπ : ∀ x, σ (π x) = x) (hπσ : ∀ x, π (σ x) = x) :
    HPAbstractor (fun F => π (op (fun z => F (π z)))) := by
  intro F G
  constructor
  · intro h
    have h' : op (fun z => F (π z)) = op (fun z => G (π z)) := by
      have h0 : π (op (fun z => F (π z))) = π (op (fun z => G (π z))) := h
      have h1 := congrArg σ h0
      rw [hσπ, hσπ] at h1
      exact h1
    have e := equinum_comp σ π hπσ hσπ _ _ ((hop _ _).mp h')
    have hF : (fun z => F (π (σ z))) = F := funext fun z => by rw [hπσ]
    have hG : (fun z => G (π (σ z))) = G := funext fun z => by rw [hπσ]
    rw [hF, hG] at e
    exact e
  · intro h
    have := (hop _ _).mpr (equinum_comp π σ hσπ hπσ F G h)
    simp only [this]

/-- Proposition 5.3 (uniqueness up to relabeling). Any two operators on one
domain that satisfy Hume's principle differ by a relabeling that is one-one
on the numbers. -/
theorem hp_unique {E : Type} (op op' : (E → Prop) → E)
    (hop : HPAbstractor op) (hop' : HPAbstractor op') :
    ∃ h : E → E, (∀ F, op' F = h (op F)) ∧
      (∀ F G, h (op F) = h (op G) → op F = op G) := by
  let h : E → E := fun d => op' (Classical.epsilon (fun F => op F = d))
  have spec : ∀ F, op (Classical.epsilon (fun G => op G = op F)) = op F :=
    fun F => Classical.epsilon_spec (p := fun G => op G = op F) ⟨F, rfl⟩
  have key : ∀ F, op' F = h (op F) := fun F =>
    (hop' _ _).mpr ((hop _ _).mp (spec F).symm)
  refine ⟨h, key, fun F G e => ?_⟩
  rw [← key, ← key] at e
  exact (hop _ _).mpr ((hop' _ _).mp e)

/-- Proposition 7.1. Basic Law V is inconsistent: on no domain does any
operator identify exactly the coextensive concepts. -/
theorem basic_law_V_inconsistent {E : Type} (ext : (E → Prop) → E) :
    ¬ ∀ F G : E → Prop, ext F = ext G ↔ ∀ x, F x ↔ G x := by
  intro blv
  let R : E → Prop := fun x => ∃ F, ext F = x ∧ ¬ F x
  have hnot : ¬ R (ext R) := by
    intro ⟨F, hF, hnF⟩
    exact hnF (((blv F R).mp hF (ext R)).mpr ⟨F, hF, hnF⟩)
  exact hnot ⟨R, rfl, hnot⟩

end Philosophy.MTH_04

#print axioms Philosophy.MTH_04.zero_not_successor
#print axioms Philosophy.MTH_04.pred_injective
#print axioms Philosophy.MTH_04.hp_unique
#print axioms Philosophy.MTH_04.basic_law_V_inconsistent
