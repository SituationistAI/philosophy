/-
MTE-03 · The Frege-Geach Problem Solved
Formalization of Theorem 4.1, Corollaries 4.2 and 4.3, Proposition 4.4
and Proposition 6.2.

A small being-for semantics in the style of Schroeder's "Being For",
with contents drawn from Gibbard's fact-plan worlds. A fact-plan world
settles every descriptive matter and, for every act, whether to blame
for it (Definition 3.1). Sentences are built from descriptive atoms and
atoms "doing a is wrong" by negation and disjunction; conjunction and
the material conditional are defined (Definition 3.2). Each sentence has
a content, a set of fact-plan worlds (Definition 3.3). The philosophical
premises are axioms: there is a single attitude, being for, and a
sentence expresses being for its content (Assumption 3.4); a set of
states of being for is inconsistent if and only if their contents have
no fact-plan world in common (Assumptions 3.5 and 3.6). Validity is
defined as the inconsistency of accepting the premises while accepting
the negation of the conclusion (Definition 3.7).

What this file establishes. Validity so defined coincides with
consequence over fact-plan worlds (Theorem 4.1): states of being for
compose according to the logic of plans. Hence "doing a is wrong" and
"doing a is not wrong" are inconsistent (Corollary 4.2), modus ponens
and disjunctive syllogism are valid, including Geach's mixed arguments
(Corollary 4.3), and the three positions that the negation problem
distinguishes are distinct, only one of them being inconsistent with
judging a wrong (Proposition 4.4). A mixed disjunction is expressed by a
single state whose content is not a conjunction of a descriptive and a
practical content (Proposition 6.2).

What it does not establish. It does not establish that moral sentences
express states of being for, that being for is a coherent attitude, or
that its inconsistency is inherited from its contents: these are the
assumptions. It does not formalize the claim of Section 9, developed in
MTE-17, that the explicit commitments of the semantics make the view
indistinguishable from realism.
-/

namespace Philosophy.MTE_03

/-- Primitive: act types, the objects of blame. -/
axiom Act : Type

/-- Primitive: descriptive atoms. -/
axiom Fact : Type

/-- Definition 3.1. A fact-plan world settles every descriptive atom and,
for every act, whether to blame for doing it. -/
structure World where
  holds : Fact → Prop
  blame : Act → Prop

/-- Definition 3.2. Sentences. -/
inductive Sentence where
  | atom : Fact → Sentence
  | wrong : Act → Sentence
  | neg : Sentence → Sentence
  | disj : Sentence → Sentence → Sentence

open Sentence

/-- Definition 3.2 (defined connectives). -/
def conj (phi psi : Sentence) : Sentence := neg (disj (neg phi) (neg psi))
def cond (phi psi : Sentence) : Sentence := disj (neg phi) psi

/-- Definition 3.3. The content of a sentence: the fact-plan worlds at
which it is accepted. -/
def content : Sentence → World → Prop
  | atom p, w => w.holds p
  | wrong a, w => w.blame a
  | neg phi, w => ¬ content phi w
  | disj phi psi, w => content phi w ∨ content psi w

/-- Primitive: mental states. -/
axiom State : Type

/-- Primitive: being for a content (a set of fact-plan worlds). -/
axiom For : (World → Prop) → State

/-- Primitive: the state a sentence conventionally expresses. -/
axiom expresses : Sentence → State

/-- Primitive: joint inconsistency of a list of states. -/
axiom Inconsistent : List State → Prop

/-- Assumption 3.4 (Expression). Every sentence, descriptive or normative,
expresses being for its content. -/
axiom expression : ∀ phi, expresses phi = For (content phi)

/-- Assumption 3.5 (Inheritance). States of being for whose contents have
no fact-plan world in common are jointly inconsistent. -/
axiom inheritance : ∀ cs : List (World → Prop),
    (¬ ∃ w, ∀ c ∈ cs, c w) → Inconsistent (cs.map For)

/-- Assumption 3.6 (Only inheritance). States of being for are jointly
inconsistent only if their contents have no fact-plan world in common. -/
axiom only_inheritance : ∀ cs : List (World → Prop),
    Inconsistent (cs.map For) → ¬ ∃ w, ∀ c ∈ cs, c w

/-- Definition 3.7. An argument is valid if accepting its premises while
accepting the negation of its conclusion is inconsistent. -/
def Valid (G : List Sentence) (phi : Sentence) : Prop :=
  Inconsistent ((neg phi :: G).map expresses)

/-- Consequence over fact-plan worlds (the logic of plans). -/
def PlanConsequence (G : List Sentence) (phi : Sentence) : Prop :=
  ∀ w, (∀ g ∈ G, content g w) → content phi w

theorem map_expresses (L : List Sentence) :
    L.map expresses = (L.map content).map For := by
  rw [List.map_map]
  apply List.map_congr_left
  intro phi _
  exact expression phi

/-- Theorem 4.1 (main result). Validity coincides with consequence over
fact-plan worlds. -/
theorem valid_iff_plan_consequence (G : List Sentence) (phi : Sentence) :
    Valid G phi ↔ PlanConsequence G phi := by
  unfold Valid PlanConsequence
  rw [map_expresses]
  constructor
  · intro h w hG
    have hno := only_inheritance _ h
    apply Classical.byContradiction
    intro hphi
    apply hno
    refine ⟨w, ?_⟩
    intro c hc
    simp only [List.map_cons, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨g, hg, rfl⟩
    · exact hphi
    · exact hG g hg
  · intro h
    apply inheritance
    intro ⟨w, hw⟩
    have hneg : ¬ content phi w := hw (content (neg phi)) (by simp [List.map_cons])
    apply hneg
    apply h w
    intro g hg
    exact hw _ (by simp only [List.map_cons, List.mem_cons, List.mem_map]
                   exact Or.inr ⟨g, hg, rfl⟩)

/-- Corollary 4.2. Judging that doing a is wrong and judging that doing a
is not wrong are inconsistent. -/
theorem wrong_not_wrong_inconsistent (a : Act) :
    Inconsistent [expresses (wrong a), expresses (neg (wrong a))] := by
  have h := inheritance [content (wrong a), content (neg (wrong a))] (by
    intro ⟨w, hw⟩
    have h1 := hw (content (wrong a)) (by simp)
    have h2 := hw (content (neg (wrong a))) (by simp)
    exact h2 h1)
  rw [expression, expression]
  exact h

/-- Corollary 4.3 (a). Modus ponens is valid, for any premises, normative,
descriptive or mixed. -/
theorem modus_ponens (phi psi : Sentence) : Valid [phi, cond phi psi] psi := by
  rw [valid_iff_plan_consequence]
  intro w hw
  have h1 : content phi w := hw phi (by simp)
  have h2 : content (cond phi psi) w := hw _ (by simp)
  simp only [cond, content] at h2
  exact h2.resolve_left (fun h => h h1)

/-- Corollary 4.3 (b). Disjunctive syllogism is valid. -/
theorem disjunctive_syllogism (phi psi : Sentence) : Valid [disj phi psi, neg phi] psi := by
  rw [valid_iff_plan_consequence]
  intro w hw
  have h1 : content (disj phi psi) w := hw _ (by simp)
  have h2 : content (neg phi) w := hw _ (by simp)
  simp only [content] at h1 h2
  exact h1.resolve_left h2

/-- Geach's argument: if lying is wrong, getting one's brother to lie is
wrong; lying is wrong; so getting one's brother to lie is wrong. -/
theorem geach (lying getting : Act) :
    Valid [wrong lying, cond (wrong lying) (wrong getting)] (wrong getting) :=
  modus_ponens _ _

/-- The fact-plan world at which everything holds and everything is blamed. -/
def blameAll : World := ⟨fun _ => True, fun _ => True⟩

/-- Proposition 4.4. Let b be the act of refraining from a, distinct from
a as an object of blame. Then judging a wrong is inconsistent with judging
a not wrong, but consistent with judging b wrong; and the two judgments
"a is not wrong" and "b is wrong" have different contents. -/
theorem negation_positions (a b : Act) :
    Inconsistent [expresses (wrong a), expresses (neg (wrong a))] ∧
    ¬ Inconsistent [expresses (wrong a), expresses (wrong b)] ∧
    content (neg (wrong a)) ≠ content (wrong b) := by
  refine ⟨wrong_not_wrong_inconsistent a, ?_, ?_⟩
  · intro h
    rw [expression, expression] at h
    have h' := only_inheritance [content (wrong a), content (wrong b)] h
    apply h'
    refine ⟨blameAll, ?_⟩
    intro c hc
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact trivial
  · intro h
    have h1 : content (neg (wrong a)) blameAll = content (wrong b) blameAll := by rw [h]
    simp only [content, blameAll] at h1
    exact (cast h1.symm trivial) trivial

/-- A content is practical if it depends only on the plan component, and
descriptive if it depends only on the fact component. -/
def Descriptive (c : World → Prop) : Prop :=
  ∀ w v, w.holds = v.holds → (c w ↔ c v)
def Practical (c : World → Prop) : Prop :=
  ∀ w v, w.blame = v.blame → (c w ↔ c v)

/-- Proposition 6.2. The content of the mixed disjunction "p, or doing a
is wrong" is not the conjunction of a descriptive and a practical
content. -/
theorem mixed_not_factored (p : Fact) (a : Act) :
    ¬ ∃ d e, Descriptive d ∧ Practical e ∧
      ∀ w, content (disj (atom p) (wrong a)) w ↔ (d w ∧ e w) := by
  intro ⟨d, e, hd, he, h⟩
  let w1 : World := ⟨fun _ => True, fun _ => False⟩
  let w2 : World := ⟨fun _ => False, fun _ => True⟩
  let w3 : World := ⟨fun _ => False, fun _ => False⟩
  have h1 : d w1 ∧ e w1 := (h w1).mp (Or.inl trivial)
  have h2 : d w2 ∧ e w2 := (h w2).mp (Or.inr trivial)
  have h3 : ¬ (d w3 ∧ e w3) := fun h3 => by
    have := (h w3).mpr h3
    simp only [content, w3] at this
    exact this.elim id id
  apply h3
  constructor
  · exact (hd w2 w3 rfl).mp h2.1
  · exact (he w1 w3 rfl).mp h1.2

end Philosophy.MTE_03

#print axioms Philosophy.MTE_03.valid_iff_plan_consequence
#print axioms Philosophy.MTE_03.modus_ponens
#print axioms Philosophy.MTE_03.negation_positions
#print axioms Philosophy.MTE_03.mixed_not_factored
