/-
LNG-02 · Causal Reference With Descriptive Backup
Formalization of Lemmas 4.1–4.3, Theorem 4.4, Proposition 4.5,
Lemma 4.6 and Corollary 4.7.

A naming practice is represented by what its two components deliver: the
object, if any, that the causal component determines (Definition 3.3) and
the object, if any, that uniquely satisfies the descriptive component
(Definition 3.4). The hybrid rule (Definition 3.5) follows the causal
component when it determines an object and the descriptive component
otherwise.

What this file establishes. Every reference rule that selects one of the
two components according to which of them determines an object (Principles
P1 and P2, stated as a hypothesis) and that gives the verdicts of the Goedel,
Feynman and Madagascar cases (Principle P3, stated as hypotheses) agrees with
the hybrid rule on every practice; the hybrid rule meets these conditions;
and reference is preserved along any stretch of reference-preserving links.
It does not establish the case verdicts, the principles, or that any given
chain is intact; these are defended in the manuscript.
-/

namespace Philosophy.LNG_02

/-- Candidate referents. -/
axiom Obj : Type

/-- Definitions 3.3 and 3.4, in summary form. A practice is represented by
the object its causal component determines, if any, and the object that
uniquely satisfies its descriptive component, if any. -/
structure Practice where
  causal : Option Obj
  desc : Option Obj

/-- Definition 3.5. The hybrid rule: causal reference with descriptive
backup. -/
def hybrid (p : Practice) : Option Obj :=
  match p.causal with
  | some o => some o
  | none => p.desc

/-- The two sources of reference (Principle P1). -/
inductive Source where
  | causal
  | descriptive

/-- The referent a practice receives when a rule follows a given source. -/
def follow : Source → Practice → Option Obj
  | .causal, p => p.causal
  | .descriptive, p => p.desc

/-- Principles P1 (selection) and P2 (invariance): the rule follows one of the
two components, and which one it follows depends only on which components
determine an object. -/
def ShapeRule (R : Practice → Option Obj) : Prop :=
  ∃ sel : Bool → Bool → Source,
    ∀ p, R p = follow (sel p.causal.isSome p.desc.isSome) p

/-- Goedel, Schmidt, Feynman and the island of Madagascar. -/
axiom goedel : Obj
axiom schmidt : Obj
axiom feynman : Obj
axiom island : Obj

/-- Assumption 3.6. Goedel is not Schmidt. -/
axiom goedel_ne_schmidt : goedel ≠ schmidt

/-- The three cases of Principle P3. -/
noncomputable def goedelCase : Practice := ⟨some goedel, some schmidt⟩
noncomputable def feynmanCase : Practice := ⟨some feynman, none⟩
noncomputable def madagascarCase : Practice := ⟨none, some island⟩

/-- Lemma 4.1. When both components determine an object, a rule meeting
P1, P2 and the Goedel verdict follows the causal component. -/
theorem lemma_4_1 (sel : Bool → Bool → Source)
    (h : follow (sel true true) goedelCase = some goedel) :
    sel true true = .causal := by
  cases hs : sel true true
  · rfl
  · rw [hs] at h
    simp [follow, goedelCase] at h
    exact absurd h.symm goedel_ne_schmidt

/-- Lemma 4.2. When only the causal component determines an object, the
Feynman verdict forces the rule to follow it. -/
theorem lemma_4_2 (sel : Bool → Bool → Source)
    (h : follow (sel true false) feynmanCase = some feynman) :
    sel true false = .causal := by
  cases hs : sel true false
  · rfl
  · rw [hs] at h; simp [follow, feynmanCase] at h

/-- Lemma 4.3. When only the descriptive component determines an object, the
Madagascar verdict forces the rule to follow it. -/
theorem lemma_4_3 (sel : Bool → Bool → Source)
    (h : follow (sel false true) madagascarCase = some island) :
    sel false true = .descriptive := by
  cases hs : sel false true
  · rw [hs] at h; simp [follow, madagascarCase] at h
  · rfl

/-- Theorem 4.4 (uniqueness). Every rule satisfying P1–P3 assigns to every
practice the referent the hybrid rule assigns. -/
theorem uniqueness (R : Practice → Option Obj) (shape : ShapeRule R)
    (hg : R goedelCase = some goedel)
    (hf : R feynmanCase = some feynman)
    (hm : R madagascarCase = some island) :
    ∀ p, R p = hybrid p := by
  obtain ⟨sel, hsel⟩ := shape
  have g := lemma_4_1 sel (by rw [← hg, hsel]; rfl)
  have f := lemma_4_2 sel (by rw [← hf, hsel]; rfl)
  have m := lemma_4_3 sel (by rw [← hm, hsel]; rfl)
  intro p
  rw [hsel p]
  obtain ⟨c, d⟩ := p
  cases c <;> cases d <;> simp [g, f, m, follow, hybrid]
  cases sel false false <;> rfl

/-- Proposition 4.5 (adequacy). The hybrid rule satisfies P1–P3. -/
theorem adequacy :
    ShapeRule hybrid ∧ hybrid goedelCase = some goedel ∧
      hybrid feynmanCase = some feynman ∧ hybrid madagascarCase = some island := by
  refine ⟨⟨fun c _ => if c then .causal else .descriptive, ?_⟩, rfl, rfl, rfl⟩
  intro ⟨c, d⟩
  cases c <;> rfl

/-- Lemma 4.6 (transmission). If every link from stage k to stage k + n is
reference-preserving, the use at stage k + n refers to what the use at
stage k refers to. -/
theorem transmission (ref : Nat → Option Obj) (Pres : Nat → Prop)
    (link : ∀ i, Pres i → ref (i + 1) = ref i) (k : Nat) :
    ∀ n, (∀ i, k ≤ i → i < k + n → Pres i) → ref (k + n) = ref k := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hall
    have h1 : ref (k + n) = ref k := ih (fun i h1 h2 => hall i h1 (by omega))
    have h2 := link (k + n) (hall (k + n) (by omega) (by omega))
    rw [show k + (n + 1) = k + n + 1 by omega, h2, h1]

/-- Corollary 4.7 (break). If the causal component fails at stage k, so that
the use at k refers by its descriptive component to d, and every later link
is reference-preserving, every later use refers to d. -/
theorem after_break (ref : Nat → Option Obj) (Pres : Nat → Prop)
    (link : ∀ i, Pres i → ref (i + 1) = ref i) (k : Nat) (d : Obj)
    (hk : ref k = hybrid ⟨none, some d⟩)
    (hall : ∀ i, k ≤ i → Pres i) :
    ∀ n, ref (k + n) = some d := by
  intro n
  rw [transmission ref Pres link k n (fun i h1 _ => hall i h1), hk]
  rfl

end Philosophy.LNG_02

#print axioms Philosophy.LNG_02.uniqueness
#print axioms Philosophy.LNG_02.adequacy
#print axioms Philosophy.LNG_02.after_break
