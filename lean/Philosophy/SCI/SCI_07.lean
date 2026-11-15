/-
SCI-07 · The Falsifiability Criterion Is Not Self-Refuting
Formalization of Proposition 3.1, Theorem 3.2, Proposition 3.3 and
Corollary 3.4.

A frame (Definition 2.1) has statements, a scope (the statements a criterion
governs), the falsifiable statements, the statements its proponents accept,
and a distinguished element, the criterion itself. The criterion is the norm
that every accepted statement in its scope is falsifiable (Definition 2.2).

What this file establishes. If the criterion falls within its own scope, is
accepted and is unfalsifiable, the norm is violated: this is the form of the
self-refutation charge (Proposition 3.1). If the criterion is a proposal and
not an empirical statement (Assumption 2.3), so that it lies outside its own
scope, its application to itself is vacuous and the charge has no premise to
work with (Theorem 3.2); and the position that accepts the criterion, holds
it unfalsifiable and obeys it is consistent, since it has a model
(Proposition 3.3). It does not establish that the criterion is a good one.
-/

namespace Philosophy.SCI_07

/-- Definition 2.1. A frame. -/
structure Frame where
  Stmt : Type
  scope : Stmt → Prop
  falsifiable : Stmt → Prop
  accepted : Stmt → Prop
  crit : Stmt

/-- Definition 2.2. The norm the criterion expresses: every accepted statement
in its scope is falsifiable. -/
def Norm (F : Frame) : Prop := ∀ s, F.scope s → F.accepted s → F.falsifiable s

/-- Proposition 3.1 (The form of the charge). If the criterion is within its
own scope, accepted and unfalsifiable, the norm is violated. -/
theorem charge (F : Frame) (hin : F.scope F.crit) (hacc : F.accepted F.crit)
    (hnf : ¬ F.falsifiable F.crit) : ¬ Norm F :=
  fun h => hnf (h F.crit hin hacc)

/-- Theorem 3.2. If the criterion is outside its own scope, the norm holds
exactly when it holds for every statement other than the criterion: its
verdict does not depend on whether the criterion is falsifiable. -/
theorem outside_scope (F : Frame) (hout : ¬ F.scope F.crit) :
    Norm F ↔ ∀ s, s ≠ F.crit → F.scope s → F.accepted s → F.falsifiable s := by
  constructor
  · intro h s _ hs ha; exact h s hs ha
  · intro h s hs ha
    by_cases he : s = F.crit
    · subst he; exact absurd hs hout
    · exact h s he hs ha

/-- A model: statement `true` is an empirical, falsifiable, accepted
hypothesis; statement `false` is the criterion, accepted, unfalsifiable and
not empirical. -/
def model : Frame where
  Stmt := Bool
  scope := fun s => s = true
  falsifiable := fun s => s = true
  accepted := fun _ => True
  crit := false

/-- Proposition 3.3 (Consistency). There is a frame in which the criterion is
accepted, unfalsifiable and outside its scope, and the norm holds. -/
theorem consistent :
    ∃ F : Frame, F.accepted F.crit ∧ ¬ F.falsifiable F.crit ∧
      ¬ F.scope F.crit ∧ Norm F :=
  ⟨model, trivial, Bool.noConfusion, Bool.noConfusion, fun _ hs _ => hs⟩

/-- Primitive: the frame of empirical inquiry in which the falsifiability
criterion is proposed. -/
axiom inquiry : Frame
/-- Assumption 2.3 (Proposal). The criterion is a methodological proposal, not
an empirical statement, and so lies outside the scope it governs. -/
axiom proposal : ¬ inquiry.scope inquiry.crit

/-- Corollary 3.4. In the frame of inquiry, whether the norm holds does not
depend on the criterion's own falsifiability. -/
theorem not_self_refuting :
    Norm inquiry ↔
      ∀ s, s ≠ inquiry.crit → inquiry.scope s → inquiry.accepted s →
        inquiry.falsifiable s :=
  outside_scope inquiry proposal

end Philosophy.SCI_07

#print axioms Philosophy.SCI_07.consistent
#print axioms Philosophy.SCI_07.not_self_refuting
