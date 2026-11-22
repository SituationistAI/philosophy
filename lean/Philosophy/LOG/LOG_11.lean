/-
LOG-11 · The Surprise Examination
Formalization of Theorem 3.1 (revised version of 7 October 2026).

The students' knowledge on the morning of day n-1 is a predicate `K` on
propositions, constrained only by factivity and by closure under logical
consequence. `E1` and `E2` are the propositions that the examination is on
day n-1 and on day n. The announcement, as it bears on these two days, is
`¬ E2 ∧ (E1 → ¬ K E1)`: by Theorem 2.1 it excludes day n, and its surprise
clause applies to day n-1.

What this file establishes. Under factivity and closure, and given that the
students know the examination is on one of the two remaining days, they do not
know the announcement. No KK principle is assumed. The file does not model
the first step (Theorem 2.1), which is stated in the announcement's content.
-/

namespace Philosophy.LOG_11

/-- Theorem 3.1. The announcement is unknowable on the morning of day n-1. -/
theorem announcement_unknowable (K : Prop → Prop)
    (factive : ∀ p, K p → p)
    (closure : ∀ p q, (p → q) → K p → K q)
    (E1 E2 : Prop) (calendar : K (E1 ∨ E2)) :
    ¬ K (¬ E2 ∧ (E1 → ¬ K E1)) := by
  intro hA
  -- by closure, the students know that the examination is not on day n
  have hnot2 : K (¬ E2) := closure _ _ (fun h => h.1) hA
  -- combining with the calendar, they know it is on day n-1
  have hconj : K ((E1 ∨ E2) ∧ ¬ E2) :=
    closure _ _ (fun h => h) (closure _ _ (fun h2 => ⟨factive _ calendar, h2⟩) hnot2)
  have hk1 : K E1 := closure _ _ (fun h => h.1.resolve_right h.2) hconj
  -- by factivity, the announcement is true, so the examination is on day n-1
  have hA' := factive _ hA
  have he1 : E1 := (factive _ calendar).resolve_right hA'.1
  -- and then the surprise clause contradicts their knowledge
  exact hA'.2 he1 hk1

end Philosophy.LOG_11

#print axioms Philosophy.LOG_11.announcement_unknowable
