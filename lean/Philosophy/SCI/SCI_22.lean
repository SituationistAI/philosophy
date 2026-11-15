/-
SCI-22 · The Scientific Status of Machine-Generated Results
Formalization of Propositions 3.1 and 3.2.

A body of results is a list of candidate results, each of which is true or
false and passes or fails an independent check. A check is sound for a body
of results if every result that passes is true (Definition 2.2).

What this file establishes. If the check is sound, every accepted result is
true, whatever process generated the candidates, and soundness does not
require completeness: a sound check may reject true results. It does not
establish that any particular checker is sound; that is the trust placed in
the checker's kernel and in the statement of the result.
-/

namespace Philosophy.SCI_22

/-- A candidate result. -/
structure Result where
  isTrue : Bool
  passes : Bool

/-- Definition 2.2. A check is sound on a body of results. -/
def Sound (rs : List Result) : Prop := ∀ r ∈ rs, r.passes = true → r.isTrue = true

/-- Proposition 3.1. Under a sound check, every accepted result is true,
whatever generated the candidates. -/
theorem accepted_true (rs : List Result) (h : Sound rs) :
    ∀ r ∈ rs.filter (fun r => r.passes), r.isTrue = true := by
  intro r hr
  rw [List.mem_filter] at hr
  exact h r hr.1 hr.2

/-- Proposition 3.2. Soundness does not require completeness. -/
theorem sound_incomplete :
    ∃ rs : List Result, Sound rs ∧ ∃ r ∈ rs, r.isTrue = true ∧ r.passes = false :=
  ⟨[⟨true, true⟩, ⟨true, false⟩, ⟨false, false⟩],
   by intro r hr hp; simp at hr; rcases hr with h | h | h <;> subst h <;> simp_all,
   ⟨true, false⟩, by simp, rfl, rfl⟩

end Philosophy.SCI_22

#print axioms Philosophy.SCI_22.accepted_true
