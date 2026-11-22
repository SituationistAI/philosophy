/-
TSM-04 · Time Travel and the Grandfather Paradox
Formalization of the grandfather model of Section 2 and of Theorems 3.2 and
3.3 and Proposition 3.4.

The model has three exogenous facts (whether the traveller tries to kill her
grandfather on arrival, whether the circumstances are such that an attempt
would succeed, whether the adult traveller decides to depart) and one loop
variable (whether she departs, which by the dependencies of the model is
whether she arrives). Given a value of the loop variable, the dependencies of
Definition 2.5 fix the rest of the course of events, and in particular fix
whether she departs. By Definition 2.6 a history is consistent when the value
it assigns to the loop variable is the value the dependencies return: a fixed
point of the loop map.

What this file establishes. (i) There is a consistent history in which the
traveller arrives in the past and tries to kill her grandfather (Theorem 3.2).
(ii) In every consistent history in which she arrives, the grandfather is not
killed, and if she tries, the circumstances are unfavorable (Theorem 3.3).
(iii) The setting in which she tries, the circumstances favor her and she
decides to depart has no consistent history at all (Proposition 3.4).

What it does not establish. The dependencies of Definition 2.5 and the
fixed-point condition of Definition 2.6 (Principle P1 of the manuscript) are
definitions here, not derived: the module checks the combinatorial core of
the argument, not the claim that consistent loops are metaphysically
possible, nor anything about physical possibility.
-/

namespace Philosophy.TSM_04

/-- Definition 2.5 (exogenous facts). `tries`: the traveller tries to kill her
grandfather on arrival. `favorable`: the circumstances are such that the
attempt, if made, succeeds. `decides`: the adult traveller, if she exists,
decides to depart. -/
structure Setting where
  tries : Bool
  favorable : Bool
  decides : Bool

/-- Definition 2.5 (course of events). -/
structure Course where
  arrives : Bool
  killed : Bool
  born : Bool
  departs : Bool

/-- Definition 2.5 (dependencies). Given the setting and a value `d` of the
loop variable: she arrives iff `d`; the grandfather is killed iff she arrives,
tries and the circumstances favor her; she is born iff he is not killed; she
departs iff she is born and decides to depart. -/
def course (s : Setting) (d : Bool) : Course :=
  let killed := d && s.tries && s.favorable
  { arrives := d
    killed := killed
    born := !killed
    departs := !killed && s.decides }

/-- Definition 2.5 (loop map). -/
def loop (s : Setting) (d : Bool) : Bool := (course s d).departs

/-- Definition 2.6 (consistent history; Principle P1). A value of the loop
variable is consistent when it is a fixed point of the loop map. -/
def Consistent (s : Setting) (d : Bool) : Prop := loop s d = d

/-- Theorem 3.2 (consistency). There is a consistent history in which the
traveller arrives in the past and tries to kill her grandfather. -/
theorem consistency :
    ∃ s d, Consistent s d ∧ (course s d).arrives = true ∧ s.tries = true :=
  ⟨⟨true, false, true⟩, true, rfl, rfl, rfl⟩

/-- Theorem 3.3 (failure). In every consistent history in which the traveller
arrives, her grandfather is not killed; if she tries, the circumstances are
unfavorable. -/
theorem failure (s : Setting) (d : Bool) (hc : Consistent s d)
    (ha : (course s d).arrives = true) :
    (course s d).killed = false ∧ (s.tries = true → s.favorable = false) := by
  cases s with
  | mk t f c =>
    cases d <;> cases t <;> cases f <;> cases c <;>
      simp_all [Consistent, loop, course]

/-- Proposition 3.4 (the paradoxical setting is unrealized). If she tries,
the circumstances favor her and she decides to depart, no value of the loop
variable is consistent. -/
theorem paradox_unrealized (s : Setting) (ht : s.tries = true)
    (hf : s.favorable = true) (hd : s.decides = true) :
    ¬ ∃ d, Consistent s d := by
  intro ⟨d, hc⟩
  cases s with
  | mk t f c =>
    simp only at ht hf hd
    subst ht hf hd
    cases d <;> simp [Consistent, loop, course] at hc

end Philosophy.TSM_04

#print axioms Philosophy.TSM_04.consistency
#print axioms Philosophy.TSM_04.failure
#print axioms Philosophy.TSM_04.paradox_unrealized
