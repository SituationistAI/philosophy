/-
TSM-01 · On the Reality of Time
Formalization of the logical skeleton of the manuscript.

Part I (McTaggart). Worlds, their moments, absolute (monadic) presentness and
the reality of time are primitives. The incoherence premise is an axiom in its
formal core: absolute presentness, being incompatible with pastness and
futurity, is had by at most one moment of a world (Assumption 3.6). A changing
A-series is one in which the present is at more than one moment
(Definition 4.3). The reality of time in the actual world is an axiom
(Assumption 5.1), resting on the evidence for its causal and metrical
structure.

Part II (the B-series). A branching frame is a strict partial order whose
predecessors of any moment are linearly ordered (Definition 6.1); histories
are maximal chains (Definition 6.2); settledness of a tenseless proposition
at a moment is truth (falsity) on every history through it (Definition 6.4).
The moment-relative A-assignment is defined from the earlier-than relation
(Definition 4.5).

What this file establishes. No world contains a changing A-series
(Theorem 4.4); given that time is real, the bridge premise "time requires a
changing A-series" is false (Theorem 5.3). The moment-relative A-assignment
recovers the earlier-than order exactly (Proposition 4.6). In every
branching frame every history through a later moment passes through each
earlier one (Lemma 6.5), so settledness is monotone along every history
(Theorem 6.6), and conversely monotonicity fails wherever a history through
a moment omits an earlier moment (Proposition 6.11); truth relative to a
history is bivalent while settledness is
not: in the three-moment fork "it will be that p" is open at the root
(Proposition 6.7).

What it does not establish. It does not establish the incoherence premise,
the reality of time, or the identification of the B-series with the causal
and metrical structure of spacetime (Principle P2); and it does not
reproduce the exhaustive enumeration of the appendices, which is carried out
by the generator distributed with the manuscript.
-/

namespace Philosophy.TSM_01

/-! ## Part I: McTaggart's argument and its inversion -/

/-- Worlds. -/
axiom World : Type

/-- The moments of a world. -/
axiom Mom : World → Type

/-- Definition 3.2. Absolute (monadic, unrelativized) presentness: the
A-determination "present" as the A-theorist takes it, a property a moment has
simpliciter. -/
axiom Present : (w : World) → Mom w → Prop

/-- Assumption 3.6 (Incoherence, formal core). The A-determinations are
incompatible, so absolute presentness is had by at most one moment of a
world: a second present moment would be past or future relative to the first
and so have incompatible determinations. -/
axiom present_unique : ∀ (w : World) (x y : Mom w), Present w x → Present w y → x = y

/-- Definition 4.3. A changing A-series: the present is at more than one
moment (every event is, at some stage, present). -/
def ChangingASeries (w : World) : Prop :=
  ∃ x y : Mom w, x ≠ y ∧ Present w x ∧ Present w y

/-- Theorem 4.4. No world contains a changing A-series. -/
theorem no_changing_A_series (w : World) : ¬ ChangingASeries w :=
  fun ⟨x, y, hne, hx, hy⟩ => hne (present_unique w x y hx hy)

/-- Time is real in a world: it contains a temporal order. -/
axiom TimeReal : World → Prop

/-- The actual world. -/
axiom actual : World

/-- Assumption 5.1. Time is real in the actual world: the evidence for its
causal and metrical structure is evidence for an order of earlier and later. -/
axiom time_real_actual : TimeReal actual

/-- Definition 5.2. McTaggart's bridge: there is no time without a changing
A-series (the conjunction of Assumptions 3.4 and 3.5). -/
def Bridge : Prop := ∀ w, TimeReal w → ChangingASeries w

/-- Theorem 5.3 (the inversion). If time is real in some world, the bridge
is false; in particular, since time is real, the bridge is false. -/
theorem bridge_fails_if_time_real (h : ∃ w, TimeReal w) : ¬ Bridge :=
  fun hb => match h with
  | ⟨w, hw⟩ => no_changing_A_series w (hb w hw)

theorem bridge_fails : ¬ Bridge :=
  bridge_fails_if_time_real ⟨actual, time_real_actual⟩

/-! ## Part II: branching frames, histories and settledness -/

/-- Definition 6.1. A branching frame: moments under a strict order of
earlier-than in which the predecessors of each moment are linearly ordered. -/
structure Frame where
  M : Type
  lt : M → M → Prop
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ a b c, lt a b → lt b c → lt a c
  backlin : ∀ a b c, lt a c → lt b c → lt a b ∨ a = b ∨ lt b a

variable {F : Frame}

/-- Comparability under earlier-than. -/
def Frame.comp (F : Frame) (x y : F.M) : Prop := F.lt x y ∨ x = y ∨ F.lt y x

/-- Definition 6.2. A history: a maximal chain of moments. -/
structure History (F : Frame) where
  mem : F.M → Prop
  chain : ∀ x y, mem x → mem y → F.comp x y
  maximal : ∀ y, (∀ x, mem x → F.comp y x) → mem y

/-- Lemma 6.5. Every history through a moment passes through every earlier
moment. -/
theorem past_closed (h : History F) {m m' : F.M} (hlt : F.lt m m')
    (hm' : h.mem m') : h.mem m := by
  apply h.maximal m
  intro x hx
  rcases h.chain m' x hm' hx with h1 | h1 | h1
  · exact Or.inl (F.trans m m' x hlt h1)
  · subst h1; exact Or.inl hlt
  · exact F.backlin m x m' hlt h1

/-- Definition 6.4. A tenseless proposition (true or false relative to each
history) is settled true (settled false) at `m` if it is true (false)
relative to every history through `m`; it is open at `m` otherwise. -/
def SettledTrue (phi : History F → Prop) (m : F.M) : Prop := ∀ h : History F, h.mem m → phi h
def SettledFalse (phi : History F → Prop) (m : F.M) : Prop := ∀ h : History F, h.mem m → ¬ phi h
def Open (phi : History F → Prop) (m : F.M) : Prop := ¬ SettledTrue phi m ∧ ¬ SettledFalse phi m

/-- Theorem 6.6 (monotonicity of settledness). What is settled at a moment
is settled, with the same value, at every later moment. -/
theorem settled_monotone (phi : History F → Prop) {m m' : F.M} (hlt : F.lt m m') :
    (SettledTrue phi m → SettledTrue phi m') ∧ (SettledFalse phi m → SettledFalse phi m') :=
  ⟨fun hs h hm' => hs h (past_closed h hlt hm'),
   fun hs h hm' => hs h (past_closed h hlt hm')⟩

/-- Proposition 6.11 (fixity of the past requires a unique past). If a
history through `m'` omits a moment `m` earlier than `m'`, then the
proposition that the history passes through `m` is settled true at `m` but
not at `m'`: monotonicity fails. -/
theorem fixity_requires_unique_past {m m' : F.M} (h : History F)
    (hm' : h.mem m') (hm : ¬ h.mem m) :
    SettledTrue (fun k : History F => k.mem m) m ∧
    ¬ SettledTrue (fun k : History F => k.mem m) m' :=
  ⟨fun _ hk => hk, fun hs => hm (hs h hm')⟩

/-- Proposition 6.7 (a). Truth relative to a history is bivalent. -/
theorem bivalent (phi : History F → Prop) (h : History F) : phi h ∨ ¬ phi h :=
  Classical.em _

/-- "It will be that p", evaluated at `m` relative to a history. -/
def WillBe (p : F.M → Prop) (m : F.M) (h : History F) : Prop :=
  ∃ x, F.lt m x ∧ h.mem x ∧ p x

/-! The three-moment fork: moment 0 with two incomparable successors. -/

def forkLt (a b : Fin 3) : Prop := a.val = 0 ∧ b.val ≠ 0

instance : DecidableRel forkLt := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The fork (entry T3.2 of the tables). -/
def fork : Frame where
  M := Fin 3
  lt := forkLt
  irrefl := by decide
  trans := by decide
  backlin := by decide

def histMem (i : Fin 3) (x : Fin 3) : Prop := x.val = 0 ∨ x = i

instance (i : Fin 3) : DecidablePred (histMem i) :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The history through moment 1. -/
def h1 : History fork where
  mem := histMem 1
  chain := by
    show ∀ x y : Fin 3, histMem 1 x → histMem 1 y →
      (forkLt x y ∨ x = y ∨ forkLt y x)
    decide
  maximal := by
    show ∀ y : Fin 3, (∀ x : Fin 3, histMem 1 x → (forkLt y x ∨ y = x ∨ forkLt x y)) →
      histMem 1 y
    decide

/-- The history through moment 2. -/
def h2 : History fork where
  mem := histMem 2
  chain := by
    show ∀ x y : Fin 3, histMem 2 x → histMem 2 y →
      (forkLt x y ∨ x = y ∨ forkLt y x)
    decide
  maximal := by
    show ∀ y : Fin 3, (∀ x : Fin 3, histMem 2 x → (forkLt y x ∨ y = x ∨ forkLt x y)) →
      histMem 2 y
    decide

/-- p holds at moment 1 only. -/
def p1 (x : Fin 3) : Prop := x = 1

/-- Proposition 6.7 (b). Settledness is not bivalent: in the fork, "it will be
that p" is open at the root. -/
theorem fork_open : @Open fork (fun h => WillBe (F := fork) p1 (0 : Fin 3) h) (0 : Fin 3) := by
  constructor
  · intro hs
    obtain ⟨x, _, hx, hp⟩ := hs h2 (Or.inl rfl)
    have hx' : histMem 2 x := hx
    have hp' : x = (1 : Fin 3) := hp
    rw [hp'] at hx'
    exact absurd hx' (by decide)
  · intro hs
    exact hs h1 (Or.inl rfl) ⟨(1 : Fin 3), (by decide : forkLt 0 1), Or.inr rfl, rfl⟩

/-! ## The moment-relative A-assignment -/

/-- A-determinations relative to a moment: past, present, future, or on
another branch. -/
inductive ADet | past | present | future | other
  deriving DecidableEq

open Classical in
/-- Definition 4.5. The A-determination of `x` relative to moment `m`. -/
noncomputable def A (F : Frame) (m x : F.M) : ADet :=
  if x = m then .present else if F.lt x m then .past else if F.lt m x then .future else .other

/-- Proposition 4.6. The moment-relative A-assignment recovers the
earlier-than order: `x` is past relative to `m` iff `x` is earlier than `m`,
and `x` is future relative to `m` iff `m` is past relative to `x`. -/
theorem stage_order (m x : F.M) :
    (A F m x = .past ↔ F.lt x m) ∧ (A F m x = .future ↔ A F x m = .past) := by
  have asym : ∀ a b, F.lt a b → ¬ F.lt b a := fun a b hab hba => F.irrefl a (F.trans a b a hab hba)
  constructor
  · unfold A
    by_cases h1 : x = m
    · subst h1; simp [F.irrefl]
    · by_cases h2 : F.lt x m
      · simp [h1, h2]
      · by_cases h3 : F.lt m x <;> simp [h1, h2, h3]
  · unfold A
    by_cases h1 : x = m
    · subst h1; simp
    · have h1' : m ≠ x := fun e => h1 e.symm
      by_cases h2 : F.lt m x
      · simp [h1, h1', h2, asym m x h2]
      · by_cases h3 : F.lt x m <;> simp [h1, h1', h2, h3]

end Philosophy.TSM_01

#print axioms Philosophy.TSM_01.no_changing_A_series
#print axioms Philosophy.TSM_01.bridge_fails
#print axioms Philosophy.TSM_01.settled_monotone
#print axioms Philosophy.TSM_01.fixity_requires_unique_past
#print axioms Philosophy.TSM_01.fork_open
#print axioms Philosophy.TSM_01.stage_order
