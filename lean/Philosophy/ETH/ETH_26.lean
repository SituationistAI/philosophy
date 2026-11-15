/-
ETH-26 · Punishment as Communication
Formalization of Theorem 3.3 and its corollaries.

A punishment is represented by its profile: the amount of hard treatment
imposed in each period (Definition 2.1). Punishment is justified, on the
communicative account, when it communicates censure of the offence and the
offender has reason to accept the censure it expresses (Definition 2.4).
The philosophical premises are axioms: censure the offender has reason to
accept never exceeds, in cumulative magnitude, a fixed multiple of the
seriousness of the wrong (Assumption 2.5, accuracy); censure that is
communicated reaches at some time the seriousness of the wrong (Assumption
2.6, seriousness); and the scale is at least one (Assumption 2.7).

What this file establishes. Justified punishment is bounded above and below
by the seriousness of the wrong (Theorem 3.3 (a), (b)); it terminates, so
that a time comes after which no further hard treatment is imposed and
reconciliation is not foreclosed (Theorem 3.3 (c), via Lemma 3.2); endless
punishment is never justified (Corollary 3.4); conduct that wrongs no one
warrants no hard treatment (Corollary 3.5); and the band the theorem
defines is non-empty for every offence (Proposition 3.6).

What it does not establish. It does not establish the communicative
account itself, nor Assumptions 2.5 and 2.6, which are defended in the
manuscript; nor does it establish that any particular punishment is
justified, since Communicates and ReasonToAccept are primitives.
-/

namespace Philosophy.ETH_26

/-- Offences. -/
axiom Offence : Type

/-- The seriousness of the wrong done in an offence, on a discrete scale. -/
axiom wrong : Offence → Nat

/-- Definition 2.1. A punishment profile: hard treatment imposed in each
period. -/
abbrev Profile := Nat → Nat

/-- Definition 2.1. Cumulative hard treatment over the first `n` periods. -/
def total (p : Profile) : Nat → Nat
  | 0 => 0
  | n + 1 => total p n + p n

/-- Definition 2.2. A profile terminates if, after some period, no further
hard treatment is imposed. -/
def Terminates (p : Profile) : Prop := ∃ N, ∀ i, N ≤ i → p i = 0

/-- Definition 2.3. A profile is endless if it imposes some hard treatment
in every period. -/
def Endless (p : Profile) : Prop := ∀ i, 1 ≤ p i

/-- `Communicates o p`: the profile `p` communicates censure of `o`. -/
axiom Communicates : Offence → Profile → Prop

/-- `ReasonToAccept o p`: the offender has reason to accept the censure that
`p` expresses for `o`. -/
axiom ReasonToAccept : Offence → Profile → Prop

/-- Definition 2.4. Justified punishment on the communicative account. -/
def Justified (o : Offence) (p : Profile) : Prop :=
  Communicates o p ∧ ReasonToAccept o p

/-- The proportionality scale. -/
axiom scale : Nat

/-- Assumption 2.5 (accuracy). Censure the offender has reason to accept
never exceeds, cumulatively, `scale` times the seriousness of the wrong. -/
axiom accuracy : ∀ o p, ReasonToAccept o p → ∀ n, total p n ≤ scale * wrong o

/-- Assumption 2.6 (seriousness). Communicated censure reaches, at some
time, the seriousness of the wrong. -/
axiom seriousness : ∀ o p, Communicates o p → ∃ n, wrong o ≤ total p n

/-- Assumption 2.7. The scale is at least one. -/
axiom scale_pos : 1 ≤ scale

/-- Lemma 3.1. Cumulative hard treatment is monotone. -/
theorem total_mono (p : Profile) {m n : Nat} (h : m ≤ n) :
    total p m ≤ total p n := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ k ih =>
    by_cases hm : m ≤ k
    · have := ih hm
      show total p m ≤ total p k + p k
      omega
    · have : m = k + 1 := by omega
      subst this; exact Nat.le_refl _

/-- Lemma 3.2. A profile whose cumulative hard treatment is bounded
terminates. -/
theorem bounded_terminates (p : Profile) (B : Nat)
    (hB : ∀ n, total p n ≤ B) : Terminates p := by
  apply Classical.byContradiction
  intro hnot
  have key : ∀ N, ∃ i, N ≤ i ∧ p i ≠ 0 := fun N =>
    Classical.byContradiction fun hN =>
      hnot ⟨N, fun i hi => Classical.byContradiction fun hpi => hN ⟨i, hi, hpi⟩⟩
  have grow : ∀ m, ∃ n, m ≤ total p n := by
    intro m
    induction m with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨i, hi, hpi⟩ := key n
      have hmono := total_mono p hi
      refine ⟨i + 1, ?_⟩
      show k + 1 ≤ total p i + p i
      omega
  obtain ⟨n, hn⟩ := grow (B + 1)
  have := hB n
  omega

/-- Theorem 3.3 (main result). Justified punishment is (a) bounded above by
`scale` times the wrong, (b) reaches the wrong at some time, and (c)
terminates. -/
theorem justified_bounded (o : Offence) (p : Profile) (h : Justified o p) :
    (∀ n, total p n ≤ scale * wrong o) ∧
    (∃ n, wrong o ≤ total p n) ∧
    Terminates p :=
  ⟨accuracy o p h.2, seriousness o p h.1,
   bounded_terminates p (scale * wrong o) (accuracy o p h.2)⟩

/-- Corollary 3.4. Endless punishment expresses no censure the offender has
reason to accept, and so is never justified. -/
theorem endless_unjustified (o : Offence) (p : Profile) (hE : Endless p) :
    ¬ ReasonToAccept o p ∧ ¬ Justified o p := by
  have hR : ¬ ReasonToAccept o p := by
    intro h
    obtain ⟨N, hN⟩ := bounded_terminates p (scale * wrong o) (accuracy o p h)
    have h1 := hE N
    have h0 := hN N (Nat.le_refl N)
    omega
  exact ⟨hR, fun h => hR h.2⟩
/-- Corollary 3.5. Where there is no wrong, justified punishment imposes no
hard treatment. -/
theorem no_wrong_no_treatment (o : Offence) (p : Profile)
    (h : Justified o p) (h0 : wrong o = 0) : ∀ i, p i = 0 := by
  intro i
  have hb := (justified_bounded o p h).1 (i + 1)
  rw [h0, Nat.mul_zero] at hb
  have hmono := total_mono p (Nat.le_succ i)
  show p i = 0
  have : total p (i + 1) = total p i + p i := rfl
  omega

/-- The profile imposing the whole measure in the first period. -/
def single (w : Nat) : Profile := fun i => if i = 0 then w else 0

/-- Proposition 3.6. For every offence, some terminating profile lies within
the band of Theorem 3.3: it reaches the wrong and never exceeds `scale`
times it. -/
theorem band_nonempty (o : Offence) :
    Terminates (single (wrong o)) ∧
    (∃ n, wrong o ≤ total (single (wrong o)) n) ∧
    (∀ n, total (single (wrong o)) n ≤ scale * wrong o) := by
  have hle : wrong o ≤ scale * wrong o := by
    have := Nat.mul_le_mul_right (wrong o) scale_pos
    rw [Nat.one_mul] at this
    exact this
  have htot : ∀ n, total (single (wrong o)) (n + 1) = wrong o := by
    intro n
    induction n with
    | zero => simp [total, single]
    | succ k ih =>
      show total (single (wrong o)) (k + 1) + single (wrong o) (k + 1) = wrong o
      rw [ih]; simp [single]
  refine ⟨⟨1, fun i hi => ?_⟩, ⟨1, ?_⟩, fun n => ?_⟩
  · simp [single]; omega
  · rw [htot 0]; exact Nat.le_refl _
  · cases n with
    | zero => exact Nat.zero_le _
    | succ k => rw [htot k]; exact hle

end Philosophy.ETH_26

#print axioms Philosophy.ETH_26.justified_bounded
#print axioms Philosophy.ETH_26.endless_unjustified
