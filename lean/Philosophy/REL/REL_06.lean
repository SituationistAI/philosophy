/-
REL-06 · Pascal's Wager Under Bounded Utilities
Formalization of Proposition 3.2, Theorem 4.1, Corollary 4.2 and
Proposition 4.3.

Probabilities are natural numbers in units of `1/N`; utilities are natural
numbers. Infinite utility, for Section 3, is modelled by an extended type
with a top element.

What this file establishes. (1) With an infinite reward, every option that
gives the reward positive probability has infinite expected utility, so the
wager cannot discriminate between committing, a mixed strategy, or
committing to a rival god (Proposition 3.2). (2) With bounded utilities,
commitment has greater expected utility than abstention exactly when the
credence-weighted gain exceeds the credence-weighted cost (Theorem 4.1);
with negligible credence the wager fails (Corollary 4.2). (3) Among rival
gods with the same bounded stakes, expected utility favours the one with the
higher credence, and gods of credence at most `e` contribute at most `e * B`
(Proposition 4.3).

What it does not establish. What anyone's credence in God is, or that the
options are acts rather than beliefs (Section 5 of the manuscript).
-/

namespace Philosophy.REL_06

/-! ## Unbounded utilities (Section 3) -/

/-- Extended utilities: finite or infinite. -/
inductive XU
  | fin (n : Nat)
  | inf
  deriving DecidableEq

/-- Weighting an extended utility by a probability weight `q`. -/
def scale (q : Nat) : XU → XU
  | .fin n => .fin (q * n)
  | .inf => if q = 0 then .fin 0 else .inf

/-- Sum of extended utilities. -/
def add : XU → XU → XU
  | .fin a, .fin b => .fin (a + b)
  | _, _ => .inf

/-- Definition 3.1. Expected utility of an option that yields the infinite
reward with weight `q` and a finite utility `u` with weight `r`. -/
def xEU (q r u : Nat) : XU := add (scale q .inf) (scale r (.fin u))

/-- Proposition 3.2 (Hájek). Every option that gives the infinite reward any
positive weight has infinite expected utility, whatever its other outcomes:
committing (weight `p`), a mixed strategy (weight `p * s` for a positive
chance `s` of coming to commit) and commitment to a rival god (weight `p'`)
all tie. -/
theorem infinite_ties (q r u : Nat) (hq : 0 < q) : xEU q r u = .inf := by
  unfold xEU scale add
  have : q ≠ 0 := Nat.pos_iff_ne_zero.mp hq
  simp [this]

theorem mixed_ties (p s r r' u u' : Nat) (hp : 0 < p) (hs : 0 < s) :
    xEU (p * s) r u = xEU p r' u' :=
  by rw [infinite_ties _ _ _ (Nat.mul_pos hp hs), infinite_ties _ _ _ hp]

/-! ## Bounded utilities (Section 4) -/

/-- Definition 2.1 (the wager): credence `p` (in units of `1/N`, `p ≤ N`);
utilities of committing and abstaining if God exists (`gc`, `gn`) and if not
(`nc`, `nn`). -/
def EU (N p a b : Nat) : Nat := p * a + (N - p) * b

/-- Theorem 4.1 (threshold). If committing is no worse if God exists and no
better if God does not, it has the greater expected utility iff the
credence-weighted gain exceeds the credence-weighted cost. -/
theorem threshold (N p gc gn nc nn : Nat) (h1 : gn ≤ gc) (h2 : nc ≤ nn) :
    EU N p gn nn < EU N p gc nc ↔ (N - p) * (nn - nc) < p * (gc - gn) := by
  unfold EU
  have e1 : p * (gc - gn) + p * gn = p * gc := by
    rw [← Nat.mul_add, Nat.sub_add_cancel h1]
  have e2 : (N - p) * (nn - nc) + (N - p) * nc = (N - p) * nn := by
    rw [← Nat.mul_add, Nat.sub_add_cancel h2]
  omega

/-- Corollary 4.2 (negligible credence). If the gain is bounded by `B` and
`p * B` does not exceed the weighted cost, commitment is not favoured. -/
theorem negligible (N p g c B : Nat) (hg : g ≤ B)
    (h : p * B ≤ (N - p) * c) : ¬ (N - p) * c < p * g := by
  have : p * g ≤ p * B := Nat.mul_le_mul_left p hg
  omega

/-- Proposition 4.3 (many gods), first part. Two rival gods with the same
bounded gain `g > 0`: committing to the more credible one has the greater
expected gain. -/
theorem many_gods (p1 p2 g : Nat) (hp : p2 < p1) (hg : 0 < g) :
    p2 * g < p1 * g := Nat.mul_lt_mul_of_pos_right hp hg

/-- Proposition 4.3, second part. Gods whose credence is at most `e`, with
stakes bounded by `B`, contribute at most `e * B` to any comparison. -/
theorem small_contribution (q e u B : Nat) (hq : q ≤ e) (hu : u ≤ B) :
    q * u ≤ e * B := Nat.mul_le_mul hq hu

end Philosophy.REL_06

#print axioms Philosophy.REL_06.infinite_ties
#print axioms Philosophy.REL_06.threshold
#print axioms Philosophy.REL_06.many_gods
