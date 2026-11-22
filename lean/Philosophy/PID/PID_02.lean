/-
PID-02 · Teletransportation and Extrinsic Survival
Formalization of Theorem 3.3 and Corollary 3.4 (revised version of
7 October 2026).

A teletransportation case records whether the replica is psychologically
continuous with the original, and whether the original is destroyed before
the replica is activated. The process branches exactly when the original is
not destroyed before activation (Definition 2.2). Survival is defined by the
non-branching psychological criterion (Assumption 2.3).

What this file establishes. The timing condition of Theorem 3.3, and that
survival is extrinsic: two cases with the same relation between original and
replica receive different verdicts. It does not establish the psychological
criterion. The module uses no axioms.
-/

namespace Philosophy.PID_02

/-- A teletransportation case. -/
structure Case where
  continuous : Bool
  destroyedBeforeActivation : Bool

/-- Definition 2.2. The process branches. -/
def Branches (c : Case) : Prop := c.destroyedBeforeActivation = false

/-- Assumption 2.3. Survival as the replica. -/
def Survives (c : Case) : Prop := c.continuous = true ∧ ¬ Branches c

/-- Theorem 3.3, first half. -/
theorem survives_if_destroyed_first (c : Case)
    (hc : c.continuous = true) (hd : c.destroyedBeforeActivation = true) :
    Survives c := by
  refine ⟨hc, ?_⟩
  simp [Branches, hd]

/-- Theorem 3.3, second half. -/
theorem no_survival_if_overlap (c : Case)
    (hd : c.destroyedBeforeActivation = false) : ¬ Survives c :=
  fun ⟨_, hnb⟩ => hnb hd

/-- Corollary 3.4. Survival is extrinsic. -/
theorem extrinsic : ∃ c d : Case, c.continuous = d.continuous ∧
    Survives c ∧ ¬ Survives d :=
  ⟨⟨true, true⟩, ⟨true, false⟩, rfl,
    survives_if_destroyed_first _ rfl rfl, no_survival_if_overlap _ rfl⟩

end Philosophy.PID_02

#print axioms Philosophy.PID_02.extrinsic
