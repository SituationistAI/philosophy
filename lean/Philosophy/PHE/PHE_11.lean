/-
PHE-11 · The World as Horizon of Horizons
Formalization of Theorem 3.1 and Corollaries 3.2 and 3.3.

What this file establishes. Given the excess condition on horizons
(Assumption 2.2), the existence of a horizon within which every horizon lies
(Assumption 2.4), the antisymmetry of lying-within (Assumption 2.5) and the
principle that whatever is given as an object is given within a horizon
(Assumption 2.6): the world has no horizon of its own, there is at most one
horizon of horizons, and the world is not given as an object. It does not
establish any of the assumptions, which the manuscript defends from
Husserl's descriptions of horizon-consciousness.
-/

namespace Philosophy.PHE_11

/-- Definition 2.1. Whatever can be intended: things, fields, horizons. -/
axiom Entity : Type

/-- Definition 2.1. `IsHorizon h`: `h` is a horizon. -/
axiom IsHorizon : Entity → Prop

/-- Definition 2.1. `Within x h`: `x` lies within `h`, i.e. is co-intended as
belonging to the field that `h` opens. -/
axiom Within : Entity → Entity → Prop

/-- Definition 2.1. `HorizonOf h x`: `h` is a horizon of `x`. -/
axiom HorizonOf : Entity → Entity → Prop

/-- Assumption 2.2 (excess). A horizon of `x` is a horizon, `x` lies within
it, and it does not lie within `x`. -/
axiom excess : ∀ h x, HorizonOf h x → IsHorizon h ∧ Within x h ∧ ¬ Within h x

/-- Definition 2.3. A horizon of horizons is a horizon within which every
horizon lies. -/
def HorizonOfHorizons (w : Entity) : Prop :=
  IsHorizon w ∧ ∀ h, IsHorizon h → Within h w

/-- The world. -/
axiom world : Entity

/-- Assumption 2.4. The world is a horizon of horizons. -/
axiom world_horizon : HorizonOfHorizons world

/-- Assumption 2.5. Lying-within is antisymmetric. -/
axiom antisymm : ∀ x y, Within x y → Within y x → x = y

/-- Givenness as an object (thematic givenness). -/
axiom GivenAsObject : Entity → Prop

/-- Assumption 2.6. Whatever is given as an object is given within some
horizon of it. -/
axiom object_in_horizon : ∀ x, GivenAsObject x → ∃ h, HorizonOf h x

/-- Theorem 3.1 (main result). Nothing is a horizon of the world. -/
theorem world_has_no_horizon : ¬ ∃ h, HorizonOf h world :=
  fun ⟨h, hh⟩ =>
    have e := excess h world hh
    e.2.2 (world_horizon.2 h e.1)

/-- Remark 3.4. The proof of Theorem 3.1 uses only that the world is a
horizon of horizons: no horizon of horizons has a horizon. -/
theorem no_horizon_of_hoh (w : Entity) (hw : HorizonOfHorizons w) :
    ¬ ∃ h, HorizonOf h w :=
  fun ⟨h, hh⟩ =>
    have e := excess h w hh
    e.2.2 (hw.2 h e.1)

/-- Corollary 3.2. There is at most one horizon of horizons. -/
theorem unique_hoh (w v : Entity) (hw : HorizonOfHorizons w)
    (hv : HorizonOfHorizons v) : w = v :=
  antisymm w v (hv.2 w hw.1) (hw.2 v hv.1)

/-- Corollary 3.3. The world is not given as an object. -/
theorem world_not_object : ¬ GivenAsObject world :=
  fun hg => world_has_no_horizon (object_in_horizon world hg)

end Philosophy.PHE_11

#print axioms Philosophy.PHE_11.world_has_no_horizon
#print axioms Philosophy.PHE_11.unique_hoh
#print axioms Philosophy.PHE_11.world_not_object
