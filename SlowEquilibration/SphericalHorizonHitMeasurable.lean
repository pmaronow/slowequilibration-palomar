-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalParisiContinuousMaximum
public import SlowEquilibration.SphericalPathRotation
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! A compact-time maximum turns continuously parameterized path-hit events
into measurable sets, with no countable-time approximation at the boundary. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalHorizonHitMeasurable
open MeasureTheory SphericalParisiContinuousMaximum
open scoped NNReal
set_option autoImplicit false

theorem measurableSet_horizon_hit
    {Ω : Type*} [MeasurableSpace Ω]
    (r : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => r t ω))
    (hm : ∀ t, Measurable (r t))
    (H : ℝ≥0) (a : ℝ) :
    MeasurableSet {ω | ∃ t : ℝ≥0, t ≤ H ∧ a ≤ |r t ω|} := by
  let _ : Nonempty (SphericalRotationCovariance.PathTime H) :=
    ⟨⟨0,⟨le_rfl,bot_le⟩⟩⟩
  let f : Ω → C(SphericalRotationCovariance.PathTime H, ℝ) := fun ω =>
    ⟨fun t => |r t.1 ω|, (hc ω).abs.comp continuous_subtype_val⟩
  have hf : Measurable f := ContinuousMap.measurable_iff_eval.mpr (by
    intro t
    exact (hm t.1).abs)
  have heq : {ω | ∃ t : ℝ≥0, t ≤ H ∧ a ≤ |r t ω|} =
      {ω | a ≤ maximum (f ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t,ht,ha⟩
      exact ha.trans (le_maximum (f ω) ⟨t,⟨zero_le,ht⟩⟩)
    · intro ha
      obtain ⟨t,ht⟩ := maximum_attained (f ω)
      refine ⟨t.1,t.2.2,?_⟩
      rw [ht] at ha
      exact ha
  rw [heq]
  exact measurableSet_le measurable_const (maximum_measurable.comp hf)

end SlowEquilibration.SphericalHorizonHitMeasurable
