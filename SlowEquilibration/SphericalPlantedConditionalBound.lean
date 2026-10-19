-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTruncatedPartition

@[expose] public section

/-! An actual every-reference translated-disorder probability bound
integrates to the genuine joint planted probability bound. -/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem planted_measure_le_of_uniform_shift_probability {N P : ℕ} (hN : 1≤N)
    (c : Degree P → ℝ) (hc : ∀ p,0≤c p) (β : ℝ)
    {T : Set (Disorder N P × Vector N)} (hT : MeasurableSet T) {a : ℝ} (ha : 0≤a)
    (hbound : ∀ u : Vector N,‖u‖^2=(N : ℝ) →
      disorderLaw N P {J | (J+plantedShift c β u,u)∈T}≤ENNReal.ofReal a) :
    plantedLaw c β T≤ENNReal.ofReal a := by
  let : IsProbabilityMeasure (plantedLaw (N := N) c β) := plantedLaw_probability hN c hc β
  rw [← ENNReal.ofReal_toReal (measure_ne_top (plantedLaw c β) T)]
  apply ENNReal.ofReal_le_ofReal
  change (plantedLaw c β).real T≤a
  rw [plantedLaw_real_eq_shift_probability hN c hc β hT]
  calc
    _ ≤ ∫ _u : Vector N,a ∂sphereLaw N := by
      apply integral_mono_of_nonneg (.of_forall fun _ => measureReal_nonneg) (integrable_const _)
      filter_upwards [sphereLaw_support hN] with u hu
      have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound u hu)
      rwa [ENNReal.toReal_ofReal ha] at ht
    _ = a := by simp

end
end SlowEquilibration.SphericalModel
