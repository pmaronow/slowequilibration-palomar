-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceJointFibreEnergyIntegrability

/-! An L¹ nonnegative weighted gradient sum splits into its exact
coordinate integrals. This identifies the density used by the global
tilt with the source fibre energy defined as a sum of Gibbs integrals. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 300000

theorem weighted_gradient_density_integral_eq_sum
    {E ι : Type*} [MeasurableSpace E] [Fintype ι]
    (ν : Measure E) (F : E → ℝ) (G : ι → E → ℝ)
    (hF : Measurable F) (hG : ∀ i, Measurable (G i))
    (hF0 : ∀ᵐ z ∂ν, 0 ≤ F z)
    (hi : Integrable (fun z => F z * (∑ i, (G i z)^2)) ν) :
    (∫ z, F z * (∑ i, (G i z)^2) ∂ν) =
      ∑ i, ∫ z, F z * (G i z)^2 ∂ν := by
  have hiCoord (i : ι) : Integrable (fun z => F z * (G i z)^2) ν := by
    apply Integrable.mono_nonneg hi (by fun_prop)
    · filter_upwards [hF0] with z hz
      exact mul_nonneg hz (sq_nonneg _)
    · filter_upwards [hF0] with z hz
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun j _ => sq_nonneg (G j z)) (Finset.mem_univ i)) hz
  have hsum := integral_finsetSum Finset.univ (fun i _ => hiCoord i)
  simpa only [← Finset.mul_sum] using hsum

end SlowEquilibration.ConditionedEntrance
