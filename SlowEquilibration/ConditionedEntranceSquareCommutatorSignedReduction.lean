-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSquareCommutatorReduction

/-! Keep the sign of both physical commutators until after axis
integration. This allows the global Cauchy estimates to use the absolute
value of the integrated defect, rather than an integral of pointwise
absolute values. -/
@[expose] public section
noncomputable section
open MeasureTheory
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 300000

theorem squareCommutator_energy_reduction_signed
    {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (θ : ℝ) (hθ : 0 ≤ θ)
    (F₀ F U w : E → ℝ) (hF₀ : ∀ᵐ x ∂μ, 1 ≤ F₀ x)
    (hZ : Integrable (fun x => Real.exp (-w x) *
      (θ * (F₀ x-F x)) * (U x)^2) μ)
    (hA : Integrable (fun x => F x * (U x)^2) μ)
    (hK : Integrable (fun x => tiltDefect w x *
      (F x-1) * (U x)^2) μ)
    (B C K R : ℝ) (hK0 : 0 ≤ K)
    (he : B + (1/2 : ℝ) *
      (∫ x, Real.exp (-w x) * (θ * (F₀ x-F x)) * (U x)^2 ∂μ) +
      C + K + θ * (∫ x, F x * (U x)^2 ∂μ) ≤ R) :
    B + θ/2 * (∫ x, F x * (U x)^2 ∂μ) ≤
      R - θ/2 * (∫ x, tiltDefect w x * (F x-1) * (U x)^2 ∂μ) - C := by
  have hl := squareCommutator_integral_lower μ θ hθ F₀ F U w hF₀ hZ hA hK
  linarith

end SlowEquilibration.ConditionedEntrance
