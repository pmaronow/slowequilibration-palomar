-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceTiltCommutator

/-! Actual integral reduction of the square-test generator term to the
zero-order Gibbs defect. This retains half the weighted square energy. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
namespace SlowEquilibration.ConditionedEntrance
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {E : Type*} [MeasurableSpace E]

theorem squareCommutator_integral_lower (μ : Measure E) (θ : ℝ) (hθ : 0≤θ)
    (F₀ F U w : E→ℝ) (hF₀ : ∀ᵐ x ∂μ,1≤F₀ x)
    (hZ : Integrable (fun x => Real.exp (-w x)*(θ*(F₀ x-F x))*(U x)^2) μ)
    (hA : Integrable (fun x => F x*(U x)^2) μ)
    (hK : Integrable (fun x => tiltDefect w x*(F x-1)*(U x)^2) μ) :
    θ/2*(∫ x,F x*(U x)^2 ∂μ)+θ/2*(∫ x,tiltDefect w x*(F x-1)*(U x)^2 ∂μ)≤
      (1/2 : ℝ)*(∫ x,Real.exp (-w x)*(θ*(F₀ x-F x))*(U x)^2 ∂μ)+
        θ*(∫ x,F x*(U x)^2 ∂μ) := by
  have hp : ∀ᵐ x ∂μ,
      θ/2*(F x*(U x)^2)+θ/2*(tiltDefect w x*(F x-1)*(U x)^2)≤
        (1/2 : ℝ)*(Real.exp (-w x)*(θ*(F₀ x-F x))*(U x)^2)+θ*(F x*(U x)^2) := by
    filter_upwards [hF₀] with x hx
    apply sub_nonneg.mp
    have hh : 0≤θ/2*(Real.exp (-w x)*(F₀ x-1)+1)*(U x)^2 := by positivity
    convert hh using 1
    unfold tiltDefect
    ring
  have hi := integral_mono_ae ((hA.const_mul (θ/2)).add (hK.const_mul (θ/2)))
    ((hZ.const_mul (1/2 : ℝ)).add (hA.const_mul θ)) hp
  simp only [Pi.add_apply] at hi
  rw [integral_add (hA.const_mul (θ/2)) (hK.const_mul (θ/2)),
    integral_add (hZ.const_mul (1/2 : ℝ)) (hA.const_mul θ),
    integral_const_mul,integral_const_mul,integral_const_mul,integral_const_mul] at hi
  exact hi

theorem squareCommutator_energy_reduction (μ : Measure E) (θ : ℝ) (hθ : 0≤θ)
    (F₀ F U w : E→ℝ) (hF₀ : ∀ᵐ x ∂μ,1≤F₀ x)
    (hZ : Integrable (fun x => Real.exp (-w x)*(θ*(F₀ x-F x))*(U x)^2) μ)
    (hA : Integrable (fun x => F x*(U x)^2) μ)
    (hK : Integrable (fun x => tiltDefect w x*(F x-1)*(U x)^2) μ)
    (B C K R : ℝ) (hK0 : 0≤K)
    (he : B+(1/2 : ℝ)*(∫ x,Real.exp (-w x)*(θ*(F₀ x-F x))*(U x)^2 ∂μ)+C+K+
      θ*(∫ x,F x*(U x)^2 ∂μ)≤R) :
    B+θ/2*(∫ x,F x*(U x)^2 ∂μ)≤R+
      θ/2*|∫ x,tiltDefect w x*(F x-1)*(U x)^2 ∂μ|+|C| := by
  have hl := squareCommutator_integral_lower μ θ hθ F₀ F U w hF₀ hZ hA hK
  have hc := neg_le_abs C
  have hk := mul_le_mul_of_nonneg_left
    (neg_le_abs (∫ x,tiltDefect w x*(F x-1)*(U x)^2 ∂μ)) (by positivity : 0≤θ/2)
  linarith

end SlowEquilibration.ConditionedEntrance
