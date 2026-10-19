-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceWeightedDefectCauchy
public import SlowEquilibration.ConditionedEntranceWeightedGradientDefectCauchy
public import SlowEquilibration.ConditionedEntranceResolventEnergy

/-! Final weighted-energy absorption for the two literal commutator
integrals. The raw equation and moment inequalities remain visible as
premises; both commutator estimates and the absorption are proved here. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem weighted_energy_absorption_of_integral_moments
    {E ι : Type*} [MeasurableSpace E] [Fintype ι]
    (ν : Measure E) (k F U : E → ℝ) (a b : ι → E → ℝ)
    (hk : Measurable k) (hF : Measurable F) (hU : Measurable U)
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i))
    (hFlo : ∀ᵐ z ∂ν, 1 ≤ F z)
    (hUb : ∀ᵐ z ∂ν, 0 ≤ U z ∧ U z ≤ 1)
    (hKint : Integrable (fun z => k z^2 * (F z - 1)) ν)
    (hJint : Integrable (fun z => k z^2 *
      (∑ i, (a i z)^2 / F z)) ν)
    (hAint : Integrable (fun z => F z * U z^2) ν)
    (hBint : Integrable (fun z => F z * (∑ i, (b i z)^2)) ν)
    {lam ε J H R : ℝ} (hlam : 0 < lam) (hε : 0 ≤ ε)
    (hH : 0 ≤ H) (hJ : 0 ≤ J)
    (hKsmall : (∫ z, k z^2 * (F z - 1) ∂ν) ≤ 2*ε)
    (hJsmall : (∫ z, k z^2 *
      (∑ i, (a i z)^2 / F z) ∂ν) ≤ 2*ε*J)
    (hFisher : J ≤ lam*H)
    (hraw :
      (∫ z, F z * (∑ i, (b i z)^2) ∂ν) + lam/2 *
        (∫ z, F z * U z^2 ∂ν) ≤ lam*R + lam/2 *
        |∫ z, k z * (F z-1) * U z^2 ∂ν| +
        |∫ z, k z * U z * (∑ i, a i z * b i z) ∂ν|) :
    (∫ z, F z * (∑ i, (b i z)^2) ∂ν)/lam ≤
      2*R+ε+2*ε*H := by
  let A := ∫ z, F z * U z^2 ∂ν
  let B := ∫ z, F z * (∑ i, (b i z)^2) ∂ν
  let K := ∫ z, k z^2 * (F z-1) ∂ν
  let J₂ := ∫ z, k z^2 * (∑ i, (a i z)^2 / F z) ∂ν
  have hA : 0 ≤ A := by
    apply integral_nonneg_of_ae
    filter_upwards [hFlo] with z hz
    exact mul_nonneg (by linarith) (sq_nonneg _)
  have hB : 0 ≤ B := by
    apply integral_nonneg_of_ae
    filter_upwards [hFlo] with z hz
    exact mul_nonneg (by linarith)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hK := weighted_defect_square_commutator_cauchy ν k F U
    hk.aestronglyMeasurable hF.aestronglyMeasurable hU.aestronglyMeasurable
    hFlo hUb hKint hAint
  have hUabs : ∀ᵐ z ∂ν, |U z| ≤ 1 := hUb.mono (fun z hz => by
    rw [abs_of_nonneg hz.1]; exact hz.2)
  have hC := weighted_gradient_defect_cauchy ν k F U a b
    hk hF hU ha hb hFlo hUabs hJint hBint
  have hK' : |∫ z, k z * (F z-1) * U z^2 ∂ν| ≤
      Real.sqrt (2*ε*A) := by
    apply hK.trans (Real.sqrt_le_sqrt ?_)
    exact mul_le_mul_of_nonneg_right hKsmall hA
  have hC' : |∫ z, k z * U z * (∑ i, a i z * b i z) ∂ν| ≤
      Real.sqrt (2*ε*J*B) := by
    apply hC.trans (Real.sqrt_le_sqrt ?_)
    exact mul_le_mul_of_nonneg_right hJsmall hB
  have he : B+lam/2*A ≤ lam*R+lam/2*Real.sqrt (2*ε*A)+
      Real.sqrt (2*ε*J*B) := by
    have hz := mul_le_mul_of_nonneg_left hK' (by positivity : 0 ≤ lam/2)
    dsimp only [A,B] at *
    linarith
  exact resolvent_weighted_energy_bound hlam hA hB hε hJ hH hFisher he

end SlowEquilibration.ConditionedEntrance
