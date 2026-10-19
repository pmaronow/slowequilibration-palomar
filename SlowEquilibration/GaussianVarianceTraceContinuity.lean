-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianVariancePressureQuadraticResponse
public import SlowEquilibration.GaussianPerturbationThermal

@[expose] public section
noncomputable section

namespace SlowEquilibration.GaussianVarianceTraceContinuity

open Set Filter MeasureTheory GaussianSpinInterpolation
open GaussianSpinComparison GaussianPerturbationParameter
open GaussianPerturbationSelfAveraging GaussianPerturbationResponse
open GaussianVariancePressureQuadraticResponse
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

/-- The genuine selected-coordinate Gibbs variance is continuous in its
Gaussian amplitude at each fixed disorder realization. -/
theorem coordinateVariance_continuous_amplitude
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (w : EuclideanSpace ℝ ι) (i : ι) :
    Continuous (fun s => coordinateVariance ν L label s w i) := by
  let ρ := coordinateObservable L i
  have hρ : Measurable ρ := coordinateObservable_measurable L hL i
  have hbρ := (coordinateObservable_bound ν L hb i).and hb
  have hbρ₂ : ∀ᵐ v ∂ν, |(ρ v)^2| ≤ K^2 ∧ ‖L v‖ ≤ K := by
    filter_upwards [hbρ] with v hv
    exact ⟨by simpa only [abs_pow,sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) hK).mpr hv.1,hv.2⟩
  have hcOp : Continuous (fun s => parameterOperator label s w) :=
    (show Differentiable ℝ (fun s => parameterOperator label s w) from
      fun s => (parameterOperator_hasDerivAt label w s).differentiableAt).continuous
  have hc1 : Continuous (fun s => expectation ν ρ (parameterLinear L label s) w) := by
    change Continuous (fun s => expectation ν ρ L (parameterOperator label s w))
    exact (expectation_contDiff ν ρ L hρ hL hK hK hbρ).continuous.comp hcOp
  have hc2 : Continuous (fun s => expectation ν (fun v => (ρ v)^2)
      (parameterLinear L label s) w) := by
    change Continuous (fun s => expectation ν (fun v => (ρ v)^2) L
      (parameterOperator label s w))
    exact (expectation_contDiff ν (fun v => (ρ v)^2) L (hρ.pow_const 2)
      hL (sq_nonneg K) hK hbρ₂).continuous.comp hcOp
  have heq : (fun s => coordinateVariance ν L label s w i) =
      fun s => expectation ν (fun v => (ρ v)^2) (parameterLinear L label s) w-
        (expectation ν ρ (parameterLinear L label s) w)^2 :=
    funext fun s => coordinateVariance_eq ν L hL hK hb label s w i
  rw [heq]
  exact hc2.sub (hc1.pow 2)

/-- The Gaussian-averaged variance trace is continuous at the unperturbed
physical model. This discharges the continuity premise of the finite
variance-direction response theorem. -/
theorem varianceTraceMean_continuous
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) :
    Continuous (fun s => ∫ w, varianceTrace ν L label s w
      ∂SYK.standardGaussianMeasureOnEuclidean ι) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply continuousAt_of_dominated (bound := fun _ => (Fintype.card ι : ℝ)*K^2)
  · apply Eventually.of_forall
    intro u
    have hi : Integrable (fun w => varianceTrace ν L label u w)
        (SYK.standardGaussianMeasureOnEuclidean ι) := by
      unfold varianceTrace
      exact integrable_finsetSum Finset.univ (fun i _ => by
        by_cases h : label i=true
        · simpa only [h, ite_true] using
            coordinateVariance_gaussian_integrable ν L hL hK hb label u i
        · simp [h])
    exact hi.aestronglyMeasurable
  · exact .of_forall fun u => .of_forall fun w => by
      rw [Real.norm_eq_abs,abs_of_nonneg (by
        unfold varianceTrace
        exact Finset.sum_nonneg fun i _ => by
          split_ifs
          · exact (coordinateVariance_mem_Icc ν L hL hK hb label u w i).1
          · exact le_refl 0)]
      unfold varianceTrace
      calc
        _ ≤ ∑ i : ι, K^2 := by
          apply Finset.sum_le_sum
          intro i hi
          split_ifs
          · exact (coordinateVariance_mem_Icc ν L hL hK hb label u w i).2
          · exact sq_nonneg K
        _ = (Fintype.card ι : ℝ)*K^2 := by simp
  · exact integrable_const _
  · exact .of_forall fun w => by
      have hc : Continuous (fun u => varianceTrace ν L label u w) := by
        unfold varianceTrace
        apply continuous_finsetSum
        intro i hi
        by_cases h : label i=true
        · simpa only [h,ite_true] using
            coordinateVariance_continuous_amplitude ν L hL hK hb label w i
        · simp only [h]
          exact continuous_const
      exact hc.continuousAt

/-- Unconditional finite Gaussian variance-pressure response, expressed
through its true selected-coordinate Gibbs variance trace. -/
theorem parameterMean_quadratic_response_tendsto_unconditional
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) :
    Tendsto (fun s =>
      (parameterMean ν L label s-parameterMean ν L label 0)/s^2)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((∫ w, varianceTrace ν L label 0 w
        ∂SYK.standardGaussianMeasureOnEuclidean ι)/2)) :=
  parameterMean_quadratic_response_tendsto ν L hL hK hb label
    (varianceTraceMean_continuous ν L hL hK hb label).continuousAt

end SlowEquilibration.GaussianVarianceTraceContinuity
