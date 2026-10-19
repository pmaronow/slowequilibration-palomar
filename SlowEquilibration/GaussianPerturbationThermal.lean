-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianPerturbationIntegrated
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-! # Actual thermal perturbation-variance budget

The derivative of the genuine quenched perturbation energy is the Gaussian
average of actual Gibbs thermal variance. FTC and the proved coordinate
response bound give the integrated variance budget, uniformly in the base
spin probability and dimension.
-/

namespace SlowEquilibration.GaussianPerturbationThermal
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open GaussianSpinInterpolation GaussianSpinComparison GaussianPerturbationParameter
  GaussianPerturbationSelfAveraging GaussianPerturbationResponse GaussianPerturbationIntegrated

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem gaussian_norm_sq_integrable :
    Integrable (fun w : EuclideanSpace ℝ ι => ‖w‖^2)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  apply ((SYK.integrable_exp_mul_norm (ι := ι) 1).const_mul 2).mono'
    (continuous_norm.pow 2).aestronglyMeasurable
  exact .of_forall fun w => by
    dsimp only [Pi.pow_apply]
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := Real.pow_div_factorial_le_exp ‖w‖ (norm_nonneg w) 2
    norm_num at h ⊢
    linarith

theorem parameterVariance_mem_Icc (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (w : EuclideanSpace ℝ ι) (x : ℝ) :
    parameterVariance ν L label w x ∈ Icc 0 (K^2*‖w‖^2) := by
  let d := coordinateMask label true w
  let G := gibbsMeasure ν L (parameterOperator label x w)
  have : IsProbabilityMeasure G := gibbsMeasure_probability ν L hL hb _
  have hm : Measurable (fun v => L v d) := (ContinuousLinearMap.apply ℝ ℝ d).continuous.measurable.comp hL
  have hbd : ∀ᵐ v ∂G, L v d ∈ Icc (-(K*‖w‖)) (K*‖w‖) := by
    have hρ := (directionalObservable_bound ν L hb d).mono fun v hv =>
      abs_le.mp (hv.1.trans (mul_le_mul_of_nonneg_left (coordinateMask_norm_le label true w) hK))
    exact hρ.filter_mono (gibbsMeasure_absolutelyContinuous ν L _).ae_le
  refine ⟨ProbabilityTheory.variance_nonneg _ _,?_⟩
  calc
    _ ≤ ((K*‖w‖-(-(K*‖w‖)))/2)^2 := ProbabilityTheory.variance_le_sq_of_bounded hbd hm.aemeasurable
    _ = _ := by ring

theorem parameterVariance_eq_hessian (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (w : EuclideanSpace ℝ ι) (x : ℝ) :
    parameterVariance ν L label w x = hessian ν L (parameterOperator label x w)
      (coordinateMask label true w) (coordinateMask label true w) := by
  rw [hessian_apply_covariance ν L hL hK hb]
  symm
  have hρ := (ContinuousLinearMap.apply ℝ ℝ (coordinateMask label true w)).continuous.measurable.comp hL
  simpa only [parameterVariance,pow_two] using expectation_variance ν
    (fun v => L v (coordinateMask label true w)) L hρ hL
    (directionalObservable_bound ν L hb (coordinateMask label true w)) (parameterOperator label x w)

theorem hessian_continuous (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) : Continuous (hessian ν L) :=
  (score_contDiff ν L hL hK hb).continuous_fderiv (by norm_num)

theorem parameterVariance_gaussian_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool) (x : ℝ) :
    Integrable (fun w => parameterVariance ν L label w x)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have heq : (fun w => parameterVariance ν L label w x) =
      fun w => hessian ν L (parameterOperator label x w)
        (coordinateMask label true w) (coordinateMask label true w) :=
    funext fun w => parameterVariance_eq_hessian ν L hL hK hb label w x
  have hc : Continuous (fun w => parameterVariance ν L label w x) := by
    rw [heq]
    exact (((hessian_continuous ν L hL hK hb).comp (parameterOperator label x).continuous).clm_apply
      (coordinateMask label true).continuous).clm_apply (coordinateMask label true).continuous
  apply (gaussian_norm_sq_integrable (ι := ι) |>.const_mul (K^2)).mono' hc.aestronglyMeasurable
  exact .of_forall fun w => by
    rw [Real.norm_eq_abs,abs_of_nonneg (parameterVariance_mem_Icc ν L hL hK hb label w x).1]
    exact (parameterVariance_mem_Icc ν L hL hK hb label w x).2

def meanVariance (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (x : ℝ) : ℝ :=
  ∫ w,parameterVariance ν L label w x ∂SYK.standardGaussianMeasureOnEuclidean ι

/-- Differentiation of the actual Gaussian mean energy yields the
literal averaged Gibbs thermal variance. -/
theorem meanScore_hasDerivAt (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool) (x : ℝ) :
    HasDerivAt (meanScore ν L label) (meanVariance ν L label x) x := by
  have hmeas := (parameterVariance_gaussian_integrable ν L hL hK hb label x).aestronglyMeasurable
  have hbound : ∀ᵐ w ∂SYK.standardGaussianMeasureOnEuclidean ι, ∀ y ∈ (univ : Set ℝ),
      ‖parameterVariance ν L label w y‖ ≤ K^2*‖w‖^2 := .of_forall fun w y _ => by
        rw [Real.norm_eq_abs,abs_of_nonneg (parameterVariance_mem_Icc ν L hL hK hb label w y).1]
        exact (parameterVariance_mem_Icc ν L hL hK hb label w y).2
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := SYK.standardGaussianMeasureOnEuclidean ι) (s := univ)
    (F := fun y w => parameterScore ν L label w y)
    (F' := fun y w => parameterVariance ν L label w y) (bound := fun w => K^2*‖w‖^2) (by simp)
    (.of_forall fun y => (parameterScore_gaussian_integrable ν L hL hK hb label y).aestronglyMeasurable)
    (parameterScore_gaussian_integrable ν L hL hK hb label x) hmeas hbound
    (gaussian_norm_sq_integrable (ι := ι) |>.const_mul (K^2))
    (.of_forall fun w y _ => parameterScore_hasDerivAt ν L hL hK hb label w y)).2

theorem meanVariance_continuous (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool) :
    Continuous (meanVariance ν L label) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_dominated (bound := fun w => K^2*‖w‖^2)
  · exact .of_forall fun y => (parameterVariance_gaussian_integrable ν L hL hK hb label y).aestronglyMeasurable
  · exact .of_forall fun y => .of_forall fun w => by
      rw [Real.norm_eq_abs,abs_of_nonneg (parameterVariance_mem_Icc ν L hL hK hb label w y).1]
      exact (parameterVariance_mem_Icc ν L hL hK hb label w y).2
  · exact (gaussian_norm_sq_integrable (ι := ι)).const_mul (K^2)
  · exact .of_forall fun w => by
      have heq : (fun y => parameterVariance ν L label w y) =
          fun y => hessian ν L (parameterOperator label y w)
            (coordinateMask label true w) (coordinateMask label true w) :=
        funext fun y => parameterVariance_eq_hessian ν L hL hK hb label w y
      rw [heq]
      have hz : Continuous (fun y => parameterOperator label y w) :=
        (show Differentiable ℝ (fun y => parameterOperator label y w) from
          fun y => (parameterOperator_hasDerivAt label w y).differentiableAt).continuous
      exact ((((hessian_continuous ν L hL hK hb).comp hz).clm_apply continuous_const).clm_apply
        continuous_const).continuousAt

/-- The actual thermal variance budget on the complete coefficient
interval is bounded by the true selected-coordinate diagonal. -/
theorem meanVariance_integral_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K a : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool)
    (hdiag : ∀ᵐ v ∂ν, (∑ i, if label i=true then (coordinateObservable L i v)^2 else 0) ≤ a) :
    (∫ x in (0 : ℝ)..1,meanVariance ν L label x) ≤ a := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => meanScore_hasDerivAt ν L hL hK hb label x)
    ((meanVariance_continuous ν L hL hK hb label).intervalIntegrable 0 1),
    meanScore_response ν L hL hK hb label 0,zero_mul,sub_zero]
  have h := abs_meanScore_le ν L hL hK hb label hdiag 1
  simp only [abs_one,one_mul] at h
  exact (le_abs_self _).trans h

end
end SlowEquilibration.GaussianPerturbationThermal
