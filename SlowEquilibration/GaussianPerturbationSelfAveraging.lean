-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianPerturbationParameter
public import SlowEquilibration.GaussianPerturbationConvexity

@[expose] public section

/-! # Actual perturbation-energy self-averaging comparison

The true selected-coordinate Gaussian perturbation log-partition and its
Gaussian mean satisfy Panchenko's convex derivative comparison. Uniform
Gaussian fluctuations give a dimension-independent bound on the actual
quenched perturbation-energy fluctuations in terms of the mean derivative
spread. No self-averaging or positivity conclusion is supplied as an input.
-/

namespace SlowEquilibration.GaussianPerturbationSelfAveraging
noncomputable section
open MeasureTheory Set
open scoped Topology
open GaussianSpinInterpolation GaussianSpinComparison GaussianPerturbationParameter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

def parameterLinear (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (label : ι → Bool) (x : ℝ) :=
  fun v => (L v).comp (parameterOperator label x)

theorem parameterLinear_measurable (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hL : Measurable L) (label : ι → Bool) (x : ℝ) : Measurable (parameterLinear L label x) := by
  have hc : Continuous (fun l : EuclideanSpace ℝ ι →L[ℝ] ℝ => l.comp (parameterOperator label x)) :=
    continuous_id.clm_comp continuous_const
  exact hc.measurable.comp hL

theorem parameterLinear_bound (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool) (x : ℝ) :
    ∀ᵐ v ∂ν, ‖parameterLinear L label x v‖ ≤ (1+|x|)*K := by
  filter_upwards [hb] with v hv
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) hK)
  intro w
  exact ((L v).le_opNorm _).trans
    ((mul_le_mul hv (parameterOperator_norm_le label x w) (norm_nonneg _) hK).trans_eq (by ring))

theorem parameterLogPartition_eq (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (x : ℝ) :
    (fun w => parameterLogPartition ν L label w x) = logPartition ν (parameterLinear L label x) := rfl

def meanScore (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (x : ℝ) : ℝ :=
  ∫ w,parameterScore ν L label w x ∂SYK.standardGaussianMeasureOnEuclidean ι

theorem parameterScore_gaussian_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool) (x : ℝ) :
    Integrable (fun w => parameterScore ν L label w x)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hc : Continuous (fun w => parameterScore ν L label w x) :=
    ((score_continuous ν L hL hK hb).comp (parameterOperator label x).continuous).clm_apply
      (coordinateMask label true).continuous
  apply (gaussian_norm_integrable (ι := ι) |>.const_mul K).mono' hc.aestronglyMeasurable
  exact .of_forall fun w =>
    ((score ν L (parameterOperator label x w)).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (norm_score_le ν L hL hK hb _) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (coordinateMask_norm_le label true w) hK))

/-- Actual log-partition fluctuations remain bounded uniformly over
the selected-coordinate parameters in [-2,2]. -/
theorem parameter_fluctuation_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 < K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool)
    {x : ℝ} (hx : |x| ≤ 2) :
    (∫ w,|parameterMean ν L label x-parameterLogPartition ν L label w x|
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤ 6*Real.exp (1/2)*K := by
  have hb' : ∀ᵐ v ∂ν, ‖parameterLinear L label x v‖ ≤ 3*K :=
    (parameterLinear_bound ν L hK.le hb label x).mono fun v hv => hv.trans (by nlinarith)
  have h := GaussianPerturbationFluctuation.logPartition_integral_abs_centered_le ν
    (parameterLinear L label x) (parameterLinear_measurable L hL label x)
    (by positivity : 0 < 3*K) hb'
  rw [← parameterLogPartition_eq ν L label x] at h
  convert h using 1
  · apply integral_congr_ae
    exact .of_forall fun w => abs_sub_comm _ _
  · ring

/-- Panchenko's convex comparison specialized to the true perturbation
energy and true Gaussian mean derivative. -/
theorem score_fluctuation_pointwise_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (w : EuclideanSpace ℝ ι) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    |parameterScore ν L label w x-meanScore ν L label x| ≤
      meanScore ν L label (x+y)-meanScore ν L label (x-y)+
      (|parameterMean ν L label (x+y)-parameterLogPartition ν L label w (x+y)|+
        |parameterMean ν L label (x-y)-parameterLogPartition ν L label w (x-y)|+
        |parameterMean ν L label x-parameterLogPartition ν L label w x|)/y := by
  have hθd : Differentiable ℝ (parameterLogPartition ν L label w) :=
    fun z => (parameterLogPartition_hasDerivAt ν L hL hK hb label w z).differentiableAt
  have hψd : Differentiable ℝ (parameterMean ν L label) :=
    fun z => (parameterMean_hasDerivAt ν L hL hK hb label z).differentiableAt
  have h := GaussianPerturbationConvexity.abs_deriv_sub_le
    (parameterLogPartition ν L label w) (parameterMean ν L label)
    (parameterLogPartition_convex ν L hL hK hb label w) (parameterMean_convex ν L hL hK hb label)
    hθd hψd x hy
  rw [(parameterLogPartition_hasDerivAt ν L hL hK hb label w x).deriv,
    (parameterMean_hasDerivAt ν L hL hK hb label x).deriv,
    (parameterMean_hasDerivAt ν L hL hK hb label (x+y)).deriv,
    (parameterMean_hasDerivAt ν L hL hK hb label (x-y)).deriv] at h
  exact h

/-- Actual quenched perturbation-energy fluctuations obey the quantitative
dimension-independent convex comparison. -/
theorem integral_score_fluctuation_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 < K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) {x y : ℝ} (hy : 0 < y)
    (hx : |x| ≤ 2) (hxp : |x+y| ≤ 2) (hxm : |x-y| ≤ 2) :
    (∫ w,|parameterScore ν L label w x-meanScore ν L label x|
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
      meanScore ν L label (x+y)-meanScore ν L label (x-y)+18*Real.exp (1/2)*K/y := by
  let G := SYK.standardGaussianMeasureOnEuclidean ι
  let ep := fun w => |parameterMean ν L label (x+y)-parameterLogPartition ν L label w (x+y)|
  let em := fun w => |parameterMean ν L label (x-y)-parameterLogPartition ν L label w (x-y)|
  let e0 := fun w => |parameterMean ν L label x-parameterLogPartition ν L label w x|
  let spread := meanScore ν L label (x+y)-meanScore ν L label (x-y)
  have hiabs : Integrable (fun w => |parameterScore ν L label w x-meanScore ν L label x|) G := by
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using
      ((parameterScore_gaussian_integrable ν L hL hK.le hb label x).sub (integrable_const _)).norm
  have hip : Integrable ep G := by
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using ((integrable_const _).sub
      (parameterLogPartition_gaussian_integrable ν L hL hK.le hb label (x+y))).norm
  have him : Integrable em G := by
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using ((integrable_const _).sub
      (parameterLogPartition_gaussian_integrable ν L hL hK.le hb label (x-y))).norm
  have hi0 : Integrable e0 G := by
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using ((integrable_const _).sub
      (parameterLogPartition_gaussian_integrable ν L hL hK.le hb label x)).norm
  have hle := integral_mono hiabs ((integrable_const spread).add ((hip.add him).add hi0 |>.div_const y))
    (fun w => score_fluctuation_pointwise_le ν L hL hK.le hb label w x hy)
  simp only [Pi.add_apply] at hle
  rw [integral_add (f := fun _ => spread) (g := fun w => (ep w+em w+e0 w)/y)
      (integrable_const spread) ((hip.add him).add hi0 |>.div_const y),
    integral_const,probReal_univ,one_smul,integral_div,
    integral_add (f := fun w => ep w+em w) (g := e0) (hip.add him) hi0,
    integral_add (f := ep) (g := em) hip him] at hle
  have hp := parameter_fluctuation_le ν L hL hK hb label hxp
  have hm := parameter_fluctuation_le ν L hL hK hb label hxm
  have h0 := parameter_fluctuation_le ν L hL hK hb label hx
  calc
    _ ≤ spread+((∫ w,ep w ∂G)+(∫ w,em w ∂G)+(∫ w,e0 w ∂G))/y := hle
    _ ≤ spread+18*Real.exp (1/2)*K/y := by
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_right _ hy.le
      nlinarith [hp,hm,h0]

end
end SlowEquilibration.GaussianPerturbationSelfAveraging
