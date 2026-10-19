-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPanchenkoPressureTransport

/-! Gaussian pressure fluctuation comparison at an arbitrary unperturbed
inverse temperature. The original integrated perturbation lemma was stated
for a normalized parameter interval; the physical inverse temperature need
not lie there. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalPanchenkoArbitraryTemperature

open MeasureTheory ProbabilityTheory
open GaussianSpinInterpolation GaussianSpinComparison
open GaussianPerturbationParameter GaussianPerturbationSelfAveraging
open GaussianPerturbationIntegrated
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

/-- The genuine centered Gaussian log partition has a bound at every
temperature, with the correct linear growth in the temperature. -/
theorem parameter_fluctuation_le_any
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 < K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (x : ℝ) :
    (∫ w, |parameterMean ν L label x-parameterLogPartition ν L label w x|
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
      2*Real.exp (1/2)*(1+|x|)*K := by
  have hKx : 0 < (1+|x|)*K := mul_pos (by positivity) hK
  have hb' := parameterLinear_bound ν L hK.le hb label x
  have h := GaussianPerturbationFluctuation.logPartition_integral_abs_centered_le
    ν (parameterLinear L label x) (parameterLinear_measurable L hL label x)
    hKx hb'
  rw [← parameterLogPartition_eq ν L label x] at h
  convert h using 1
  · apply integral_congr_ae
    exact .of_forall fun w => abs_sub_comm _ _
  · ring

/-- Pointwise-in-temperature disorder fluctuations of the true Gibbs
energy are bounded by the mean derivative spread and pressure
concentration. No normalized temperature restriction is imposed. -/
theorem integral_score_fluctuation_le_any
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 < K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    energyFluctuation ν L label x ≤
      meanScore ν L label (x+y)-meanScore ν L label (x-y)+
        (2*Real.exp (1/2)*K)*
          ((1+|x+y|)+(1+|x-y|)+(1+|x|))/y := by
  let G := SYK.standardGaussianMeasureOnEuclidean ι
  let ep := fun w => |parameterMean ν L label (x+y)-parameterLogPartition ν L label w (x+y)|
  let em := fun w => |parameterMean ν L label (x-y)-parameterLogPartition ν L label w (x-y)|
  let e0 := fun w => |parameterMean ν L label x-parameterLogPartition ν L label w x|
  let spread := meanScore ν L label (x+y)-meanScore ν L label (x-y)
  have hiabs : Integrable (fun w =>
      |parameterScore ν L label w x-meanScore ν L label x|) G := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      ((parameterScore_gaussian_integrable ν L hL hK.le hb label x).sub
        (integrable_const _)).norm
  have hip : Integrable ep G := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      ((integrable_const _).sub
        (parameterLogPartition_gaussian_integrable ν L hL hK.le hb label (x+y))).norm
  have him : Integrable em G := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      ((integrable_const _).sub
        (parameterLogPartition_gaussian_integrable ν L hL hK.le hb label (x-y))).norm
  have hi0 : Integrable e0 G := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      ((integrable_const _).sub
        (parameterLogPartition_gaussian_integrable ν L hL hK.le hb label x)).norm
  have hle := integral_mono hiabs
    ((integrable_const spread).add ((hip.add him).add hi0 |>.div_const y))
    (fun w => score_fluctuation_pointwise_le ν L hL hK.le hb label w x hy)
  simp only [Pi.add_apply] at hle
  rw [integral_add (f := fun _ => spread)
      (g := fun w => (ep w+em w+e0 w)/y)
      (integrable_const spread) ((hip.add him).add hi0 |>.div_const y),
    integral_const, probReal_univ, one_smul, integral_div,
    integral_add (f := fun w => ep w+em w) (g := e0) (hip.add him) hi0,
    integral_add (f := ep) (g := em) hip him] at hle
  have hp := parameter_fluctuation_le_any ν L hL hK hb label (x+y)
  have hm := parameter_fluctuation_le_any ν L hL hK hb label (x-y)
  have h0 := parameter_fluctuation_le_any ν L hL hK hb label x
  change energyFluctuation ν L label x ≤ _
  unfold energyFluctuation
  calc
    _ ≤ spread+((∫ w, ep w ∂G)+(∫ w, em w ∂G)+(∫ w, e0 w ∂G))/y := hle
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_right _ hy.le
      nlinarith [hp, hm, h0]

end SlowEquilibration.PureCapturePhysicalPanchenkoArbitraryTemperature
