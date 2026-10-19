-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianPerturbationResponse
public import Mathlib.Analysis.Calculus.LHopital

@[expose] public section
noncomputable section

namespace SlowEquilibration.GaussianVariancePressureQuadraticResponse

open Set Filter MeasureTheory GaussianSpinInterpolation
open GaussianSpinComparison GaussianPerturbationParameter
open GaussianPerturbationSelfAveraging GaussianPerturbationResponse
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- A Gaussian amplitude response `P'(s)=s A(s)` gives the exact
infinitesimal variance response at the zero-variance boundary. -/
theorem quadratic_response_tendsto (P A : ℝ → ℝ)
    (hP : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt P (s*A s) s)
    (hPc : ContinuousAt P 0) (hAc : ContinuousAt A 0) :
    Tendsto (fun s => (P s-P 0)/s^2) (𝓝[>] (0 : ℝ))
      (𝓝 (A 0/2)) := by
  have hdiv : Tendsto (fun s => (s*A s)/(2*s)) (𝓝[>] (0 : ℝ))
      (𝓝 (A 0/2)) := by
    have hh : Tendsto (fun s => A s/2) (𝓝[>] (0 : ℝ)) (𝓝 (A 0/2)) :=
      (hAc.tendsto.mono_left nhdsWithin_le_nhds).div_const 2
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    field_simp
  apply HasDerivAt.lhopital_zero_right_on_Ioo (by norm_num : (0 : ℝ) < 1)
    (f := fun s => P s-P 0) (f' := fun s => s*A s)
    (g := fun s : ℝ => s^2) (g' := fun s => 2*s)
  · intro s hs
    exact (hP s hs).sub_const (P 0)
  · intro s hs
    convert (hasDerivAt_pow 2 s) using 1; ring
  · intro s hs
    exact mul_ne_zero (by norm_num) (ne_of_gt hs.1)
  · have hh : Tendsto (fun s => P s-P 0) (𝓝[>] (0 : ℝ)) (𝓝 (P 0-P 0)) :=
      (hPc.tendsto.mono_left nhdsWithin_le_nhds).sub_const (P 0)
    simpa only [sub_self] using hh
  · have hh : Tendsto (fun s : ℝ => s^2) (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ)^2)) :=
      ((continuousAt_id.pow 2).tendsto.mono_left nhdsWithin_le_nhds)
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hh
  · exact hdiv

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

/-- For an actual finite Gaussian spin system, the pressure's quadratic
amplitude coefficient is half its true Gibbs variance trace at zero. The
trace-continuity premise is proved separately from bounded features. -/
theorem parameterMean_quadratic_response_tendsto
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool)
    (htrace : ContinuousAt
      (fun s => ∫ w, varianceTrace ν L label s w
        ∂SYK.standardGaussianMeasureOnEuclidean ι) 0) :
    Tendsto (fun s =>
      (parameterMean ν L label s-parameterMean ν L label 0)/s^2)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((∫ w, varianceTrace ν L label 0 w
        ∂SYK.standardGaussianMeasureOnEuclidean ι)/2)) := by
  apply quadratic_response_tendsto (parameterMean ν L label)
    (fun s => ∫ w, varianceTrace ν L label s w
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ?_ ?_ htrace
  · intro s hs
    have hd := parameterMean_hasDerivAt ν L hL hK hb label s
    change HasDerivAt (parameterMean ν L label) (meanScore ν L label s) s at hd
    rw [meanScore_response ν L hL hK hb label s] at hd
    exact hd
  · exact (parameterMean_hasDerivAt ν L hL hK hb label 0).continuousAt

end SlowEquilibration.GaussianVariancePressureQuadraticResponse
