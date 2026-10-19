-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SemicirclePotential
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-! Whole-line regularity of the actual semicircle logarithmic potential.
The genuine density is convolved with the locally integrable real logarithm;
there is no nonintegrability-default interpretation of the potential. -/

@[expose] public section
namespace SlowEquilibration.SemicircleWholeLine

noncomputable section
open MeasureTheory Set Function Filter Real
open SemicirclePotential
open scoped Topology ENNReal Convolution Interval
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma density_hasCompactSupport : HasCompactSupport density := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro t ht
  by_contra hI
  exact ht (density_eq_zero_outside hI)

lemma log_locallyIntegrable : LocallyIntegrable Real.log (volume : Measure ℝ) := by
  intro x
  refine ⟨Icc (x-1) (x+1),Icc_mem_nhds (by linarith) (by linarith),?_⟩
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp intervalIntegral.intervalIntegrable_log'

lemma density_neg (t : ℝ) : density (-t)=density t := by simp [density]

lemma potential_eq_convolution : potential=
    density ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] Real.log := by
  funext z
  rw [potential,integral_law]
  simp only [Real.log_abs]
  rfl

/-- Actual all-real-shift logarithmic integrability under the semicircle law. -/
theorem log_abs_integrable (z : ℝ) : Integrable (fun t => Real.log |z-t|) law := by
  have hi := density_hasCompactSupport.convolutionExists_left
    (ContinuousLinearMap.mul ℝ ℝ) density_continuous log_locallyIntegrable z
  change Integrable (fun t => density t*Real.log (z-t)) volume at hi
  rw [law,integrable_withDensity_iff density_continuous.measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  convert hi using 1
  funext t
  rw [ENNReal.toReal_ofReal (density_nonneg t),Real.log_abs]
  ring

/-- The actual logarithmic potential is continuous on the entire real line,
including its singular integrand's moving point and the spectral edges. -/
theorem potential_continuous : Continuous potential := by
  rw [potential_eq_convolution]
  exact density_hasCompactSupport.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ)
    density_continuous log_locallyIntegrable

/-- The actual semicircle logarithmic potential is even. -/
theorem potential_even (z : ℝ) : potential (-z)=potential z := by
  rw [potential,integral_law_interval,potential,integral_law_interval]
  let f := fun t : ℝ => density t*Real.log |z-t|
  calc
    _ = ∫ t in (-2:ℝ)..2,f (-t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only [f]
      rw [density_neg]
      congr 2
      rw [show -z-t=-(z-(-t)) by ring,abs_neg]
    _ = ∫ t in (-2:ℝ)..2,f t := by
      simpa only [neg_neg] using intervalIntegral.integral_comp_neg (a := (-2:ℝ)) (b := 2) f

end
end SlowEquilibration.SemicircleWholeLine
