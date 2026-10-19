-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Literal probability normalization of an actual nonnegative radial
Lebesgue density and its exact expectation and event-mass formulas. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.NormalizedRadialMeasure
open Set MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 300000

def law (f : ℝ → ℝ) (U : Set ℝ) : Measure ℝ :=
  (volume.restrict U).withDensity (fun k => ENNReal.ofReal (f k/(∫ v in U,f v)))

theorem law_probability {f : ℝ → ℝ} {U : Set ℝ}
    (hf : IntegrableOn f U) (h0 : ∀ k,0 ≤ f k) (hZ : 0 < ∫ k in U,f k) :
    IsProbabilityMeasure (law f U) := by
  constructor
  rw [law,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal (hf.div_const _) (ae_of_all _ (fun k => div_nonneg (h0 k) hZ.le)),
    integral_div,div_self hZ.ne',ENNReal.ofReal_one]

theorem law_integral {f : ℝ → ℝ} {U : Set ℝ}
    (hf : Measurable f) (h0 : ∀ k,0 ≤ f k) (hZ : 0 < ∫ k in U,f k) (g : ℝ → ℝ) :
    (∫ k,g k ∂law f U)=(∫ k in U,g k*f k)/(∫ k in U,f k) := by
  rw [law,integral_withDensity_eq_integral_toReal_smul
    ((hf.div_const _).ennreal_ofReal) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (h0 _) hZ.le),smul_eq_mul]
  calc
    _=(∫ k in U,(g k*f k)/(∫ v in U,f v)) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun _ => by ring)
    _=_ := integral_div _ _

theorem law_real_apply {f : ℝ → ℝ} {U A : Set ℝ}
    (hf : IntegrableOn f U) (h0 : ∀ k,0 ≤ f k) (hZ : 0 < ∫ k in U,f k)
    (hA : MeasurableSet A) :
    (law f U).real A=(∫ k in U∩A,f k)/(∫ k in U,f k) := by
  rw [Measure.real,law,withDensity_apply _ hA,Measure.restrict_restrict hA]
  have hi : IntegrableOn f (U∩A) := hf.mono_set inter_subset_left
  rw [inter_comm A U,←ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
    (ae_of_all _ (fun k => div_nonneg (h0 k) hZ.le)),integral_div]
  exact ENNReal.toReal_ofReal (div_nonneg (integral_nonneg (fun k => h0 k)) hZ.le)

theorem law_ae_mem {f : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U) :
    ∀ᵐ k ∂law f U,k ∈ U :=
  (withDensity_absolutelyContinuous (volume.restrict U) _).ae_le (ae_restrict_mem hU)
end SlowEquilibration.NormalizedRadialMeasure
