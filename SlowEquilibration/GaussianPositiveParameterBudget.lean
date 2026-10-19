-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianPerturbationDeviationBudget
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-! Genuine uniform positive parameter averaging. Restricting the active
coefficient to [1/2,1] avoids a reciprocal singularity in the GG response. -/
namespace SlowEquilibration.GaussianPerturbationDeviation
noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal
open GaussianSpinInterpolation GaussianPerturbationParameter
  GaussianPerturbationSelfAveraging GaussianPerturbationResponse GaussianPerturbationIntegrated
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

def positiveParameterLaw : Measure ℝ := (2:ℝ≥0∞) • volume.restrict (Icc (1/2:ℝ) 1)

instance positiveParameterLaw_probability : IsProbabilityMeasure positiveParameterLaw := by
  constructor
  rw [positiveParameterLaw,Measure.smul_apply,Measure.restrict_apply MeasurableSet.univ]
  simp only [univ_inter,Real.volume_Icc,smul_eq_mul]
  rw [show (2:ℝ≥0∞)=ENNReal.ofReal (2:ℝ) by norm_num,← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem positiveParameterLaw_support : ∀ᵐ x ∂positiveParameterLaw,x∈Icc (1/2:ℝ) 1 := by
  rw [positiveParameterLaw]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

theorem positiveParameterLaw_integral (f : ℝ → ℝ) :
    (∫ x,f x ∂positiveParameterLaw)=2*(∫ x in (1/2:ℝ)..1,f x) := by
  rw [positiveParameterLaw,integral_smul_measure]
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (1/2:ℝ)≤1)]
  norm_num

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

theorem totalDeviation_positive_integral_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K a r y : ℝ} (hK : 0<K) (hb : ∀ᵐ v ∂ν,‖L v‖≤K) (ha : 0≤a)
    (label : ι → Bool)
    (hdiag : ∀ᵐ v ∂ν,(∑ i,if label i=true then
      (GaussianSpinComparison.coordinateObservable L i v)^2 else 0)≤a)
    (hr : 0<r) (hy : 0<y) (hy1 : y≤1) :
    (∫ x,totalDeviation ν L label x ∂positiveParameterLaw) ≤
      2*((a+r^2)/(2*r)+8*a*y+18*Real.exp (1/2)*K/y) := by
  rw [positiveParameterLaw_integral]
  have hi:=totalDeviation_intervalIntegrable ν L hL hK.le hb label 0 1
  have hmono : (∫ x in (1/2:ℝ)..1,totalDeviation ν L label x) ≤
      ∫ x in (0:ℝ)..1,totalDeviation ν L label x := by
    rw [intervalIntegral.integral_of_le (by norm_num : (1/2:ℝ)≤1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
    apply setIntegral_mono_set hi.1
    · exact .of_forall fun x => totalDeviation_nonneg ν L label x
    · exact (Ioc_subset_Ioc (by norm_num : (0:ℝ)≤1/2) le_rfl).eventuallySubset
  exact mul_le_mul_of_nonneg_left
    (hmono.trans (totalDeviation_integral_le ν L hL hK hb ha label hdiag hr hy hy1)) (by norm_num)

end
end SlowEquilibration.GaussianPerturbationDeviation
