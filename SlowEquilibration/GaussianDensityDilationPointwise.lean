-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianDensityDilation
public import SlowEquilibration.GaussianDensityEnergy
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! Pointwise scalar transport of the actual Gaussian observation density.
Continuity upgrades the true Lebesgue density identity at every target. -/
@[expose] public section
namespace SlowEquilibration.GaussianRegression
noncomputable section
open Function MeasureTheory
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma observationPdf_continuous (A : E →L[ℝ] F) : Continuous (observationPdf A) := by
  unfold observationPdf
  apply ENNReal.continuous_ofReal.comp
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
lemma div_smul_observation_surjective (A : E →L[ℝ] F) (hA : Surjective A)
    {c : ℝ} (hc : 0 < c) : Surjective (c⁻¹ • A) := by
  intro w
  obtain ⟨z,hz⟩:=hA (c • w)
  refine ⟨z,?_⟩
  simp only [smul_apply,hz,smul_smul,inv_mul_cancel₀ hc.ne',one_smul]

/-- Every-target Gaussian density transport, including null conditioning
scores. The Jacobian is derived from actual dimension and Haar transport. -/
theorem observationPdf_div_smul (A : E →L[ℝ] F) (hA : Surjective A)
    {c : ℝ} (hc : 0 < c) (w : F) :
    observationPdf (c⁻¹ • A) w=
      ENNReal.ofReal (c^Module.finrank ℝ F)*observationPdf A (c • w) := by
  have hScaled:=div_smul_observation_surjective A hA hc
  have hLaw : (observationLaw A).map (fun z : F=>c⁻¹ • z)=observationLaw (c⁻¹ • A) := by
    rw [observationLaw,observationLaw,Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hm:=map_withDensity_div_smul (observationPdf A) (observationPdf_measurable A) hc
  rw [← observationLaw_eq_explicit_density A hA,hLaw,
    observationLaw_eq_explicit_density _ hScaled] at hm
  have hf:=observationPdf_continuous (c⁻¹ • A)
  have hg : Continuous (fun z : F=>ENNReal.ofReal (c^Module.finrank ℝ F)*observationPdf A (c • z)) := by
    exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
      ((observationPdf_continuous A).comp (continuous_const.smul continuous_id))
  have hae:= (withDensity_eq_iff_of_sigmaFinite hf.measurable.aemeasurable hg.measurable.aemeasurable).mp hm
  exact congrFun (Measure.eq_of_ae_eq (μ:=volume) hae hf hg) w

/-- The corresponding ordinary real density formula. -/
theorem realObservationDensity_div_smul (A : E →L[ℝ] F) (hA : Surjective A)
    {c : ℝ} (hc : 0 < c) (w : F) :
    realObservationDensity (c⁻¹ • A) w=
      c^Module.finrank ℝ F*realObservationDensity A (c • w) := by
  have h:=congrArg ENNReal.toReal (observationPdf_div_smul A hA hc w)
  rw [← realObservationDensity_eq_toReal _ (div_smul_observation_surjective A hA hc),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg hc.le _),
    ← realObservationDensity_eq_toReal A hA] at h
  exact h

end
end SlowEquilibration.GaussianRegression
