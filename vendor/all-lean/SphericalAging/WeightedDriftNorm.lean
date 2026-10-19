module

public import SphericalAging.WeightedItoNorm

public section

/-!
# Exponentially weighted genuine drift Volterra norm

The actual deterministic primitive, its finite-time Cauchy–Schwarz bound, and
triangular Fubini give T/(2α) in squared predictable product L² norm.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter Topology
open StochasticCalculus (PredictableProcessL2 TimeProcessL2 nonnegativeLebesgueMeasure)
open scoped NNReal ENNReal InnerProductSpace

namespace SphericalAging.WeightedDriftNorm
open WeightedPredictable WeightedItoNorm PredictableDriftTime
open FourPapersCommon.FilteredBrownian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

omit [IsProbabilityMeasure P] in
/-- Nesting the finite-horizon coefficient cut leaves an earlier primitive unchanged. -/
theorem driftVersion_prefix (U : PredictableProcessL2 F P) {T t : ℝ≥0} (ht : t ≤ T) (ω : Ω) :
    driftVersion U T t ω=driftVersion U t t ω := by
  unfold driftVersion primitive
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hsT : s ≤ T := hs.2.trans ht
  simp [cutRepresentative,predictableTimeFrame,hs.1,hs.2,hsT]

/-- The actual drift output row has its causal energy bound. -/
theorem rowEnergy_driftVolterra_le (U : PredictableProcessL2 F P) (T : ℝ≥0) :
    ∀ᵐ t ∂finiteTimeMeasure T,
      rowEnergy (driftVolterra T U) t ≤ (T : ℝ)*‖predictableTimeRestrict F t U‖^2 := by
  have hcoe := Measure.ae_ae_of_ae_prod (driftVersion_timeCut_memLp U T).coeFn_toLp
  filter_upwards [ae_restrict_of_ae hcoe,ae_restrict_mem measurableSet_Ioc] with t ht htT
  unfold rowEnergy
  change (∫ ω, (((driftVersion_timeCut_memLp U T).toLp _ : TimeProcessL2 P) (t,ω))^2 ∂P)≤_
  rw [integral_congr_ae (ht.mono (fun ω hω => congrArg (fun z : ℝ => z^2) hω))]
  simp only [FourPapersCommon.continuousAdaptedTimeCut,htT,ite_true]
  have he (ω : Ω) := driftVersion_prefix U htT.2 ω
  simp_rw [he]
  exact (RadialUniqueness.integral_sq_driftVersion_le U t).trans
    (mul_le_mul_of_nonneg_right (show (t : ℝ) ≤ T from htT.2) (sq_nonneg _))

/-- Squared weighted drift Volterra norm gain on every finite horizon. -/
theorem norm_sq_weighted_driftVolterra_le {α : ℝ} (hα : 0 < α) (T : ℝ≥0)
    (U : PredictableProcessL2 F P) :
    ‖multiply α T (driftVolterra T U)‖^2 ≤
      ((T : ℝ)/(2*α))*‖multiply α T U‖^2 := by
  rw [norm_sq_multiply]
  have hcut : ∀ᵐ t ∂nonnegativeLebesgueMeasure,
      t ∉ Ioc 0 T → rowEnergy (driftVolterra T U) t=0 := by
    have hcoe := Measure.ae_ae_of_ae_prod (driftVersion_timeCut_memLp U T).coeFn_toLp
    filter_upwards [hcoe] with t ht
    intro htT
    unfold rowEnergy
    change (∫ ω, (((driftVersion_timeCut_memLp U T).toLp _ : TimeProcessL2 P) (t,ω))^2 ∂P)=0
    rw [integral_congr_ae (ht.mono (fun ω hω => congrArg (fun z : ℝ => z^2) hω))]
    simp [FourPapersCommon.continuousAdaptedTimeCut,htT]
  have hout : Integrable (fun t : ℝ≥0 => (weight α T t)^2*rowEnergy (driftVolterra T U) t)
      nonnegativeLebesgueMeasure :=
    (rowEnergy_integrable (multiply α T (driftVolterra T U))).congr
      (weighted_rowEnergy α T (driftVolterra T U))
  have hrestrict : (∫ t, (weight α T t)^2*rowEnergy (driftVolterra T U) t ∂nonnegativeLebesgueMeasure)=
      (∫ t in Ioc (0 : ℝ≥0) T, (weight α T t)^2*rowEnergy (driftVolterra T U) t
        ∂nonnegativeLebesgueMeasure) := by
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [hcut] with t ht
    by_cases htT : t ∈ Ioc 0 T
    · simp [htT]
    · simp [htT,ht htT]
  rw [hrestrict]
  have hc : Continuous (fun t : ℝ≥0 => (T : ℝ)*Real.exp (-(2*α)*(t : ℝ))*
      ‖predictableTimeRestrict F t U‖^2) :=
    (continuous_const.mul (by fun_prop : Continuous (fun t : ℝ≥0 => Real.exp (-(2*α)*(t : ℝ))))).mul
      ((continuous_predictableTimeRestrict U).norm.pow 2)
  have hright : Integrable (fun t : ℝ≥0 => (T : ℝ)*Real.exp (-(2*α)*(t : ℝ))*
      ‖predictableTimeRestrict F t U‖^2) (finiteTimeMeasure T) := by
    apply memLp_one_iff_integrable.mp
    apply MemLp.of_bound hc.aestronglyMeasurable ((T : ℝ)*‖U‖^2)
    exact ae_of_all _ (fun t => by
      rw [Real.norm_of_nonneg (by positivity)]
      have he : Real.exp (-(2*α)*(t : ℝ)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) t.coe_nonneg
      have hn := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_predictableTimeRestrict_le F t U)
      calc
        _ ≤ (T : ℝ)*1*‖U‖^2 := by gcongr
        _ = _ := by ring)
  calc
    _ ≤ ∫ t in Ioc (0 : ℝ≥0) T, (T : ℝ)*Real.exp (-(2*α)*(t : ℝ))*
        ‖predictableTimeRestrict F t U‖^2 ∂nonnegativeLebesgueMeasure := by
      apply integral_mono_ae hout.restrict hright
      filter_upwards [rowEnergy_driftVolterra_le U T,ae_restrict_mem measurableSet_Ioc] with t ht htT
      rw [weight_sq htT.2]
      simpa only [mul_assoc,mul_comm,mul_left_comm] using
        mul_le_mul_of_nonneg_left ht (Real.exp_nonneg _)
    _ = (T : ℝ)*(∫ t in Ioc (0 : ℝ≥0) T, Real.exp (-(2*α)*(t : ℝ))*
        (∫ s in Ioc (0 : ℝ≥0) t, rowEnergy U s ∂nonnegativeLebesgueMeasure)
        ∂nonnegativeLebesgueMeasure) := by
      simp_rw [restricted_norm_sq]
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by ring)
    _ ≤ (T : ℝ)*((2*α)⁻¹*(∫ s in Ioc (0 : ℝ≥0) T, Real.exp (-(2*α)*(s : ℝ))*rowEnergy U s
        ∂nonnegativeLebesgueMeasure)) :=
      mul_le_mul_of_nonneg_left
        (WeightedVolterra.weighted_causal_integral_le (by positivity : 0 < 2*α) T (rowEnergy U)
          ((rowEnergy_integrable U).restrict) (ae_of_all _ (rowEnergy_nonnegative U))) T.coe_nonneg
    _ ≤ ((T : ℝ)/(2*α))*‖multiply α T U‖^2 := by
      rw [weighted_input_integral]
      have hn := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
        (norm_predictableTimeRestrict_le F T (multiply α T U))
      rw [div_eq_mul_inv,mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn (by positivity)) T.coe_nonneg

/-- The arbitrary-horizon weighted drift contraction gain in norm form. -/
theorem norm_weighted_driftVolterra_le {α : ℝ} (hα : 0 < α) (T : ℝ≥0)
    (U : PredictableProcessL2 F P) :
    ‖multiply α T (driftVolterra T U)‖ ≤
      Real.sqrt ((T : ℝ)/(2*α))*‖multiply α T U‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ (T : ℝ)/(2*α))]
  exact norm_sq_weighted_driftVolterra_le hα T U

/-- Difference version for the actual predictable Picard drift map. -/
theorem norm_weighted_driftVolterra_sub_le {α : ℝ} (hα : 0 < α) (T : ℝ≥0)
    (U V : PredictableProcessL2 F P) :
    ‖multiply α T (driftVolterra T U-driftVolterra T V)‖ ≤
      Real.sqrt ((T : ℝ)/(2*α))*‖multiply α T (U-V)‖ := by
  rw [← driftVolterra_sub]
  exact norm_weighted_driftVolterra_le hα T (U-V)

end SphericalAging.WeightedDriftNorm
