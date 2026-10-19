module

public import SphericalAging.WeightedVolterra

public section

/-!
# Exponentially weighted genuine Itô Volterra norm

The actual Itô isometry and triangular Fubini yield a contraction gain
1/(2α) in squared predictable product L² norm on every finite horizon.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter Topology
open StochasticCalculus (PredictableProcessL2 TimeProcessL2 nonnegativeLebesgueMeasure IsBrownianMotion)
open scoped NNReal ENNReal InnerProductSpace

namespace SphericalAging.WeightedItoNorm
open WeightedPredictable PredictableItoTime
open FourPapersCommon.FilteredBrownian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {B : ℝ≥0 → Ω → ℝ}

@[expose] def rowEnergy (U : PredictableProcessL2 F P) (t : ℝ≥0) : ℝ :=
  ∫ ω, ((U : TimeProcessL2 P) (t,ω))^2 ∂P

omit [IsProbabilityMeasure P] in
theorem rowEnergy_nonnegative (U : PredictableProcessL2 F P) (t : ℝ≥0) :
    0 ≤ rowEnergy U t := integral_nonneg (fun _ω => sq_nonneg _)

theorem rowEnergy_integrable (U : PredictableProcessL2 F P) :
    Integrable (rowEnergy U) nonnegativeLebesgueMeasure :=
  (Lp.memLp (U : TimeProcessL2 P)).integrable_sq.integral_prod_left

theorem weight_sq {α : ℝ} {T t : ℝ≥0} (ht : t ≤ T) :
    (weight α T t)^2=Real.exp (-(2*α)*(t : ℝ)) := by
  unfold weight
  rw [min_eq_left ht,← Real.exp_nat_mul]
  congr 1
  ring

theorem norm_sq_multiply (α : ℝ) (T : ℝ≥0) (U : PredictableProcessL2 F P) :
    ‖multiply α T U‖^2=∫ t, (weight α T t)^2*rowEnergy U t ∂nonnegativeLebesgueMeasure := by
  have he : (fun q => ((multiply α T U : TimeProcessL2 P) q)^2)=ᵐ[
      nonnegativeLebesgueMeasure.prod P]
      (fun q => (weight α T q.1)^2*((U : TimeProcessL2 P) q)^2) := by
    filter_upwards [multiply_coeFn α T U] with q hq
    rw [hq,smul_eq_mul,mul_pow]
  have hi := (Lp.memLp (multiply α T U : TimeProcessL2 P)).integrable_sq.congr he
  rw [RadialUniqueness.predictable_norm_sq,integral_congr_ae he,integral_prod _ hi]
  simp_rw [integral_const_mul]
  rfl

omit [IsProbabilityMeasure P] in
theorem multiply_restrict (α : ℝ) (T t : ℝ≥0) (U : PredictableProcessL2 F P) :
    multiply α T (predictableTimeRestrict F t U)=predictableTimeRestrict F t (multiply α T U) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [multiply_coeFn α T (predictableTimeRestrict F t U),
    multiply_coeFn α T U,predictableTimeRestrict_coeFn F t U,
    predictableTimeRestrict_coeFn F t (multiply α T U)] with q hw hU hr hrw
  rw [hw,hrw,hr]
  by_cases hq : q.1 ∈ Ioc 0 t <;> simp [hq,predictableTimeFrame,hU]

theorem restricted_norm_sq (U : PredictableProcessL2 F P) (t : ℝ≥0) :
    ‖predictableTimeRestrict F t U‖^2=∫ s in Ioc (0 : ℝ≥0) t,
      rowEnergy U s ∂nonnegativeLebesgueMeasure := by
  have he : (fun q => ((predictableTimeRestrict F t U : TimeProcessL2 P) q)^2)=ᵐ[
      nonnegativeLebesgueMeasure.prod P]
      (fun q => if q.1 ∈ Ioc 0 t then ((U : TimeProcessL2 P) q)^2 else 0) := by
    filter_upwards [predictableTimeRestrict_coeFn F t U] with q hq
    rw [hq]
    by_cases ht : q.1 ∈ Ioc 0 t <;> simp [ht,predictableTimeFrame]
  have hi := (Lp.memLp (predictableTimeRestrict F t U : TimeProcessL2 P)).integrable_sq.congr he
  rw [RadialUniqueness.predictable_norm_sq,integral_congr_ae he,integral_prod _ hi]
  have hh (s : ℝ≥0) : (∫ ω, (if s ∈ Ioc 0 t then ((U : TimeProcessL2 P) (s,ω))^2 else 0) ∂P)=
      (Ioc (0 : ℝ≥0) t).indicator (rowEnergy U) s := by
    by_cases hs : s ∈ Ioc 0 t <;> simp [hs,rowEnergy]
  simp_rw [hh]
  exact integral_indicator measurableSet_Ioc

theorem weighted_rowEnergy (α : ℝ) (T : ℝ≥0) (U : PredictableProcessL2 F P) :
    rowEnergy (multiply α T U)=ᵐ[nonnegativeLebesgueMeasure]
      (fun t => (weight α T t)^2*rowEnergy U t) := by
  have he := Measure.ae_ae_of_ae_prod (multiply_coeFn α T U)
  filter_upwards [he] with t ht
  unfold rowEnergy
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ht] with ω hω
  rw [hω,smul_eq_mul,mul_pow]

/-- The exact weighted time integral over the horizon is a truncated input L² norm. -/
theorem weighted_input_integral (α : ℝ) (T : ℝ≥0) (U : PredictableProcessL2 F P) :
    (∫ s in Ioc (0 : ℝ≥0) T, Real.exp (-(2*α)*(s : ℝ))*rowEnergy U s
      ∂nonnegativeLebesgueMeasure)=‖predictableTimeRestrict F T (multiply α T U)‖^2 := by
  rw [restricted_norm_sq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (weighted_rowEnergy α T U),ae_restrict_mem measurableSet_Ioc] with s hs hsT
  rw [hs,weight_sq hsT.2]

/-- Fixed-time genuine Itô isometry expressed as a real causal energy integral. -/
theorem ito_norm_sq_as_causal_energy (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P)
    (U : PredictableProcessL2 F P) (t : ℝ≥0) :
    ‖naturalItoProcess hB.toIsPreBrownianReal hsm hfiltered U t‖^2=
      ∫ s in Ioc (0 : ℝ≥0) t, rowEnergy U s ∂nonnegativeLebesgueMeasure := by
  rw [norm_naturalItoProcess,restricted_norm_sq]

/-- Genuine weighted Itô output norm equals the exponentially weighted causal energy integral. -/
theorem weighted_ito_norm_sq (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P)
    (α : ℝ) (T : ℝ≥0) (U : PredictableProcessL2 F P) :
    ‖multiply α T (itoVolterra hB hsm hfiltered T U)‖^2=
      ∫ t in Ioc (0 : ℝ≥0) T, Real.exp (-(2*α)*(t : ℝ))*
        (∫ s in Ioc (0 : ℝ≥0) t, rowEnergy U s ∂nonnegativeLebesgueMeasure)
        ∂nonnegativeLebesgueMeasure := by
  rw [norm_sq_multiply]
  have hcut : rowEnergy (itoVolterra hB hsm hfiltered T U)=ᵐ[nonnegativeLebesgueMeasure]
      (Ioc (0 : ℝ≥0) T).indicator
        (fun t => ‖naturalItoProcess hB.toIsPreBrownianReal hsm hfiltered U t‖^2) := by
    have he := Measure.ae_ae_of_ae_prod (itoVersion_timeCut_memLp hB hsm hfiltered U T).coeFn_toLp
    filter_upwards [he] with t ht
    unfold rowEnergy
    have hi := integral_congr_ae (ht.mono (fun ω hω => congrArg (fun z : ℝ => z^2) hω))
    change (∫ ω, (((itoVersion_timeCut_memLp hB hsm hfiltered U T).toLp _ : TimeProcessL2 P) (t,ω))^2 ∂P)=_
    rw [hi]
    by_cases htT : t ∈ Ioc 0 T
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,htT,ite_true,indicator_of_mem]
      rw [integral_sq_toLp _ (itoVersion_memLp hB hsm hfiltered U t),itoVersion_toLp]
    · simp [FourPapersCommon.continuousAdaptedTimeCut,htT]
  rw [integral_congr_ae (hcut.mono (fun t ht => congrArg (fun z : ℝ => (weight α T t)^2*z) ht))]
  have hh : (fun t : ℝ≥0 => (weight α T t)^2*((Ioc (0 : ℝ≥0) T).indicator
      (fun t => ‖naturalItoProcess hB.toIsPreBrownianReal hsm hfiltered U t‖^2) t))=
      (Ioc (0 : ℝ≥0) T).indicator (fun t => Real.exp (-(2*α)*(t : ℝ))*
        (∫ s in Ioc (0 : ℝ≥0) t, rowEnergy U s ∂nonnegativeLebesgueMeasure)) := by
    funext t
    by_cases ht : t ∈ Ioc 0 T
    · simp only [indicator_of_mem ht,weight_sq ht.2]
      rw [ito_norm_sq_as_causal_energy hB hsm hfiltered U t]
    · simp [ht]
  rw [hh,integral_indicator measurableSet_Ioc]

/-- Squared weighted Itô Volterra norm gain on every finite horizon. -/
theorem norm_sq_weighted_itoVolterra_le (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P)
    {α : ℝ} (hα : 0 < α) (T : ℝ≥0) (U : PredictableProcessL2 F P) :
    ‖multiply α T (itoVolterra hB hsm hfiltered T U)‖^2 ≤
      (2*α)⁻¹*‖multiply α T U‖^2 := by
  rw [weighted_ito_norm_sq]
  have hh := WeightedVolterra.weighted_causal_integral_le (by positivity : 0 < 2*α) T
    (rowEnergy U) ((rowEnergy_integrable U).restrict) (ae_of_all _ (rowEnergy_nonnegative U))
  apply hh.trans
  rw [weighted_input_integral]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_predictableTimeRestrict_le F T _)

/-- The arbitrary-horizon weighted Itô contraction gain in norm form. -/
theorem norm_weighted_itoVolterra_le (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P)
    {α : ℝ} (hα : 0 < α) (T : ℝ≥0) (U : PredictableProcessL2 F P) :
    ‖multiply α T (itoVolterra hB hsm hfiltered T U)‖ ≤
      Real.sqrt ((2*α)⁻¹)*‖multiply α T U‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ (2*α)⁻¹)]
  exact norm_sq_weighted_itoVolterra_le hB hsm hfiltered hα T U

/-- Difference version for the actual predictable Picard map. -/
theorem norm_weighted_itoVolterra_sub_le (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P)
    {α : ℝ} (hα : 0 < α) (T : ℝ≥0) (U V : PredictableProcessL2 F P) :
    ‖multiply α T (itoVolterra hB hsm hfiltered T U-itoVolterra hB hsm hfiltered T V)‖ ≤
      Real.sqrt ((2*α)⁻¹)*‖multiply α T (U-V)‖ := by
  rw [← itoVolterra_sub]
  exact norm_weighted_itoVolterra_le hB hsm hfiltered hα T (U-V)

end SphericalAging.WeightedItoNorm
