module

public import SphericalAging.WeightedPredictable
public import SphericalAging.RadialUniqueness
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

public section

/-! Weighted norm bounds for the actual predictable Itô and drift Volterra
operators on arbitrary finite deterministic horizons. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.WeightedVolterra
open WeightedPredictable PredictableItoTime PredictableDriftTime

theorem nnreal_Ioc_integral_eq_interval (g : ℝ≥0 → ℝ) (a b : ℝ≥0) (hab : a ≤ b) :
    (∫ s in Ioc a b, g s ∂nonnegativeLebesgueMeasure) =
      ∫ s in (a : ℝ)..(b : ℝ), g s.toNNReal := by
  have himage : ((↑) : ℝ≥0 → ℝ) '' Ioc a b = Ioc (a : ℝ) (b : ℝ) := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨by exact_mod_cast hs.1, by exact_mod_cast hs.2⟩
    · intro hx
      exact ⟨⟨x, a.coe_nonneg.trans hx.1.le⟩,
        ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩, rfl⟩
  have hmap : Measure.map ((↑) : ℝ≥0 → ℝ)
      (nonnegativeLebesgueMeasure.restrict (Ioc a b)) = volume.restrict (Ioc (a : ℝ) (b : ℝ)) := by
    rw [nonnegativeLebesgueMeasure, measurableEmbedding_nnrealCoe_iterated.restrict_comap,
      measurableEmbedding_nnrealCoe_iterated.map_comap,
      Measure.restrict_restrict measurableEmbedding_nnrealCoe_iterated.measurableSet_range,
      inter_eq_right.mpr (image_subset_range _ _), himage]
  rw [intervalIntegral.integral_of_le (show (a : ℝ) ≤ b from hab), ← hmap,
    measurableEmbedding_nnrealCoe_iterated.integral_map]
  simp only [Real.toNNReal_coe]

theorem exponential_tail_le {β : ℝ} (hβ : 0 < β) (s T : ℝ≥0) (hs : s ≤ T) :
    (∫ t in Icc s T, Real.exp (-β * (t : ℝ)) ∂nonnegativeLebesgueMeasure) ≤
      β⁻¹ * Real.exp (-β * (s : ℝ)) := by
  rw [integral_Icc_eq_integral_Ioc'
    (FourPapersCommon.FilteredBrownian.nonnegativeLebesgueMeasure_singleton s),
    nnreal_Ioc_integral_eq_interval _ s T hs]
  have hfun : (fun t : ℝ => Real.exp (-β * (t.toNNReal : ℝ))) =ᵐ[
      volume.restrict (Ioc (s : ℝ) (T : ℝ))] (fun t => Real.exp (-β * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.coe_toNNReal t (s.coe_nonneg.trans ht.1.le)]
  rw [intervalIntegral.integral_of_le (show (s : ℝ) ≤ T from hs), integral_congr_ae hfun,
    ← intervalIntegral.integral_of_le (show (s : ℝ) ≤ T from hs),
    intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hβ.ne'), integral_exp,
    smul_eq_mul]
  have hEq : (-β)⁻¹ * (Real.exp (-β * (T : ℝ)) - Real.exp (-β * (s : ℝ))) =
      β⁻¹ * Real.exp (-β * (s : ℝ)) - β⁻¹ * Real.exp (-β * (T : ℝ)) := by
    rw [inv_neg]
    ring
  rw [hEq]
  exact sub_le_self _ (mul_nonneg (inv_nonneg.mpr hβ.le) (Real.exp_pos _).le)

open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)

/-- The causal triangular exponential kernel has norm at most `1/β` in
time L¹. Both Fubini integrability and the endpoint convention are proved. -/
theorem weighted_causal_integral_le {β : ℝ} (hβ : 0 < β) (T : ℝ≥0)
    (f : ℝ≥0 → ℝ) (hf : Integrable f (finiteTimeMeasure T))
    (hnonneg : ∀ᵐ s ∂finiteTimeMeasure T, 0 ≤ f s) :
    (∫ t in Ioc (0 : ℝ≥0) T,
      Real.exp (-β * (t : ℝ)) * (∫ s in Ioc (0 : ℝ≥0) t, f s ∂nonnegativeLebesgueMeasure)
        ∂nonnegativeLebesgueMeasure) ≤
      β⁻¹ * ∫ s in Ioc (0 : ℝ≥0) T, Real.exp (-β * (s : ℝ)) * f s ∂nonnegativeLebesgueMeasure := by
  let μ := finiteTimeMeasure T
  let H : ℝ≥0 × ℝ≥0 → ℝ := fun q => if q.2 ≤ q.1 then Real.exp (-β * (q.1 : ℝ)) * f q.2 else 0
  have hμ : IsFiniteMeasure μ := inferInstance
  have hmeas : AEStronglyMeasurable H (μ.prod μ) := by
    have hc : StronglyMeasurable (fun q : ℝ≥0 × ℝ≥0 => Real.exp (-β * (q.1 : ℝ))) := by
      apply Continuous.stronglyMeasurable
      fun_prop
    have hi : AEStronglyMeasurable
        ({q : ℝ≥0 × ℝ≥0 | q.2 ≤ q.1}.indicator
          (fun q => Real.exp (-β * (q.1 : ℝ)) * f q.2)) (μ.prod μ) :=
      (hc.aestronglyMeasurable.mul (hf.comp_snd μ).aestronglyMeasurable).indicator
        (measurableSet_le measurable_snd measurable_fst)
    exact hi.congr (.of_forall (fun q => by by_cases hq : q.2 ≤ q.1 <;> simp [H, hq]))
  have hH : Integrable H (μ.prod μ) := by
    apply (hf.norm.comp_snd μ).mono' hmeas
    exact .of_forall (fun q => by
      by_cases hq : q.2 ≤ q.1
      · simp only [H, hq, ite_true, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
        have he : Real.exp (-β * (q.1 : ℝ)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ.le) q.1.coe_nonneg
        simpa only [one_mul] using mul_le_mul_of_nonneg_right he (norm_nonneg (f q.2))
      · simp [H, hq])
  have hinner (t : ℝ≥0) (ht : t ∈ Ioc 0 T) :
      (∫ s, H (t,s) ∂μ) = Real.exp (-β * (t : ℝ)) *
        ∫ s in Ioc (0 : ℝ≥0) t, f s ∂nonnegativeLebesgueMeasure := by
    rw [← integral_const_mul]
    dsimp only [μ, finiteTimeMeasure]
    rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact .of_forall (fun s => by
      by_cases hs0 : 0 < s
      · by_cases hst : s ≤ t
        · simp [H, hs0, hst, hst.trans ht.2]
        · simp [H, hs0, hst]
      · simp [H, hs0])
  have htail (s : ℝ≥0) (hs : s ∈ Ioc 0 T) :
      (∫ t, H (t,s) ∂μ) = f s *
        ∫ t in Icc s T, Real.exp (-β * (t : ℝ)) ∂nonnegativeLebesgueMeasure := by
    rw [← integral_const_mul]
    dsimp only [μ, finiteTimeMeasure]
    rw [← integral_indicator measurableSet_Ioc,
      ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    exact .of_forall (fun t => by
      by_cases hst : s ≤ t
      · by_cases ht : t ≤ T
        · simp [H, hst, ht, hs.1.trans_le hst, mul_comm]
        · simp [H, hst, ht]
      · simp [H, hst])
  have hright : Integrable (fun s : ℝ≥0 => β⁻¹ * (Real.exp (-β * (s : ℝ)) * f s)) μ := by
    apply (hf.const_mul β⁻¹).norm.mono'
      (((by fun_prop : Continuous (fun s : ℝ≥0 => Real.exp (-β * (s : ℝ)))).aestronglyMeasurable.mul
        hf.aestronglyMeasurable).const_mul _)
    exact .of_forall (fun s => by
      change ‖β⁻¹ * (Real.exp (-β * (s : ℝ)) * f s)‖ ≤ ‖β⁻¹ * f s‖
      rw [norm_mul, norm_mul]
      have he : Real.exp (-β * (s : ℝ)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ.le) s.coe_nonneg
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      simpa only [norm_mul, one_mul, mul_assoc] using
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (norm_nonneg _)) (norm_nonneg (β⁻¹)))
  calc
    _ = ∫ t, ∫ s, H (t,s) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (hinner t ht).symm
    _ = ∫ s, ∫ t, H (t,s) ∂μ ∂μ := integral_integral_swap hH
    _ ≤ ∫ s, β⁻¹ * (Real.exp (-β * (s : ℝ)) * f s) ∂μ := by
      apply integral_mono_ae hH.integral_prod_right hright
      filter_upwards [hnonneg, ae_restrict_mem measurableSet_Ioc] with s hsnon hs
      rw [htail s hs]
      have ht := mul_le_mul_of_nonneg_left (exponential_tail_le hβ s T hs.2) hsnon
      simpa only [mul_assoc, mul_comm, mul_left_comm] using ht
    _ = _ := by rw [integral_const_mul]; rfl

end SphericalAging.WeightedVolterra
