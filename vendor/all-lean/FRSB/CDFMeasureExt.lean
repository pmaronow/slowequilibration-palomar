module
public import FRSB.ParisiMeasureTopology
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! # Actual overlap-measure identification from integrated CDFs

CDF equality almost everywhere detects both endpoint atoms because the
measures have total mass one. Right continuity is obtained from Mathlib's
actual probability-distribution CDF, rather than assumed for a candidate.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace FRSB
open Paper ProbabilityTheory

theorem parisiCDF_eq_realCDF (μ : ParisiMeasure) (t : ℝ) :
    parisiCDF μ t = cdf ((μ : Measure Overlap).map Subtype.val) t := by
  rw [cdf_eq_real, measureReal_def, Measure.map_apply measurable_subtype_coe measurableSet_Iic]
  rfl

theorem parisiCDF_right_continuous (μ : ParisiMeasure) (t : ℝ) :
    ContinuousWithinAt (parisiCDF μ) (Ici t) t := by
  have heq : parisiCDF μ = cdf ((μ : Measure Overlap).map Subtype.val) :=
    funext (parisiCDF_eq_realCDF μ)
  rw [heq]
  exact (cdf _).right_continuous t

theorem parisiCDF_eq_zero_of_lt_zero (μ : ParisiMeasure) {t : ℝ} (ht : t < 0) :
    parisiCDF μ t = 0 := by
  have hs : {q : Overlap | (q : ℝ) ≤ t} = ∅ := by
    ext q
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact not_le.mpr (ht.trans_le q.property.1)
  simp [parisiCDF, hs]

theorem parisiCDF_tail_hasDerivWithinAt (μ ν : ParisiMeasure) (t : ℝ) :
    HasDerivWithinAt (fun x => ∫ s in x..1, parisiCDF μ s - parisiCDF ν s)
      (-(parisiCDF μ t - parisiCDF ν t)) (Ici t) t := by
  exact intervalIntegral.integral_hasDerivWithinAt_left (t := Ioi t)
    ((parisiCDF_intervalIntegrable μ t 1).sub (parisiCDF_intervalIntegrable ν t 1))
    (((parisiCDF_measurable μ).sub (parisiCDF_measurable ν)).stronglyMeasurable.stronglyMeasurableAtFilter)
    (((parisiCDF_right_continuous μ t).sub (parisiCDF_right_continuous ν t)).mono
      Ioi_subset_Ici_self)

/-- Full real almost-everywhere CDF equality identifies the actual laws. -/
theorem eq_of_parisiCDF_ae_eq (μ ν : ParisiMeasure)
    (h : parisiCDF μ =ᵐ[volume] parisiCDF ν) : μ = ν := by
  have hCDF : ∀ t, parisiCDF μ t = parisiCDF ν t := by
    intro t
    have hp : (fun x => ∫ s in x..1, parisiCDF μ s - parisiCDF ν s) = fun _ => 0 := by
      funext x
      apply intervalIntegral.integral_zero_ae
      filter_upwards [h] with s hs
      intro _
      simp [hs]
    have hd := (parisiCDF_tail_hasDerivWithinAt μ ν t).derivWithin
      (uniqueDiffWithinAt_Ici t)
    rw [hp] at hd
    have he : parisiCDF ν t - parisiCDF μ t = 0 := by simpa using hd.symm
    linarith
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_Iic
  intro q
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact hCDF q

/-- Equality on almost every physical time extends through the endpoint atoms. -/
theorem eq_of_parisiCDF_ae_eq_on (μ ν : ParisiMeasure)
    (h : parisiCDF μ =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] parisiCDF ν) : μ = ν := by
  apply eq_of_parisiCDF_ae_eq
  have hh := (ae_restrict_iff' measurableSet_Ioc).mp h
  filter_upwards [hh, volume.ae_ne (0 : ℝ)] with t ht ht0
  by_cases hi : t ∈ Ioc (0 : ℝ) 1
  · exact ht hi
  · by_cases hn : t < 0
    · rw [parisiCDF_eq_zero_of_lt_zero μ hn, parisiCDF_eq_zero_of_lt_zero ν hn]
    · have hge : 1 ≤ t := by
        simp only [mem_Ioc, not_and_or, not_lt, not_le] at hi
        rcases hi with hi | hi
        · exact False.elim (ht0 (le_antisymm hi (not_lt.mp hn)))
        · exact hi.le
      rw [parisiCDF_eq_one_of_one_le μ hge, parisiCDF_eq_one_of_one_le ν hge]

/-- The genuine CDF L¹ distance separates overlap probability measures. -/
theorem eq_of_parisiCDFDistance_eq_zero (μ ν : ParisiMeasure)
    (h : parisiCDFDistance μ ν = 0) : μ = ν := by
  apply eq_of_parisiCDF_ae_eq_on
  have hz := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
    (show (0 : ℝ) ≤ 1 by norm_num)
    (Eventually.of_forall (fun t => abs_nonneg (parisiCDF μ t - parisiCDF ν t)))
    (parisiCDF_abs_diff_intervalIntegrable μ ν 0 1)).mp h
  filter_upwards [hz] with t ht
  exact sub_eq_zero.mp (abs_eq_zero.mp ht)

/-- Vanishing signed CDF tail integrals also identifies the actual laws.
Right FTC is valid even at an atom; no continuity-at-atoms premise is used. -/
theorem eq_of_parisiCDF_tail_integrals_eq_zero (μ ν : ParisiMeasure)
    (h : ∀ t ∈ Ioo (0 : ℝ) 1,
      (∫ s in t..1, parisiCDF μ s - parisiCDF ν s) = 0) : μ = ν := by
  have heq (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : parisiCDF μ t = parisiCDF ν t := by
    have hz : (fun x => ∫ s in x..1, parisiCDF μ s - parisiCDF ν s) =ᶠ[𝓝[≥] t]
        (fun _ => 0) := by
      have hm : ∀ᶠ x in 𝓝 t, x ∈ Ioo (0 : ℝ) 1 := isOpen_Ioo.mem_nhds ht
      filter_upwards [hm.filter_mono nhdsWithin_le_nhds]
        with x hx
      exact h x hx
    have hd0 : HasDerivWithinAt
        (fun x => ∫ s in x..1, parisiCDF μ s - parisiCDF ν s) 0 (Ici t) t :=
      (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt.congr_of_eventuallyEq_of_mem
        hz (self_mem_Ici)
    have hd := (parisiCDF_tail_hasDerivWithinAt μ ν t).derivWithin
      (uniqueDiffWithinAt_Ici t)
    rw [hd0.derivWithin (uniqueDiffWithinAt_Ici t)] at hd
    linarith
  apply eq_of_parisiCDF_ae_eq
  filter_upwards [volume.ae_ne (0 : ℝ)] with t ht0
  by_cases hn : t < 0
  · rw [parisiCDF_eq_zero_of_lt_zero μ hn, parisiCDF_eq_zero_of_lt_zero ν hn]
  · by_cases hge : 1 ≤ t
    · rw [parisiCDF_eq_one_of_one_le μ hge, parisiCDF_eq_one_of_one_le ν hge]
    · exact heq t ⟨lt_of_le_of_ne (not_lt.mp hn) (Ne.symm ht0), not_le.mp hge⟩

end FRSB
