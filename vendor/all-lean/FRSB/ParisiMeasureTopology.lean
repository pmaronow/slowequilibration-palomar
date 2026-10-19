module
public import FRSB.Foundation
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Weak convergence of actual overlap probability measures controls their
integrated CDF distance, including atoms at either endpoint. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace FRSB
open Paper

/-- Only countably many real thresholds carry positive overlap mass. -/
theorem countable_parisi_atoms (μ : ParisiMeasure) :
    Set.Countable {s : ℝ | 0 < (μ : Measure Overlap) {q | (q : ℝ) = s}} :=
  Measure.countable_meas_level_set_pos measurable_subtype_coe

/-- Almost every real threshold has zero mass under an arbitrary Parisi measure. -/
theorem ae_parisi_level_null (μ : ParisiMeasure) :
    ∀ᵐ s ∂(volume : Measure ℝ), (μ : Measure Overlap) {q | (q : ℝ) = s} = 0 := by
  filter_upwards [(countable_parisi_atoms μ).ae_notMem volume] with s hs
  exact le_antisymm (not_lt.mp hs) (bot_le)

/-- Portmanteau gives pointwise CDF convergence at every null level set. -/
theorem tendsto_parisiCDF_of_level_null {ι : Type*} {L : Filter ι}
    {μs : ι → ParisiMeasure} {μ : ParisiMeasure}
    (hμ : Tendsto μs L (𝓝 μ)) {s : ℝ}
    (hs : (μ : Measure Overlap) {q | (q : ℝ) = s} = 0) :
    Tendsto (fun i => parisiCDF (μs i) s) L (𝓝 (parisiCDF μ s)) := by
  have hf : (μ : Measure Overlap) (frontier {q : Overlap | (q : ℝ) ≤ s}) = 0 := by
    apply measure_mono_null (frontier_le_subset_eq continuous_subtype_val continuous_const) hs
  exact (ENNReal.tendsto_toReal (measure_ne_top (μ : Measure Overlap) _)).comp
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ hf)

/-- Genuine weak convergence implies convergence of the time-L¹ CDF distance. -/
theorem tendsto_parisiCDFDistance_of_tendsto {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] {μs : ι → ParisiMeasure} {μ : ParisiMeasure}
    (hμ : Tendsto μs L (𝓝 μ)) :
    Tendsto (fun i => parisiCDFDistance (μs i) μ) L (𝓝 0) := by
  let τ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have : IsFiniteMeasure τ := by
    dsimp [τ]
    exact isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ioc])
  have hlim : ∀ᵐ s ∂τ,
      Tendsto (fun i => |parisiCDF (μs i) s - parisiCDF μ s|) L (𝓝 (0 : ℝ)) := by
    filter_upwards [(ae_parisi_level_null μ).filter_mono (ae_mono (Measure.restrict_le_self))]
      with s hs
    simpa only [sub_self, abs_zero] using
      (tendsto_parisiCDF_of_level_null hμ hs).sub
        (tendsto_const_nhds (x := parisiCDF μ s)) |>.abs
  have hbound (i : ι) (s : ℝ) :
      ‖|parisiCDF (μs i) s - parisiCDF μ s|‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    constructor <;> linarith [parisiCDF_nonneg (μs i) s, parisiCDF_le_one (μs i) s,
      parisiCDF_nonneg μ s, parisiCDF_le_one μ s]
  have hi := tendsto_integral_filter_of_dominated_convergence (μ := τ)
    (fun _ => (1 : ℝ))
    (Eventually.of_forall fun i =>
      (((parisiCDF_measurable (μs i)).sub (parisiCDF_measurable μ)).abs).aestronglyMeasurable)
    (Eventually.of_forall fun i => Eventually.of_forall (hbound i))
    (integrable_const (1 : ℝ)) hlim
  dsimp only [τ] at hi
  simpa only [Pi.sub_apply, parisiCDFDistance, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_zero] using hi

/-- The integrated CDF distance is continuous in its first weak measure argument. -/
theorem continuous_parisiCDFDistance_left (μ : ParisiMeasure) :
    Continuous (fun ν => parisiCDFDistance ν μ) := by
  apply continuous_iff_continuousAt.mpr
  intro ν
  have hdiff : Tendsto (fun η => parisiCDFDistance η ν) (𝓝 ν) (𝓝 0) :=
    tendsto_parisiCDFDistance_of_tendsto tendsto_id
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto (fun η => parisiCDFDistance ν μ - parisiCDFDistance η ν)
      (𝓝 ν) (𝓝 (parisiCDFDistance ν μ)) by simpa using tendsto_const_nhds.sub hdiff)
    (show Tendsto (fun η => parisiCDFDistance ν μ + parisiCDFDistance η ν)
      (𝓝 ν) (𝓝 (parisiCDFDistance ν μ)) by simpa using tendsto_const_nhds.add hdiff)
    (fun η => ?_) (fun η => ?_)
  · unfold parisiCDFDistance
    rw [← intervalIntegral.integral_sub
      (parisiCDF_abs_diff_intervalIntegrable ν μ 0 1)
      (parisiCDF_abs_diff_intervalIntegrable η ν 0 1)]
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((parisiCDF_abs_diff_intervalIntegrable ν μ 0 1).sub
        (parisiCDF_abs_diff_intervalIntegrable η ν 0 1))
      (parisiCDF_abs_diff_intervalIntegrable η μ 0 1)
    intro s _
    have ht := abs_sub_le (parisiCDF ν s - parisiCDF η s)
      (parisiCDF η s - parisiCDF μ s)
    have ha := abs_add_le (parisiCDF ν s - parisiCDF η s)
      (parisiCDF η s - parisiCDF μ s)
    rw [abs_sub_comm (parisiCDF ν s) (parisiCDF η s)] at ha
    have he : parisiCDF ν s - parisiCDF η s +
        (parisiCDF η s - parisiCDF μ s) = parisiCDF ν s - parisiCDF μ s := by ring
    rw [he] at ha
    linarith
  · unfold parisiCDFDistance
    rw [← intervalIntegral.integral_add
      (parisiCDF_abs_diff_intervalIntegrable ν μ 0 1)
      (parisiCDF_abs_diff_intervalIntegrable η ν 0 1)]
    apply intervalIntegral.integral_mono_on (by norm_num)
      (parisiCDF_abs_diff_intervalIntegrable η μ 0 1)
      ((parisiCDF_abs_diff_intervalIntegrable ν μ 0 1).add
        (parisiCDF_abs_diff_intervalIntegrable η ν 0 1))
    intro s _
    have ha := abs_add_le (parisiCDF η s - parisiCDF ν s)
      (parisiCDF ν s - parisiCDF μ s)
    have he : parisiCDF η s - parisiCDF ν s +
        (parisiCDF ν s - parisiCDF μ s) = parisiCDF η s - parisiCDF μ s := by ring
    rw [he] at ha
    linarith

end FRSB
