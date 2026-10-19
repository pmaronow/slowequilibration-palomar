module
public import FRSB.GlobalMeasureStability

@[expose] public section

/-! Uniform weak-measure continuity of the genuine unbounded potential.
The difference has a global spatial bound, although either potential grows
linearly. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace FRSB
open Paper

def parisiPotentialMeasureError (β : ℝ) (μ ν : ParisiMeasure) : ℝ :=
  β ^ 2 * ‖parisiGradientBCF β μ - parisiGradientBCF β ν‖ + β ^ 2 / 2 * parisiCDFDistance μ ν

theorem parisiPotential_measure_error_bound (β : ℝ) (μ ν : ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖parisiPotential β μ (t, x) - parisiPotential β ν (t, x)‖ ≤
      parisiPotentialMeasureError β μ ν := by
  have h := norm_parisiDuhamelPotential_measure_gradient_sub_le β μ ν
    (parisiGradient β μ) (parisiGradient β ν)
    (continuous_parisiGradient β μ).measurable (continuous_parisiGradient β ν).measurable
    1 ‖parisiGradientBCF β μ - parisiGradientBCF β ν‖
    (norm_parisiGradient_le_one β μ) (norm_parisiGradient_le_one β ν)
    (norm_parisiSlabExtend_sub_le (by norm_num : (0 : ℝ) ≤ 1)
      (parisiGradientBCF β μ) (parisiGradientBCF β ν)) t x ht
  rw [parisiPotential_eq_duhamel β μ t x ht.2, parisiPotential_eq_duhamel β ν t x ht.2]
  simpa only [parisiPotentialMeasureError, one_pow, mul_one, Real.norm_eq_abs,
    parisiCDFDistance] using h

theorem tendsto_parisiPotentialMeasureError_of_weak {A : Type*} {l : Filter A}
    [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure) (ν : A → ParisiMeasure)
    (hν : Tendsto ν l (𝓝 μ)) :
    Tendsto (fun i => parisiPotentialMeasureError β (ν i) μ) l (𝓝 0) := by
  have hgrad := ((continuous_gradientBCF β).tendsto μ).comp hν
  have hnorm : Tendsto (fun i => ‖parisiGradientBCF β (ν i) - parisiGradientBCF β μ‖)
      l (𝓝 0) := by simpa using (hgrad.sub_const (parisiGradientBCF β μ)).norm
  have hCDF := tendsto_parisiCDFDistance_of_tendsto hν
  simpa [parisiPotentialMeasureError] using
    (hnorm.const_mul (β ^ 2)).add (hCDF.const_mul (β ^ 2 / 2))

theorem tendsto_parisiPotential_of_weak {A : Type*} {l : Filter A}
    [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure) (ν : A → ParisiMeasure)
    (hν : Tendsto ν l (𝓝 μ)) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun i => parisiPotential β (ν i) (t, x)) l (𝓝 (parisiPotential β μ (t, x))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun i => parisiPotential_measure_error_bound β (ν i) μ t x ht)
    (tendsto_parisiPotentialMeasureError_of_weak β μ ν hν)

/-- The literal order-zero assertion is uniform in time and the entire
unbounded spatial line. -/
theorem eventually_uniform_parisiPotential_of_weak {A : Type*} {l : Filter A}
    [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure) (ν : A → ParisiMeasure)
    (hν : Tendsto ν l (𝓝 μ)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ,
      |parisiPotential β (ν i) (t, x) - parisiPotential β μ (t, x)| < ε := by
  filter_upwards [(tendsto_parisiPotentialMeasureError_of_weak β μ ν hν).eventually
    (eventually_lt_nhds hε)] with i hi
  intro t ht x
  have hbound : |parisiPotential β (ν i) (t, x) - parisiPotential β μ (t, x)| ≤
      parisiPotentialMeasureError β (ν i) μ := by
    simpa only [Real.norm_eq_abs] using parisiPotential_measure_error_bound β (ν i) μ t x ht
  exact hbound.trans_lt hi

theorem tendstoUniformlyOn_parisiPotential_of_weak {A : Type*} {l : Filter A}
    [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure) (ν : A → ParisiMeasure)
    (hν : Tendsto ν l (𝓝 μ)) :
    TendstoUniformlyOn (fun i => parisiPotential β (ν i)) (parisiPotential β μ) l
      (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [eventually_uniform_parisiPotential_of_weak β μ ν hν ε hε] with i hi
  intro p hp
  rw [Real.dist_eq, abs_sub_comm]
  exact hi p.1 hp.1 p.2

end FRSB
