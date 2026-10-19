module
public import FRSB.ConstantMassFarField
public import Paper.DoobKernel

@[expose] public section

/-! Positivity and the sharp absolute-growth envelope of the actual PDE. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal
namespace FRSB

lemma logCosh_nonneg (x : ℝ) : 0 ≤ Real.log (Real.cosh x) :=
  Real.log_nonneg (Real.one_le_cosh x)

theorem parisiPotential_nonneg (β : ℝ) (μ : ParisiMeasure) (t x : ℝ)
    (ht : t ≤ 1) : 0 ≤ parisiPotential β μ (t, x) := by
  rw [parisiPotential_eq_duhamel β μ t x ht]
  unfold parisiDuhamelPotential parisiDuhamelCorrection
  apply add_nonneg
  · exact integral_nonneg (fun _ => logCosh_nonneg _)
  · apply mul_nonneg (by positivity)
    apply intervalIntegral.integral_nonneg ht
    intro r hr
    unfold parisiHeatSource
    exact mul_nonneg (parisiCDF_nonneg μ r) (integral_nonneg (fun _ => sq_nonneg _))

lemma integral_logCosh_gaussianReal_le (x : ℝ) (v : ℝ≥0) :
    ∫ y, Real.log (Real.cosh y) ∂gaussianReal x v ≤ (v : ℝ) / 2 + Real.log (Real.cosh x) := by
  let b := Real.exp ((v : ℝ) / 2) * Real.cosh x
  have hb : 0 < b := mul_pos (Real.exp_pos _) (Real.cosh_pos x)
  have hilog : Integrable (fun y => Real.log (Real.cosh y)) (gaussianReal x v) := by
    have hg : ColeHopfFoundation.ProbabilityTheory.HasLinearGrowth
        (fun y => Real.log (Real.cosh y)) := ⟨0, 1, zero_le_one, fun y => by
      simpa only [zero_add, one_mul, Real.norm_eq_abs] using norm_logcosh_le_abs y⟩
    apply hg.toHasExpGrowth.integrable_gaussianReal
    exact ((Real.continuous_cosh).log (fun y => (Real.cosh_pos y).ne')).aestronglyMeasurable
  have hic := integrable_cosh_gaussianReal x v
  have hpoint (y : ℝ) : Real.log (Real.cosh y) ≤ Real.log b + Real.cosh y / b - 1 := by
    have hh := Real.log_le_sub_one_of_pos (div_pos (Real.cosh_pos y) hb)
    rw [Real.log_div (Real.cosh_pos y).ne' hb.ne'] at hh
    linarith
  have h := integral_mono hilog (((integrable_const (Real.log b)).add (hic.div_const b)).sub (integrable_const 1)) hpoint
  simp only [Pi.add_apply, Pi.sub_apply] at h
  have hconst : (∫ y, Real.log b + Real.cosh y / b - 1 ∂gaussianReal x v) = Real.log b := by
    have hsub := integral_sub ((integrable_const (Real.log b)).add (hic.div_const b))
      (integrable_const (1 : ℝ))
    have hadd := integral_add (integrable_const (Real.log b)) (hic.div_const b)
    simp only [Pi.add_apply, Pi.sub_apply] at hsub hadd
    rw [hsub, hadd, integral_div, integral_cosh_gaussianReal]
    simp [b, hb.ne']
  rw [hconst] at h
  simpa only [b, Real.log_mul (Real.exp_pos _).ne' (Real.cosh_pos x).ne', Real.log_exp] using h

lemma heatLogCosh_le (ell x : ℝ) (hell : 0 ≤ ell) :
    heatSemigroup ell (fun y => Real.log (Real.cosh y)) x ≤ ell / 2 + Real.log (Real.cosh x) := by
  have hm : (gaussianReal 0 1).map (fun z => x + Real.sqrt ell * z) = gaussianReal x ell.toNNReal := by
    rw [show (fun z : ℝ => x + Real.sqrt ell * z) =
      (fun z => x + z) ∘ (fun z => Real.sqrt ell * z) by rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_const_add]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt hell, Real.toNNReal_of_nonneg hell]
  have hi := integral_logCosh_gaussianReal_le x ell.toNNReal
  rw [← hm, integral_map (by fun_prop)
    ((Real.continuous_cosh).log (fun y => (Real.cosh_pos y).ne')).aestronglyMeasurable] at hi
  simpa only [heatSemigroup, gaussianExpectation, Real.coe_toNNReal _ hell] using hi

/-- The exact Gaussian-growth envelope used for forward density tails. -/
theorem parisiPotential_absolute_growth (β : ℝ) (μ : ParisiMeasure) (t x : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |parisiPotential β μ (t, x)| ≤ β ^ 2 + |x| := by
  rw [abs_of_nonneg (parisiPotential_nonneg β μ t x ht.2),
    parisiPotential_eq_duhamel β μ t x ht.2]
  unfold parisiDuhamelPotential
  have hh := heatLogCosh_le (β ^ 2 * (1 - t)) x (by nlinarith [sq_nonneg β, ht.2])
  have hc := norm_parisiDuhamelCorrection_le β μ (parisiGradient β μ) 1
    (norm_parisiGradient_le_one β μ) 1 t x ht.2
  have hl := norm_logcosh_le_abs x
  rw [Real.norm_eq_abs] at hc hl
  have hc' := le_trans (le_abs_self _) hc
  have hl' := le_trans (le_abs_self _) hl
  nlinarith [sq_nonneg β, ht.1]

end FRSB
