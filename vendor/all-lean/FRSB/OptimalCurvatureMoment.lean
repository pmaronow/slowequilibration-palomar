module
public import FRSB.OptimalDiffusion

@[expose] public section

/-! The actual curvature observable is strictly positive along every physical
state path. Its squared expectation is finite, positive, and at most one. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology
namespace FRSB
open Paper

@[simp] theorem parisiSpatialJet_two (β : ℝ) (μ : ParisiMeasure) (s x : ℝ) :
    parisiSpatialJet β μ 2 s x = parisiHessian β μ (s,x) := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, parisiSpatialJet_succ_eq_gradient_derivative]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  exact (hasDerivAt_parisiGradient_spatial_all β μ s x).deriv

@[simp] theorem C_eq_hessian (β : ℝ) (μ : ParisiMeasure) (s : ℝ) (ω : BrownianSample) :
    C β μ s ω = parisiHessian β μ (s, optimalStateReal β μ ω s) := by
  exact parisiSpatialJet_two β μ s _

theorem C_pos (β : ℝ) (μ : ParisiMeasure) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ω : BrownianSample) : 0 < C β μ s ω := by
  rw [C_eq_hessian]
  exact parisiHessian_pos_all β μ s _ hs

theorem norm_C_le_one (β : ℝ) (μ : ParisiMeasure) (s : ℝ) (ω : BrownianSample) :
    ‖C β μ s ω‖ ≤ 1 := by
  rw [C_eq_hessian]
  exact norm_parisiHessian_le_one_all β μ _

def curvatureMoment2 (β : ℝ) (μ : ParisiMeasure) (s : ℝ) : ℝ :=
  ∫ ω, C β μ s ω ^ 2 ∂canonicalBrownianMeasure

theorem measurable_C (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : Measurable (C β μ s) := by
  change Measurable (fun ω => C β μ s ω)
  simp_rw [C_eq_hessian]
  exact (continuous_parisiHessian_all β μ).measurable.comp
    (measurable_const.prodMk (by
      rw [optimalStateReal_eq_selected β hβ μ]
      exact measurable_selectedParisiStateReal β 0 hβ μ s hs))

theorem integrable_C_sq (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : Integrable (fun ω => C β μ s ω ^ 2) canonicalBrownianMeasure := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_C β hβ μ hs).pow_const 2).aestronglyMeasurable
  exact .of_forall fun ω => by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_C_le_one β μ s ω)

theorem curvatureMoment2_pos (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : 0 < curvatureMoment2 β μ s := by
  unfold curvatureMoment2
  apply (integral_pos_iff_support_of_nonneg (fun ω => sq_nonneg (C β μ s ω))
    (integrable_C_sq β hβ μ hs)).mpr
  have he : Function.support (fun ω => C β μ s ω ^ 2) = univ := by
    ext ω
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (sq_pos_of_pos (C_pos β μ hs ω)).ne'
  rw [he]
  simp

theorem curvatureMoment2_le_one (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : curvatureMoment2 β μ s ≤ 1 := by
  have hh := integral_mono (integrable_C_sq β hβ μ hs)
    (integrable_const (1 : ℝ)) (fun ω => by
      have hnorm := norm_C_le_one β μ s ω
      rw [Real.norm_eq_abs, abs_le] at hnorm
      nlinarith [hnorm.1, hnorm.2])
  simpa only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    one_smul, curvatureMoment2] using hh

end FRSB
