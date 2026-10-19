module
public import FourPapersCommon.FiniteStateCascadeHessianTelescoping
public import QuantitativeFollowup.DirectionalConvexity
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-! Convexity of the actual normalized finite Gaussian cascade. The
successor Hessian is the mean of the preceding Hessian plus a nonnegative
mass times its genuine conditional variance. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ContDiff
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT QuantitativeFollowup
variable {S I : Type*} [Fintype S] [Fintype I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]
set_option maxHeartbeats 1800000

theorem finiteStateTerminalHessian_nonneg (V : S → ℝ)
    (H K : FiniteStateField S) :
    0 ≤ fderiv ℝ (fderiv ℝ (gtStateLogPartition V)) H K K := by
  haveI := isMarkovKernel_finiteStateGibbsKernel V
  have hk : MemLp (fun σ : S => K σ) 2 (finiteStateGibbsKernel V H) := by
    exact (memLp_two_iff_integrable_sq (measurable_of_finite _).aestronglyMeasurable).mpr
      Integrable.of_finite
  rw [second_fderiv_finiteStateTerminal_eq_gibbsCovariance]
  have hv := variance_nonneg (X := fun σ : S => K σ) (μ := finiteStateGibbsKernel V H)
  rw [variance_eq_sub hk] at hv
  simpa only [pow_two,Pi.mul_apply] using hv

theorem finiteStateCascadeHessian_nonneg (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H K : FiniteStateField S) :
    0 ≤ fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) H K K := by
  induction j generalizing H with
  | zero => exact finiteStateTerminalHessian_nonneg V H K
  | succ j ih =>
    let P := finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H
    let g := fun y => fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y K
    let d := fun y => fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) y K K
    haveI : IsProbabilityMeasure P := by
      dsimp [P]
      haveI := isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L j
      infer_instance
    have hc := finiteStateGaussianTerminalCascade_C2_bounds V a ha L j
    have hg := (hc.1.continuous_fderiv (by norm_num)).clm_apply (continuous_const (y := K))
    have hgLp : MemLp g 2 P :=
      memLp_of_bounded (Filter.Eventually.of_forall fun y =>
        abs_le.mp (finiteStateCascadeFirst_abs_le V a ha L j y K))
        hg.measurable.aestronglyMeasurable 2
    have hcD : ContDiff ℝ 1 (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) :=
      hc.1.fderiv_right (by norm_num)
    have hd := (hcD.continuous_fderiv (by norm_num)).clm_apply
      (continuous_const (y := K)) |>.clm_apply (continuous_const (y := K))
    have hdB (y : FiniteStateField S) : |d y| ≤ finiteStateCascadeHessianBound a j * ‖K‖ * ‖K‖ := by
      have h1 := (fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) y).le_opNorm K
      have h2 := (fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) y K).le_opNorm K
      rw [Real.norm_eq_abs] at h2
      exact h2.trans (mul_le_mul_of_nonneg_right
        (h1.trans (mul_le_mul_of_nonneg_right (hc.2 y) (norm_nonneg K))) (norm_nonneg K))
    have hdInt : Integrable d P := source_bounded_integrable _ _ hd.measurable _ hdB
    have hgSq : Integrable (fun y => g y ^ 2) P := hgLp.integrable_sq
    have hEq : (∫ y, d y + a j * g y * g y ∂P) =
        (∫ y, d y ∂P) + a j * ∫ y, g y ^ 2 ∂P := by
      simp_rw [show ∀ y, a j * g y * g y = a j * g y ^ 2 by intro y; ring]
      rw [integral_add hdInt (hgSq.const_mul _),integral_const_mul]
    have hfirst : fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j+1)) H K =
        ∫ y, g y ∂P := fderiv_finiteStateGaussianTerminalCascade_succ_integral V a ha L j H K
    rw [second_fderiv_finiteStateGaussianTerminalCascade_succ_integral V a ha L j H K K]
    change 0 ≤ (∫ y, d y + a j * g y * g y ∂P) -
      a j * fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j+1)) H K *
        fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j+1)) H K
    rw [hEq,hfirst]
    have hmean : 0 ≤ ∫ y, d y ∂P := integral_nonneg fun y => ih y
    have hv := variance_nonneg (X := g) (μ := P)
    rw [variance_eq_sub hgLp] at hv
    simp only [Pi.pow_apply] at hv
    nlinarith [mul_nonneg (ha j) hv]

theorem convexOn_finiteStateGaussianTerminalCascade (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    ConvexOn ℝ univ (finiteStateGaussianTerminalCascade V a L j) := by
  have hc := (finiteStateGaussianTerminalCascade_C2_bounds V a ha L j).1
  apply convexOn_of_line_second_derivatives univ convex_univ _ hc.continuous.continuousOn
  intro x hx y hy
  refine ⟨(fun r => fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)
      (x+r • (y-x)) (y-x)),
    (fun r => directionalHessian (finiteStateGaussianTerminalCascade V a L j)
      (x+r • (y-x)) (y-x)),?_,?_,?_⟩
  · exact fun r _ => hasDerivAt_on_affine_line _ hc x (y-x) r
  · exact fun r _ => hasDerivAt_directional_on_affine_line _ hc x (y-x) r
  · exact fun r _ => finiteStateCascadeHessian_nonneg V a ha L j _ _

end FourPapersCommon
