module
public import FourPapersCommon.FiniteStateCascadeGibbs
public import FourPapersCommon.GenericFiniteStateCascadeC1

@[expose] public section

/-! The actual differential of a finite Gaussian cascade is the mean of the
terminal coordinate under its genuine normalized Gibbs kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
variable {S I : Type*} [Fintype S] [Fintype I]

theorem finiteStateGaussianDifferential_eq_integral (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 1 F)
    (H : FiniteStateField S) :
    finiteStateGaussianDifferential a L F H =
      ∫ y, fderiv ℝ F y ∂finiteStateGaussianStepLaw a L F H := by
  have hDf := hF.continuous_fderiv (by norm_num)
  rw [finiteStateGaussianStepLaw_eq_map_tilted a L F hF.continuous.measurable H,
    integral_map (by fun_prop : Measurable (fun z => H + L z)).aemeasurable
      hDf.aestronglyMeasurable, integral_tilted]
  unfold finiteStateGaussianDifferential
  rw [← integral_smul]
  congr 1
  funext z
  simp only [smul_smul, div_eq_mul_inv, mul_comm]

theorem finiteStateGaussianDifferential_apply_eq_integral (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 1 F)
    (C : NNReal) (hC : ∀ y, ‖fderiv ℝ F y‖ ≤ C)
    (H K : FiniteStateField S) :
    finiteStateGaussianDifferential a L F H K =
      ∫ y, fderiv ℝ F y K ∂finiteStateGaussianStepLaw a L F H := by
  have hLip : LipschitzWith C F := lipschitzWith_of_nnnorm_fderiv_le hF.differentiable_one
    (fun y => NNReal.coe_le_coe.mp (hC y))
  haveI := isProbabilityMeasure_finiteStateGaussianStepLaw a L F hF.continuous.measurable H
    (integrable_exp_finiteStateGaussian_lipschitz F hLip L H a)
  have hi : Integrable (fderiv ℝ F) (finiteStateGaussianStepLaw a L F H) :=
    Integrable.of_bound (hF.continuous_fderiv (by norm_num)).aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)
  rw [finiteStateGaussianDifferential_eq_integral a L F hF H]
  exact ContinuousLinearMap.integral_apply hi K

variable [MeasurableSpace S] [MeasurableSingletonClass S]

theorem integral_finiteStateGibbsKernel (V : S → ℝ) [Nonempty S]
    (H : FiniteStateField S) (f : S → ℝ) :
    ∫ σ, f σ ∂finiteStateGibbsKernel V H = ∑ σ, gtStateGibbs V H σ * f σ := by
  rw [finiteStateGibbsKernel_apply V H,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (gtStateGibbs_nonneg V H _), smul_eq_mul,
    integral_count]

theorem fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean [Nonempty S]
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H K : FiniteStateField S) :
    fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) H K =
      ∫ σ, K σ ∂finiteStateCascadeGibbsKernel V a L j H := by
  classical
  have hKm : Measurable (fun σ : S => K σ) := measurable_of_finite _
  have hb (σ : S) : |K σ| ≤ ∑ τ : S, |K τ| :=
    Finset.single_le_sum (f := fun τ : S => |K τ|)
      (fun τ _ => abs_nonneg (K τ)) (Finset.mem_univ σ)
  induction j generalizing H with
  | zero =>
    rw [finiteStateCascadeGibbsKernel, finiteStateCascadeFieldKernel, sourceKernelLaw]
    simp only [Kernel.comp_id, finiteStateGaussianTerminalCascade, finiteStateGaussianCascade]
    rw [fderiv_gtStateLogPartition_apply, integral_finiteStateGibbsKernel]
  | succ j ih =>
    have hj := contDiff_one_finiteStateGaussianTerminalCascade V a ha L j
    have hd := (hasFDerivAt_finiteStateGaussianTerminalCascade_succ V a ha L j H).fderiv
    rw [hd, finiteStateGaussianDifferential_apply_eq_integral _ _ _ hj 1
      (fun y => norm_fderiv_le_of_lipschitz ℝ
        (finiteStateGaussianTerminalCascade_lipschitz V a ha L j)) H K]
    simp_rw [ih]
    haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L j
    haveI := isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L j
    change (∫ y, (∫ σ, K σ ∂finiteStateCascadeGibbsKernel V a L j y)
        ∂finiteStateGaussianStepLaw (a j) (L j)
          (finiteStateGaussianTerminalCascade V a L j) H) = _
    rw [← finiteStateGaussianStepKernel_apply _ _ _ hj.continuous.measurable]
    change (∫ y, (∫ σ, K σ ∂finiteStateCascadeGibbsKernel V a L j y)
      ∂finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H) = _
    rw [← Kernel.integral_comp (source_bounded_integrable _ _ hKm (∑ τ : S, |K τ|) hb)]
    congr 1
    simp only [finiteStateCascadeGibbsKernel, finiteStateCascadeFieldKernel, sourceKernelLaw,
      Kernel.comp_assoc]

end FourPapersCommon
