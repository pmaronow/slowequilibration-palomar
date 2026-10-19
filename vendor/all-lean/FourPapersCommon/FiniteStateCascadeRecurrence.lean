module
public import FourPapersCommon.FiniteStateCascadeHessianExpectations
public import FourPapersCommon.FiniteStateCascadePairs

@[expose] public section

/-! Exact conditional recurrences for the actual first/second Gaussian
cascade derivatives, and their actual split-replica moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
variable {S I : Type*} [Fintype S] [Fintype I] [Nonempty S]
set_option maxHeartbeats 1400000

theorem fderiv_finiteStateGaussianTerminalCascade_succ_integral (V : S → ℝ)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H K : FiniteStateField S) :
    fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j+1)) H K =
      ∫ y, fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y K
        ∂finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H := by
  have hj := contDiff_one_finiteStateGaussianTerminalCascade V a ha L j
  rw [(hasFDerivAt_finiteStateGaussianTerminalCascade_succ V a ha L j H).fderiv,
    finiteStateGaussianDifferential_apply_eq_integral _ _ _ hj 1
      (fun y => norm_fderiv_le_of_lipschitz ℝ
        (finiteStateGaussianTerminalCascade_lipschitz V a ha L j)) H K]
  rw [finiteStateGaussianCascadeKernel, finiteStateGaussianStepKernel_apply
    (a j) (L j) (finiteStateGaussianCascade a L (gtStateLogPartition V) j) hj.continuous.measurable]
  rfl

theorem second_fderiv_finiteStateGaussianTerminalCascade_succ_integral (V : S → ℝ)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H K M : FiniteStateField S) :
    fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j+1))) H K M =
      (∫ y, fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) y K M +
        a j * fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y K *
          fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y M
          ∂finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H) -
        a j * fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j+1)) H K *
          fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j+1)) H M := by
  have hj := finiteStateGaussianTerminalCascade_C2_bounds V a ha L j
  have hgrad : ∀ y, ‖fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y‖ ≤ (1 : NNReal) :=
    fun y => norm_fderiv_le_of_lipschitz ℝ (finiteStateGaussianTerminalCascade_lipschitz V a ha L j)
  have hEq : fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j+1)) =
      finiteStateGaussianDifferential (a j) (L j) (finiteStateGaussianTerminalCascade V a L j) :=
    funext fun y => (hasFDerivAt_finiteStateGaussianTerminalCascade_succ V a ha L j y).fderiv
  have hDD := hasFDerivAt_finiteStateGaussianDifferential (a j) (L j)
    (finiteStateGaussianTerminalCascade V a L j) hj.1 1 (finiteStateCascadeHessianBound a j)
    hgrad hj.2 H
  have hessEq : fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j+1))) H =
      finiteStateGaussianHessian (a j) (L j) (finiteStateGaussianTerminalCascade V a L j) H := by
    rw [hEq, hDD.fderiv]
  rw [hessEq, finiteStateGaussianHessian_apply_eq_integral _ _ _ hj.1 1
    (finiteStateCascadeHessianBound a j) hgrad hj.2 H K M, ← hEq]
  rw [finiteStateGaussianCascadeKernel, finiteStateGaussianStepKernel_apply
    (a j) (L j) (finiteStateGaussianCascade a L (gtStateLogPartition V) j) hj.1.continuous.measurable]
  rfl

def finiteStateCascadePairMoment (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p q : ℕ) (H K M : FiniteStateField S) : ℝ :=
  sourceKernelExpectation
    (fun j => finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (p+j)) q
    (fun y => fderiv ℝ (finiteStateGaussianTerminalCascade V a L p) y K *
      fderiv ℝ (finiteStateGaussianTerminalCascade V a L p) y M) H

theorem finiteStateCascadePairMoment_succ (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p q : ℕ) (H K M : FiniteStateField S) :
    finiteStateCascadePairMoment V a L p (q+1) H K M =
      ∫ y, finiteStateCascadePairMoment V a L p q y K M
        ∂finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (p+q) H := rfl

theorem finiteStateCascadePairMoment_measurable (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p q : ℕ) (K M : FiniteStateField S) :
    Measurable (fun H => finiteStateCascadePairMoment V a L p q H K M) := by
  have hd := (contDiff_one_finiteStateGaussianTerminalCascade V a ha L p).continuous_fderiv (by norm_num)
  exact sourceKernelExpectation_measurable _ _
    ((hd.clm_apply continuous_const).mul (hd.clm_apply continuous_const)).measurable q

theorem finiteStateCascadePairMoment_abs_le (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p q : ℕ) (H K M : FiniteStateField S) :
    |finiteStateCascadePairMoment V a L p q H K M| ≤ ‖K‖*‖M‖ := by
  have hd := (contDiff_one_finiteStateGaussianTerminalCascade V a ha L p).continuous_fderiv (by norm_num)
  have hgrad (y) : ‖fderiv ℝ (finiteStateGaussianTerminalCascade V a L p) y‖ ≤ 1 :=
    norm_fderiv_le_of_lipschitz ℝ (finiteStateGaussianTerminalCascade_lipschitz V a ha L p)
  have hb (y : FiniteStateField S) :
      |fderiv ℝ (finiteStateGaussianTerminalCascade V a L p) y K *
        fderiv ℝ (finiteStateGaussianTerminalCascade V a L p) y M| ≤ ‖K‖*‖M‖ := by
    have hk := (fderiv ℝ (finiteStateGaussianTerminalCascade V a L p) y).le_opNorm K
    have hm := (fderiv ℝ (finiteStateGaussianTerminalCascade V a L p) y).le_opNorm M
    rw [Real.norm_eq_abs] at hk hm
    rw [abs_mul]
    exact mul_le_mul
      (hk.trans (by simpa using mul_le_mul_of_nonneg_right (hgrad y) (norm_nonneg K)))
      (hm.trans (by simpa using mul_le_mul_of_nonneg_right (hgrad y) (norm_nonneg M)))
      (abs_nonneg _) (norm_nonneg K)
  exact sourceKernelExpectation_abs_le _
    (fun j => isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L (p+j)) _
    ((hd.clm_apply continuous_const).mul (hd.clm_apply continuous_const)).measurable
    (‖K‖*‖M‖) (mul_nonneg (norm_nonneg K) (norm_nonneg M)) hb q H

variable [MeasurableSpace S] [MeasurableSingletonClass S]
theorem finiteStateCascadePairMoment_eq_splitLaw (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p q : ℕ) (H K M : FiniteStateField S) :
    finiteStateCascadePairMoment V a L p q H K M =
      ∫ z, K z.1 * M z.2 ∂finiteStateCascadeSplitLaw V a L p q H := by
  have hd := (contDiff_one_finiteStateGaussianTerminalCascade V a ha L p).continuous_fderiv (by norm_num)
  unfold finiteStateCascadePairMoment
  rw [sourceKernelExpectation_eq_integral _
    (fun j => isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L (p+j)) _
    (show Measurable (fun y => fderiv ℝ (finiteStateGaussianTerminalCascade V a L p) y K *
        fderiv ℝ (finiteStateGaussianTerminalCascade V a L p) y M) from
      ((hd.clm_apply continuous_const).mul (hd.clm_apply continuous_const)).measurable)
    (‖K‖*‖M‖) (fun y => by
      simpa only [finiteStateCascadePairMoment, sourceKernelExpectation] using
        finiteStateCascadePairMoment_abs_le V a ha L p 0 y K M) q H]
  exact (integral_finiteStateCascadeSplitLaw_coordinates V a ha L p q H K M).symm

end FourPapersCommon
