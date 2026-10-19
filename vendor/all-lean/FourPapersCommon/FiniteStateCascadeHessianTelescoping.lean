module
public import FourPapersCommon.FiniteStateCascadeRecurrence
public import FourPapersCommon.FiniteStateSpectralTraces

@[expose] public section

/-! Exact finite split-replica decomposition of the genuine cascade Hessian.
Every pair moment is an integral under the actual normalized cascade law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
variable {S I : Type*} [Fintype S] [Fintype I] [Nonempty S]
set_option maxHeartbeats 1600000

def finiteStatePointwiseProduct (K M : FiniteStateField S) : FiniteStateField S :=
  WithLp.toLp 2 (fun σ => K σ * M σ)

@[simp] theorem finiteStatePointwiseProduct_apply (K M : FiniteStateField S) (σ : S) :
    finiteStatePointwiseProduct K M σ = K σ * M σ := rfl

theorem finiteStateCascadeFirst_abs_le (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p : ℕ) (H K : FiniteStateField S) :
    |fderiv ℝ (finiteStateGaussianTerminalCascade V a L p) H K| ≤ ‖K‖ := by
  have hgrad : ‖fderiv ℝ (finiteStateGaussianTerminalCascade V a L p) H‖ ≤ 1 :=
    norm_fderiv_le_of_lipschitz ℝ (finiteStateGaussianTerminalCascade_lipschitz V a ha L p)
  have hk := (fderiv ℝ (finiteStateGaussianTerminalCascade V a L p) H).le_opNorm K
  rw [Real.norm_eq_abs] at hk
  exact hk.trans (by simpa using mul_le_mul_of_nonneg_right hgrad (norm_nonneg K))

theorem integrable_finiteStateCascadeFirst_kernel (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p k : ℕ) (H K : FiniteStateField S) :
    Integrable (fun y => fderiv ℝ (finiteStateGaussianTerminalCascade V a L p) y K)
      (finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) k H) := by
  haveI := isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L k
  have hd := (contDiff_one_finiteStateGaussianTerminalCascade V a ha L p).continuous_fderiv (by norm_num)
  exact source_bounded_integrable _ _ (hd.clm_apply continuous_const).measurable ‖K‖
    (fun y => finiteStateCascadeFirst_abs_le V a ha L p y K)

theorem integrable_finiteStateCascadePairMoment_kernel (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p q k : ℕ) (H K M : FiniteStateField S) :
    Integrable (fun y => finiteStateCascadePairMoment V a L p q y K M)
      (finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) k H) := by
  haveI := isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L k
  exact source_bounded_integrable _ _ (finiteStateCascadePairMoment_measurable V a ha L p q K M)
    (‖K‖*‖M‖) (fun y => finiteStateCascadePairMoment_abs_le V a ha L p q y K M)

variable [MeasurableSpace S] [MeasurableSingletonClass S]

theorem finiteStateCascadeHessian_pair_decomposition (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H K M : FiniteStateField S) :
    fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) H K M +
      a j * fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) H K *
        fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) H M =
    fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) H (finiteStatePointwiseProduct K M) +
      (a 0 - 1) * finiteStateCascadePairMoment V a L 0 j H K M +
      ∑ p ∈ Finset.range j, (a (p+1)-a p) *
        finiteStateCascadePairMoment V a L (p+1) (j-(p+1)) H K M := by
  classical
  induction j generalizing H with
  | zero =>
    simp only [finiteStateGaussianTerminalCascade, finiteStateGaussianCascade,
      finiteStateCascadePairMoment, sourceKernelExpectation, Finset.sum_range_zero, add_zero]
    rw [second_fderiv_finiteStateTerminal_eq_gibbsCovariance,
      fderiv_gtStateLogPartition_apply, integral_finiteStateGibbsKernel]
    simp only [finiteStatePointwiseProduct]
    simp_rw [integral_finiteStateGibbsKernel]
    rw [fderiv_gtStateLogPartition_apply, fderiv_gtStateLogPartition_apply]
    ring
  | succ j ih =>
    have hi1 := integrable_finiteStateCascadeFirst_kernel V a ha L j j H (finiteStatePointwiseProduct K M)
    have hi2 := (integrable_finiteStateCascadePairMoment_kernel V a ha L 0 j j H K M).const_mul (a 0-1)
    have hi3 (p : ℕ) (_hp : p ∈ Finset.range j) :=
      (integrable_finiteStateCascadePairMoment_kernel V a ha L (p+1) (j-(p+1)) j H K M).const_mul (a (p+1)-a p)
    have hint :
        (∫ y, fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) y K M +
          a j * fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y K *
            fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y M
          ∂finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H) =
        fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j+1)) H (finiteStatePointwiseProduct K M) +
          (a 0 - 1) * finiteStateCascadePairMoment V a L 0 (j+1) H K M +
          ∑ p ∈ Finset.range j, (a (p+1)-a p) *
            finiteStateCascadePairMoment V a L (p+1) ((j+1)-(p+1)) H K M := by
      simp_rw [ih]
      have hi12 : Integrable (fun y =>
          fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y (finiteStatePointwiseProduct K M) +
          (a 0-1)*finiteStateCascadePairMoment V a L 0 j y K M)
          (finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H) := hi1.add hi2
      have hisum : Integrable (fun y => ∑ p ∈ Finset.range j, (a (p+1)-a p)*
          finiteStateCascadePairMoment V a L (p+1) (j-(p+1)) y K M)
          (finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H) := integrable_finsetSum _ hi3
      have e1 := integral_add hi12 hisum
      have e2 := integral_add hi1 hi2
      try simp only [Pi.add_apply] at e1
      try simp only [Pi.add_apply] at e2
      rw [e1, e2, integral_const_mul, integral_finsetSum _ hi3,
        ← fderiv_finiteStateGaussianTerminalCascade_succ_integral V a ha L j H (finiteStatePointwiseProduct K M)]
      congr 1
      · rw [finiteStateCascadePairMoment_succ]
        simp only [zero_add]
      · apply Finset.sum_congr rfl
        intro p hp
        rw [integral_const_mul]
        have hq : p+1+(j-(p+1)) = j := by have := Finset.mem_range.mp hp; omega
        have hr : j+1-(p+1) = (j-(p+1))+1 := by have := Finset.mem_range.mp hp; omega
        rw [hr, finiteStateCascadePairMoment_succ, hq]
    rw [second_fderiv_finiteStateGaussianTerminalCascade_succ_integral V a ha L j H K M, hint,
      Finset.sum_range_succ]
    simp only [Nat.sub_self]
    have hz : finiteStateCascadePairMoment V a L (j+1) 0 H K M =
        fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j+1)) H K *
          fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j+1)) H M := rfl
    rw [hz]
    ring

end FourPapersCommon
