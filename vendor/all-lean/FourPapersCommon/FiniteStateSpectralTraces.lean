module
public import FourPapersCommon.FiniteStateCascadePairs

@[expose] public section

/-! Genuine finite spectral contractions of first/second derivatives. The
terminal Hessian is its Gibbs diagonal contraction minus the independent-copy
contraction, with all finite sums kept explicit. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace FourPapersCommon
open SpinGlass.AT
variable {S I : Type*} [Fintype S] [Fintype I] [DecidableEq I]

def finiteStateSpectralCovariance
    (L : EuclideanSpace ℝ I →L[ℝ] FiniteStateField S) (σ τ : S) : ℝ :=
  ∑ i : I, L (EuclideanSpace.single i 1) σ * L (EuclideanSpace.single i 1) τ

def finiteStateHessianTrace
    (L : EuclideanSpace ℝ I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (H : FiniteStateField S) : ℝ :=
  ∑ i : I, fderiv ℝ (fderiv ℝ F) H (L (EuclideanSpace.single i 1))
    (L (EuclideanSpace.single i 1))

def finiteStateGradientSquareTrace
    (L : EuclideanSpace ℝ I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (H : FiniteStateField S) : ℝ :=
  ∑ i : I, (fderiv ℝ F H (L (EuclideanSpace.single i 1)))^2

variable [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem second_fderiv_finiteStateTerminal_eq_gibbsCovariance (V : S → ℝ)
    (H K M : FiniteStateField S) :
    fderiv ℝ (fderiv ℝ (gtStateLogPartition V)) H K M =
      (∫ σ, K σ * M σ ∂finiteStateGibbsKernel V H) -
        (∫ σ, K σ ∂finiteStateGibbsKernel V H) *
          (∫ τ, M τ ∂finiteStateGibbsKernel V H) := by
  rw [second_fderiv_gtStateLogPartition_apply]
  simp_rw [integral_finiteStateGibbsKernel]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem finiteStateHessianTrace_terminal (V : S → ℝ)
    (L : EuclideanSpace ℝ I →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    finiteStateHessianTrace L (gtStateLogPartition V) H =
      (∫ σ, finiteStateSpectralCovariance L σ σ ∂finiteStateGibbsKernel V H) -
        ∫ z, finiteStateSpectralCovariance L z.1 z.2
          ∂(finiteStateGibbsKernel V H).prod (finiteStateGibbsKernel V H) := by
  haveI := isMarkovKernel_finiteStateGibbsKernel V
  unfold finiteStateHessianTrace finiteStateSpectralCovariance
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite),
    integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_prod_mul, second_fderiv_finiteStateTerminal_eq_gibbsCovariance]
  rw [Finset.sum_sub_distrib]

theorem finiteStateGradientSquareTrace_eq_independentGibbs (V : S → ℝ)
    (L : EuclideanSpace ℝ I →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    finiteStateGradientSquareTrace L (gtStateLogPartition V) H =
      ∫ z, finiteStateSpectralCovariance L z.1 z.2
        ∂(finiteStateGibbsKernel V H).prod (finiteStateGibbsKernel V H) := by
  haveI := isMarkovKernel_finiteStateGibbsKernel V
  unfold finiteStateGradientSquareTrace finiteStateSpectralCovariance
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_prod_mul, pow_two]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finiteStateGibbsKernel, fderiv_gtStateLogPartition_apply]

end FourPapersCommon
