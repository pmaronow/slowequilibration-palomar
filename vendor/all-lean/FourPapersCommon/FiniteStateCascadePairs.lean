module
public import FourPapersCommon.FiniteStateCascadeExpectations

@[expose] public section

/-! Independent terminal replicas at a genuine common cascade field. Their
coordinate moments equal products of the actual cascade differential, and
their covariance contractions are finite integrals under probability laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
variable {S I : Type*} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem integral_finiteStateCascadeSplitLaw_mul (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p j : ℕ) (H : FiniteStateField S) (f g : S → ℝ) :
    (∫ z, f z.1 * g z.2 ∂finiteStateCascadeSplitLaw V a L p j H) =
      ∫ y, (∫ σ, f σ ∂finiteStateCascadeGibbsKernel V a L p y) *
        (∫ τ, g τ ∂finiteStateCascadeGibbsKernel V a L p y)
        ∂sourceKernelLaw
          (fun q => finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (p+q)) j H := by
  classical
  haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L p
  haveI := isMarkovKernel_sourceKernelLaw
    (fun q => finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (p+q))
    (fun q => isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L (p+q)) j
  have hb (z : S × S) : |f z.1 * g z.2| ≤
      (∑ σ : S, |f σ|) * (∑ τ : S, |g τ|) := by
    rw [abs_mul]
    exact mul_le_mul
      (Finset.single_le_sum (f := fun σ : S => |f σ|)
        (fun σ _ => abs_nonneg (f σ)) (Finset.mem_univ z.1))
      (Finset.single_le_sum (f := fun τ : S => |g τ|)
        (fun τ _ => abs_nonneg (g τ)) (Finset.mem_univ z.2))
      (abs_nonneg _) (Finset.sum_nonneg (fun σ _ => abs_nonneg (f σ)))
  rw [finiteStateCascadeSplitLaw, Measure.comp_eq_comp_const_apply,
    Kernel.integral_comp (source_bounded_integrable _ _ (measurable_of_finite _)
      ((∑ σ : S, |f σ|) * (∑ τ : S, |g τ|)) hb)]
  simp only [Kernel.const_apply, Kernel.prod_apply, integral_prod_mul]

theorem integral_finiteStateCascadeSplitLaw_coordinates (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p j : ℕ) (H K M : FiniteStateField S) :
    (∫ z, K z.1 * M z.2 ∂finiteStateCascadeSplitLaw V a L p j H) =
      ∫ y, fderiv ℝ (finiteStateGaussianTerminalCascade V a L p) y K *
        fderiv ℝ (finiteStateGaussianTerminalCascade V a L p) y M
        ∂sourceKernelLaw
          (fun q => finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (p+q)) j H := by
  rw [integral_finiteStateCascadeSplitLaw_mul V a ha L p j H]
  simp_rw [← fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean V a ha L p]

theorem finiteStateCascadeSplitLaw_nonneg (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p j : ℕ) (H : FiniteStateField S) (Q : S × S → ℝ)
    (hQ : ∀ z, 0 ≤ Q z) :
    0 ≤ ∫ z, Q z ∂finiteStateCascadeSplitLaw V a L p j H :=
  integral_nonneg hQ

theorem finiteStateCascadeSplitLaw_le (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p j : ℕ) (H : FiniteStateField S) (Q : S × S → ℝ)
    (C : ℝ) (hQ : ∀ z, Q z ≤ C) :
    (∫ z, Q z ∂finiteStateCascadeSplitLaw V a L p j H) ≤ C := by
  haveI := isProbabilityMeasure_finiteStateCascadeSplitLaw V a ha L p j H
  have hi : Integrable Q (finiteStateCascadeSplitLaw V a L p j H) :=
    Integrable.of_finite
  calc
    _ ≤ ∫ _, C ∂finiteStateCascadeSplitLaw V a L p j H :=
      integral_mono hi (integrable_const C) hQ
    _ = C := by simp

end FourPapersCommon
