module
public import FourPapersCommon.FiniteStateCascadeKernels
public import OverlapPaper.ReplicaSourceBranchingEstimate
public import Mathlib.MeasureTheory.Measure.Count

@[expose] public section

/-! Actual finite terminal Gibbs kernels and their transport through the
normalized Gaussian cascade. Split replicas are sampled independently after
a common normalized field, giving genuine probability laws at every cut. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass.AT
namespace FourPapersCommon
open OverlapPaper
open scoped BigOperators
variable {S I : Type*} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S]

def finiteStateGibbsKernel (V : S → ℝ) : Kernel (FiniteStateField S) S :=
  Kernel.withDensity (Kernel.const (FiniteStateField S) (Measure.count : Measure S))
    (fun H σ => ENNReal.ofReal (gtStateGibbs V H σ))

theorem finiteStateGibbsKernel_apply (V : S → ℝ) [Nonempty S] (H : FiniteStateField S) :
    finiteStateGibbsKernel V H =
      (Measure.count : Measure S).withDensity (fun σ => ENNReal.ofReal (gtStateGibbs V H σ)) := by
  unfold finiteStateGibbsKernel
  rw [Kernel.withDensity_apply _ (measurable_from_prod_countable_left
    (fun σ => (contDiff_gtStateGibbs V σ).continuous.measurable.ennreal_ofReal))]
  rfl

theorem isMarkovKernel_finiteStateGibbsKernel (V : S → ℝ) [Nonempty S] :
    IsMarkovKernel (finiteStateGibbsKernel V) := by
  constructor
  intro H
  constructor
  rw [finiteStateGibbsKernel_apply V H, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_count, tsum_fintype,
    ← ENNReal.ofReal_sum_of_nonneg (fun σ _ => gtStateGibbs_nonneg V H σ),
    sum_gtStateGibbs]
  simp

theorem finiteStateGibbsKernel_singleton (V : S → ℝ) [Nonempty S]
    (H : FiniteStateField S) (σ : S) :
    finiteStateGibbsKernel V H {σ} = ENNReal.ofReal (gtStateGibbs V H σ) := by
  rw [finiteStateGibbsKernel_apply V H, withDensity_apply _ (measurableSet_singleton σ)]
  simp

def finiteStateCascadeFieldKernel (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    Kernel (FiniteStateField S) (FiniteStateField S) :=
  sourceKernelLaw (finiteStateGaussianCascadeKernel a L (gtStateLogPartition V)) j

def finiteStateCascadeGibbsKernel (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    Kernel (FiniteStateField S) S :=
  finiteStateGibbsKernel V ∘ₖ finiteStateCascadeFieldKernel V a L j

theorem isMarkovKernel_finiteStateCascadeFieldKernel (V : S → ℝ) [Nonempty S]
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    IsMarkovKernel (finiteStateCascadeFieldKernel V a L j) :=
  isMarkovKernel_sourceKernelLaw _
    (fun p => isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L p) j

theorem isMarkovKernel_finiteStateCascadeGibbsKernel (V : S → ℝ) [Nonempty S]
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    IsMarkovKernel (finiteStateCascadeGibbsKernel V a L j) := by
  haveI := isMarkovKernel_finiteStateCascadeFieldKernel V a ha L j
  haveI := isMarkovKernel_finiteStateGibbsKernel V
  unfold finiteStateCascadeGibbsKernel
  infer_instance

def finiteStateCascadeSplitLaw (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p j : ℕ) (H : FiniteStateField S) : Measure (S × S) :=
  (finiteStateCascadeGibbsKernel V a L p ×ₖ finiteStateCascadeGibbsKernel V a L p) ∘ₘ
    sourceKernelLaw (fun q => finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (p + q)) j H

theorem isProbabilityMeasure_finiteStateCascadeSplitLaw (V : S → ℝ) [Nonempty S]
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p j : ℕ) (H : FiniteStateField S) :
    IsProbabilityMeasure (finiteStateCascadeSplitLaw V a L p j H) := by
  haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L p
  haveI := isMarkovKernel_sourceKernelLaw
    (fun q => finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (p + q))
    (fun q => isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L (p + q)) j
  unfold finiteStateCascadeSplitLaw
  infer_instance

end FourPapersCommon
