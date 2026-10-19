module
public import FourPapersCommon.FiniteStateCascadeGrowth

@[expose] public section

/-! Genuine normalized Markov kernels for every finite-state Gaussian cascade
level. The normalizers are actual Gaussian integrals, with integrability
proved from the inherited Lipschitz bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
namespace FourPapersCommon
variable {S I : Type*} [Fintype S] [Fintype I]

def finiteStateGaussianNormalizer (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (H : FiniteStateField S) : ℝ :=
  ∫ y, Real.exp (a * F y) ∂finiteStateGaussianRawKernel L H

def finiteStateGaussianStepKernel (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) : Kernel (FiniteStateField S) (FiniteStateField S) :=
  Kernel.withDensity (finiteStateGaussianRawKernel L)
    (fun H y => ENNReal.ofReal (Real.exp (a * F y) / finiteStateGaussianNormalizer a L F H))

theorem finiteStateGaussianStepKernel_apply (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : Measurable F) (H : FiniteStateField S) :
    finiteStateGaussianStepKernel a L F H = finiteStateGaussianStepLaw a L F H := by
  have hm : Measurable (finiteStateGaussianNormalizer a L F) :=
    ((hF.const_mul a).exp.stronglyMeasurable.integral_kernel).measurable
  rw [finiteStateGaussianStepKernel, Kernel.withDensity_apply _
    ((((hF.comp measurable_snd).const_mul a).exp.div (hm.comp measurable_fst)).ennreal_ofReal) H]
  rfl

theorem isMarkovKernel_finiteStateGaussianStepKernel (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) {C : NNReal} (hF : LipschitzWith C F) :
    IsMarkovKernel (finiteStateGaussianStepKernel a L F) := by
  constructor
  intro H
  rw [finiteStateGaussianStepKernel_apply a L F hF.continuous.measurable]
  exact isProbabilityMeasure_finiteStateGaussianStepLaw a L F hF.continuous.measurable H
    (integrable_exp_finiteStateGaussian_lipschitz F hF L H a)

def finiteStateGaussianCascadeKernel (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (j : ℕ) : Kernel (FiniteStateField S) (FiniteStateField S) :=
  finiteStateGaussianStepKernel (a j) (L j) (finiteStateGaussianCascade a L F j)

theorem isMarkovKernel_finiteStateGaussianCascadeKernel (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) {C : NNReal} (hF : LipschitzWith C F) (j : ℕ) :
    IsMarkovKernel (finiteStateGaussianCascadeKernel a L F j) :=
  isMarkovKernel_finiteStateGaussianStepKernel _ _ _
    (finiteStateGaussianCascade_lipschitz F hF a ha L j)

theorem isMarkovKernel_finiteStateGaussianTerminalCascadeKernel [Nonempty S]
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    IsMarkovKernel (finiteStateGaussianCascadeKernel a L (SpinGlass.AT.gtStateLogPartition V) j) :=
  isMarkovKernel_finiteStateGaussianCascadeKernel a ha L _ (finiteStateGaussianTerminal_lipschitz V) j

end FourPapersCommon
