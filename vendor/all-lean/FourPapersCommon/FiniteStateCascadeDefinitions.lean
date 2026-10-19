module
public import OverlapPaper.ReplicaSourceGroupKernel
public import Lemmas.GuerraTalagrand.Bound.FiniteState
public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

/-! Covariance-independent finite-state Gaussian cascade definitions. Every
level is a genuine Gaussian logarithmic average, and its normalized transition
is the exponential tilt of that Gaussian. No cascade derivative is postulated. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open SpinGlass.AT
namespace FourPapersCommon
open OverlapPaper

variable {S I : Type*} [Fintype S] [Fintype I]
abbrev FiniteStateField (S : Type*) [Fintype S] := EuclideanSpace ℝ S
abbrev FiniteStateGaussianInput (I : Type*) [Fintype I] := EuclideanSpace ℝ I

def finiteStateGaussianRawKernel
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    Kernel (FiniteStateField S) (FiniteStateField S) :=
  ((Kernel.id : Kernel (FiniteStateField S) (FiniteStateField S)) ×ₖ
    Kernel.const (FiniteStateField S) (stdGaussian (FiniteStateGaussianInput I))).map
      (fun p => p.1 + L p.2)

instance isMarkovKernel_finiteStateGaussianRawKernel
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    IsMarkovKernel (finiteStateGaussianRawKernel L) := by
  unfold finiteStateGaussianRawKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

theorem finiteStateGaussianRawKernel_apply
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (H : FiniteStateField S) :
    finiteStateGaussianRawKernel L H =
      (stdGaussian (FiniteStateGaussianInput I)).map (fun z => H + L z) := by
  rw [finiteStateGaussianRawKernel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply]
  rw [Measure.dirac_prod, Measure.map_map (by fun_prop) measurable_prodMk_left]
  rfl

def finiteStateGaussianStep (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (H : FiniteStateField S) : ℝ :=
  sourceLogAverage (stdGaussian (FiniteStateGaussianInput I)) a (fun z => F (H + L z))

def finiteStateGaussianCascade (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) : ℕ → FiniteStateField S → ℝ
  | 0 => F
  | j + 1 => finiteStateGaussianStep (a j) (L j) (finiteStateGaussianCascade a L F j)

def finiteStateGaussianTerminalCascade (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    ℕ → FiniteStateField S → ℝ :=
  finiteStateGaussianCascade a L (gtStateLogPartition V)

def finiteStateGaussianStepLaw (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (H : FiniteStateField S) : Measure (FiniteStateField S) :=
  (finiteStateGaussianRawKernel L H).tilted (fun H' => a * F H')

def finiteStateGaussianStepMean (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F G : FiniteStateField S → ℝ) (H : FiniteStateField S) : ℝ :=
  ∫ H', G H' ∂finiteStateGaussianStepLaw a L F H

theorem finiteStateGaussianStepLaw_eq_map_tilted (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : Measurable F) (H : FiniteStateField S) :
    finiteStateGaussianStepLaw a L F H =
      ((stdGaussian (FiniteStateGaussianInput I)).tilted (fun z => a * F (H + L z))).map
        (fun z => H + L z) := by
  rw [finiteStateGaussianStepLaw, finiteStateGaussianRawKernel_apply,
    tilted_map_eq _ _ (by fun_prop) _ (hF.const_mul a)]

theorem isProbabilityMeasure_finiteStateGaussianStepLaw (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : Measurable F) (H : FiniteStateField S)
    (he : Integrable (fun z => Real.exp (a * F (H + L z)))
      (stdGaussian (FiniteStateGaussianInput I))) :
    IsProbabilityMeasure (finiteStateGaussianStepLaw a L F H) := by
  rw [finiteStateGaussianStepLaw_eq_map_tilted a L F hF H]
  haveI := isProbabilityMeasure_tilted he
  infer_instance

theorem finiteStateGaussianStepLaw_zero
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (H : FiniteStateField S) :
    finiteStateGaussianStepLaw 0 L F H = finiteStateGaussianRawKernel L H := by
  simp [finiteStateGaussianStepLaw]

theorem finiteStateGaussianStepMean_one (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : Measurable F) (H : FiniteStateField S)
    (he : Integrable (fun z => Real.exp (a * F (H + L z)))
      (stdGaussian (FiniteStateGaussianInput I))) :
    finiteStateGaussianStepMean a L F (fun _ => 1) H = 1 := by
  haveI := isProbabilityMeasure_finiteStateGaussianStepLaw a L F hF H he
  simp [finiteStateGaussianStepMean]

end FourPapersCommon
