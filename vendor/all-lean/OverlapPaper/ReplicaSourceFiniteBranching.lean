module
public import OverlapPaper.ReplicaSourceTensor
public import FourPapersCommon.MixedFiniteKernelConcatenation
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-! Actual finite scalar transitions, independently continued in every replica
coordinate. The coefficient is computed from the normalized endpoint kernels;
unmarked coordinates remain present and the empty mark has coefficient one. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass SpinGlass.Targets FourPapersCommon
namespace OverlapPaper

def replicaTerminalChildrenKernel {k g d : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (p : ℕ) (parent : Fin d → Fin g) :
    Kernel (Fin g → ℝ) (Fin d → ℝ) :=
  replicaPiKernel d (fun l =>
    (mixedSchemeEndpointKernel ξ s p (k + 2 - p)).comap
      (fun x : Fin g → ℝ => x (parent l)) (measurable_pi_apply _))

theorem isMarkovKernel_replicaTerminalChildrenKernel {k g d : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (p : ℕ)
    (hp : p ≤ k + 2) (parent : Fin d → Fin g) :
    IsMarkovKernel (replicaTerminalChildrenKernel ξ s p parent) := by
  haveI := isMarkovKernel_mixedSchemeEndpointKernel ξ s p (k + 2 - p) (by omega)
  exact isMarkovKernel_replicaPiKernel d _ (fun _ => inferInstance)

theorem integral_replicaTerminalChildrenKernel_coefficient {k g d : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (p : ℕ)
    (hp : p ≤ k + 2) (parent : Fin d → Fin g) (x : Fin g → ℝ)
    (J : Finset (Fin d)) :
    (∫ y, replicaTerminalCoefficient J y ∂replicaTerminalChildrenKernel ξ s p parent x) =
      ∏ l ∈ J, mixedGradient ξ (Paper.parisiSchemeMeasure s) (s.q p, x (parent l)) := by
  haveI := isMarkovKernel_mixedSchemeEndpointKernel ξ s p (k + 2 - p) (by omega)
  rw [replicaTerminalChildrenKernel, integral_replicaPiKernel_marked d _
    (fun _ => inferInstance)]
  congr 1
  ext l
  rw [Kernel.comap_apply, ← mixedGradient_eq_terminalTanh_average ξ s hp]

def replicaTerminalChildrenLaw {k g d : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (p : ℕ) (parent : Fin d → Fin g)
    (μ : Measure (Fin g → ℝ)) : Measure (Fin d → ℝ) :=
  replicaTerminalChildrenKernel ξ s p parent ∘ₘ μ

theorem isProbabilityMeasure_replicaTerminalChildrenLaw {k g d : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (p : ℕ)
    (hp : p ≤ k + 2) (parent : Fin d → Fin g)
    (μ : Measure (Fin g → ℝ)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (replicaTerminalChildrenLaw ξ s p parent μ) := by
  haveI := isMarkovKernel_replicaTerminalChildrenKernel ξ s p hp parent
  unfold replicaTerminalChildrenLaw
  infer_instance

theorem integral_replicaTerminalChildrenLaw_coefficient {k g d : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (p : ℕ)
    (hp : p ≤ k + 2) (parent : Fin d → Fin g)
    (μ : Measure (Fin g → ℝ)) [IsProbabilityMeasure μ] (J : Finset (Fin d)) :
    (∫ y, replicaTerminalCoefficient J y ∂replicaTerminalChildrenLaw ξ s p parent μ) =
      ∫ x, ∏ l ∈ J, mixedGradient ξ (Paper.parisiSchemeMeasure s)
        (s.q p, x (parent l)) ∂μ := by
  haveI := isMarkovKernel_replicaTerminalChildrenKernel ξ s p hp parent
  haveI := isProbabilityMeasure_replicaTerminalChildrenLaw ξ s p hp parent μ
  have hi := integrable_replicaTerminalCoefficient J
    (replicaTerminalChildrenLaw ξ s p parent μ)
  unfold replicaTerminalChildrenLaw at hi ⊢
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  simp_rw [Kernel.const_apply,
    integral_replicaTerminalChildrenKernel_coefficient ξ s p hp parent]

end OverlapPaper
