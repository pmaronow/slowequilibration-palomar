module

public import SphericalAging.C2ObservableDerivative
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

public section

/-! Actual C¹ gradient and uniformly continuous bounded Hessian of a C²
compactly supported finite-dimensional observable. -/
noncomputable section
open Set Filter Topology
open scoped NNReal
namespace SphericalAging.CompactObservableGradient
open HardSphereDynamics
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {f : State N → ℝ}

theorem gradient_contDiff_one (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (gradient f) := by
  exact (InnerProductSpace.toDual ℝ (State N)).symm.toContinuousLinearEquiv.contDiff.comp
    (hf.fderiv_right (m := 1) (by norm_num))

theorem gradient_hasCompactSupport (hfc : HasCompactSupport f) : HasCompactSupport (gradient f) := by
  exact (hfc.fderiv ℝ).comp_left (by simp)

theorem gradient_uniformContinuous (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    UniformContinuous (gradient f) :=
  (gradient_hasCompactSupport hfc).uniformContinuous_of_continuous
    (gradient_contDiff_one hf).continuous

theorem gradient_fderiv_uniformContinuous (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    UniformContinuous (fderiv ℝ (gradient f)) :=
  ((gradient_hasCompactSupport hfc).fderiv ℝ).uniformContinuous_of_continuous
    ((gradient_contDiff_one hf).continuous_fderiv (by norm_num))

theorem gradient_fderiv_bounded (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ K : ℝ≥0,∀ x,‖fderiv ℝ (gradient f) x‖≤K := by
  obtain ⟨K,hK⟩ := ((gradient_hasCompactSupport hfc).fderiv ℝ).exists_bound_of_continuous
    ((gradient_contDiff_one hf).continuous_fderiv (by norm_num))
  exact ⟨⟨max K 0,le_max_right _ _⟩,fun x => (hK x).trans (le_max_left _ _)⟩

end SphericalAging.CompactObservableGradient
