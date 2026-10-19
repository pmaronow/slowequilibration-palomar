-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalAtomSmoothCutoffApproximation

/-! Actual Gibbs stationarity for the original sampled field plus a smooth
finite-atom cutoff correction. The genuine common-Brownian smooth diffusion
is obtained through the proved uniform C¹ physical tensor approximation. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalAtomSmoothCutoffApproximation
open Set MeasureTheory ProbabilityTheory
open SphericalModel ConditionedEntrance.TensorPolynomial SphericalSmoothTensorStationarity
open scoped NNReal RealInnerProductSpace
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N P : ℕ} {ι : Type*} [Fintype ι]

/-- No approximation or stationarity conclusion is an assumption. All
source atoms, cutoffs and original ordered coefficients are literal data. -/
theorem atomSmoothCutoffField_gibbs_invariant (hN : 1 ≤ N) (hP : 2 ≤ P) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (hdegree : μ.maxDegree ≤ P) (a : ι → Atom N P)
    (v₁ v₂ : Vector N) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) (β : ℝ) (t : ℝ≥0) :
    smoothTransitionKernel (atomSmoothCutoffField μ J a v₁ v₂ χ)
      (atomSmoothCutoffField_contDiff hN hP μ J a v₁ v₂ χ hχ) β t ∘ₘ
      gibbsLaw N β (atomSmoothCutoffField μ J a v₁ v₂ χ)=
        gibbsLaw N β (atomSmoothCutoffField μ J a v₁ v₂ χ) := by
  obtain ⟨ν,K,M,δ,hM,hfield,hδ,hgrad,hlim⟩ :=
    exists_actual_tensor_approximants hN hP μ J hdegree a v₁ v₂ χ hχ
  exact smoothTransitionKernel_gibbs_invariant hN _ _ ν K M hM hfield δ hδ hgrad hlim β t

end SlowEquilibration.SphericalAtomSmoothCutoffApproximation
