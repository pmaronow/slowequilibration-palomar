-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetCovariance

@[expose] public section

/-! The actual quadratic latitude bank is uncorrelated with every component
of the center's value, radial score, and tangent gradient observation. These
are identities in the original tensor disorder, prior to any Palm regression.
The gradient identity uses the manuscript's supported-degree assumption. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open SphericalTwoPointCovariance
open scoped RealInnerProductSpace
set_option autoImplicit false

private theorem mixture_supported_degree_three (μ : FiniteMixture)
    (hμ : 3 ≤ μ.minDegree) :
    ∀ p, mixtureCoefficients μ p ≠ 0 → 3 ≤ p.val.val := by
  intro p hp
  exact hμ.trans (μ.degree_bounds (Finsupp.mem_support_iff.mpr hp)).1

/-- Exact zero covariance with the Hamiltonian value at the center. -/
theorem quadraticLatitudeJet_center_value_covariance_zero {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) (a : ℝ) (u ω : Vector N)
    (hω : inner ℝ ω u = 0) :
    cov[quadraticLatitudeJet μ a u ω,
      jet (mixtureCoefficients μ) 0 u (fun i => Fin.elim0 i);
        disorderLaw N μ.maxDegree] = 0 := by
  unfold quadraticLatitudeJet
  rw [covariance_const_mul_left,
    hessian_value_covariance hN _ (mixtureCoefficients_nonnegative μ)]
  simp [hω]

/-- Exact zero covariance with the extensive radial mark at the center. -/
theorem quadraticLatitudeJet_center_radial_covariance_zero {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree) (a : ℝ) (u ω : Vector N)
    (hω : inner ℝ ω u = 0) :
    cov[quadraticLatitudeJet μ a u ω,
      jet (mixtureCoefficients μ) 1 u (fun _ => u);
        disorderLaw N μ.maxDegree] = 0 := by
  unfold quadraticLatitudeJet
  rw [covariance_const_mul_left,
    hessian_radial_covariance hN _ (mixtureCoefficients_nonnegative μ)
      (mixture_supported_degree_three μ hμ)]
  simp [hω]

/-- Exact zero covariance with an arbitrary tangent directional gradient at
the center. Thus the entire center tangent-gradient vector has zero cross
covariance with the quadratic bank, not just one selected direction. -/
theorem quadraticLatitudeJet_center_tangent_covariance_zero {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree) (a : ℝ) (u ω v : Vector N)
    (hω : inner ℝ ω u = 0) :
    cov[quadraticLatitudeJet μ a u ω,
      jet (mixtureCoefficients μ) 1 u (fun _ => v);
        disorderLaw N μ.maxDegree] = 0 := by
  unfold quadraticLatitudeJet
  rw [covariance_const_mul_left,
    hessian_gradient_covariance hN _ (mixtureCoefficients_nonnegative μ)
      (mixture_supported_degree_three μ hμ)]
  simp [hω]

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
