-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCommonHessianCovariance
public import SlowEquilibration.SphericalTAPCriticalAnalyticNeighborhood

@[expose] public section

/-! The tangential-degree-two part of the original spherical Hamiltonian is
its genuine second Taylor jet in a transverse direction. Its covariance is
exactly the quadratic latitude kernel printed in source Lemma 12.8. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open SphericalTwoPointCovariance SphericalTAPCriticalAnalyticNeighborhood
open scoped RealInnerProductSpace
set_option autoImplicit false

/-- The actual degree-two Taylor bank at latitude `a`, defined on the same
original ordered tensor disorder as the Hamiltonian. -/
def quadraticLatitudeJet {N : ℕ} (μ : FiniteMixture) (a : ℝ)
    (u ω : Vector N) (J : Disorder N μ.maxDegree) : ℝ :=
  ((1-a^2)/2) * jet (mixtureCoefficients μ) 2 (a • u) ![ω,ω] J

/-- The original tensor bank has the literal `N v₂(a) R²` covariance at
every normalized center and arbitrary transverse directions. -/
theorem quadraticLatitudeJet_covariance {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) (a : ℝ) (u ω ω' : Vector N)
    (hu : ‖u‖^2=(N:ℝ))
    (hω : inner ℝ ω u=0) (hω' : inner ℝ ω' u=0) :
    cov[quadraticLatitudeJet μ a u ω,
      quadraticLatitudeJet μ a u ω'; disorderLaw N μ.maxDegree] =
      (N:ℝ)*sourceQuadraticLatitudeVariance μ a*(overlap ω ω')^2 := by
  let c := mixtureCoefficients μ
  have hωa : inner ℝ ω (a • u)=0 := by simp [inner_smul_right,hω]
  have hω'a : inner ℝ ω' (a • u)=0 := by simp [inner_smul_right,hω']
  have hcov := common_hessian_covariance hN c
    (mixtureCoefficients_nonnegative μ)
    (a • u) (a • u) ω ω ω' ω' hωa hωa
  have hself : overlap (a • u) (a • u)=a^2 := by
    unfold overlap
    rw [inner_smul_left,inner_smul_right,real_inner_self_eq_norm_sq,hu]
    have hNr : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
    simp [pow_two]
  unfold quadraticLatitudeJet
  simp only [covariance_const_mul_left,covariance_const_mul_right]
  rw [hcov,hself,secondCovariance_mixture]
  unfold sourceQuadraticLatitudeVariance overlap
  have hNr : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [real_inner_comm ω' ω]
  field_simp
  ring

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
