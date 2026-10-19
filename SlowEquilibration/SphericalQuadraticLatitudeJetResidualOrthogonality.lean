-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPhysicalPalmMarginal

@[expose] public section

/-! The true degree-two Taylor bank is exactly the projection of the
original latitude field onto tangential Gaussian degree two. The covariance
is computed using the actual original tensor disorder and physical sphere. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open SphericalTwoPointCovariance
open SphericalTAPCriticalAnalyticNeighborhood
open scoped RealInnerProductSpace
set_option autoImplicit false

def originalLatitudePoint {N : ℕ} (a : ℝ)
    (u ω : Vector N) : Vector N :=
  a • u + Real.sqrt (1-a^2) • ω

/-- The genuine original-field covariance with the degree-two bank equals
the bank's own covariance, with exact `N v₂(a) R²` normalization. -/
theorem quadraticLatitudeJet_originalLatitudeField_covariance
    {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    (a : ℝ) (ha : 0 ≤ 1-a^2) (u ω ω' : Vector N)
    (hu : ‖u‖^2=(N:ℝ))
    (hω : inner ℝ ω u=0) (hω' : inner ℝ ω' u=0) :
    cov[quadraticLatitudeJet μ a u ω,
      fun J => field (mixtureCoefficients μ) J
        (originalLatitudePoint a u ω');
      disorderLaw N μ.maxDegree] =
      (N:ℝ)*sourceQuadraticLatitudeVariance μ a*(overlap ω ω')^2 := by
  let c := mixtureCoefficients μ
  let σ := originalLatitudePoint a u ω'
  have hNreal : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hinner : inner ℝ ω σ = Real.sqrt (1-a^2)*inner ℝ ω ω' := by
    simp [σ,originalLatitudePoint,inner_add_right,inner_smul_right,hω]
  have huω' : inner ℝ u ω' = 0 := by
    rw [real_inner_comm]
    exact hω'
  have hover : overlap (a • u) σ = a^2 := by
    unfold overlap σ originalLatitudePoint
    simp only [inner_add_right,real_inner_smul_left,inner_smul_right,
      real_inner_self_eq_norm_sq,hu,huω',mul_zero,add_zero]
    field_simp
  have hfield : (fun J : Disorder N μ.maxDegree => field c J σ) =
      jet c 0 σ (fun i => Fin.elim0 i) := by
    funext J
    simp only [jet,iteratedFDeriv_zero_apply]
  unfold quadraticLatitudeJet
  rw [covariance_const_mul_left,hfield,
    hessian_value_covariance hN c (mixtureCoefficients_nonnegative μ),
    hover,hinner,secondCovariance_mixture]
  unfold sourceQuadraticLatitudeVariance overlap
  calc
    (1-a^2)/2 *
      (μ.xi2 (a^2)/(N:ℝ) *
        (Real.sqrt (1-a^2)*inner ℝ ω ω') *
        (Real.sqrt (1-a^2)*inner ℝ ω ω')) =
      (1-a^2)/2 *
        (μ.xi2 (a^2)/(N:ℝ) *
          ((Real.sqrt (1-a^2)*inner ℝ ω ω')^2)) := by ring
    _ = (1-a^2)/2 *
        (μ.xi2 (a^2)/(N:ℝ) *
          ((1-a^2)*(inner ℝ ω ω')^2)) := by
          rw [mul_pow,Real.sq_sqrt ha]
    _ = _ := by field_simp

/-- Subtracting the genuine Y₂ bank leaves a field component orthogonal to
every degree-two bank probe at the same physical latitude. -/
theorem quadraticLatitudeJet_residualField_covariance_zero
    {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    (a : ℝ) (ha : 0 ≤ 1-a^2) (u ω ω' : Vector N)
    (hu : ‖u‖^2=(N:ℝ))
    (hω : inner ℝ ω u=0) (hω' : inner ℝ ω' u=0) :
    cov[quadraticLatitudeJet μ a u ω,
      fun J => field (mixtureCoefficients μ) J
        (originalLatitudePoint a u ω') -
        quadraticLatitudeJet μ a u ω' J;
      disorderLaw N μ.maxDegree] = 0 := by
  have hjet : MemLp (quadraticLatitudeJet μ a u ω) 2
      (disorderLaw N μ.maxDegree) :=
    (jet_memLp (mixtureCoefficients μ) 2 (a • u) ![ω,ω]).const_mul _
  have hfield : MemLp (fun J : Disorder N μ.maxDegree =>
      field (mixtureCoefficients μ) J (originalLatitudePoint a u ω')) 2
      (disorderLaw N μ.maxDegree) := by
    convert jet_memLp (mixtureCoefficients μ) 0
      (originalLatitudePoint a u ω') (fun i => Fin.elim0 i) using 1
    funext J
    simp only [jet,iteratedFDeriv_zero_apply]
  have hjet' : MemLp (quadraticLatitudeJet μ a u ω') 2
      (disorderLaw N μ.maxDegree) :=
    (jet_memLp (mixtureCoefficients μ) 2 (a • u) ![ω',ω']).const_mul _
  rw [covariance_fun_sub_right hjet hfield hjet',
    quadraticLatitudeJet_originalLatitudeField_covariance
      hN μ a ha u ω ω' hu hω hω',
    quadraticLatitudeJet_covariance hN μ a u ω ω' hu hω hω']
  ring

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
