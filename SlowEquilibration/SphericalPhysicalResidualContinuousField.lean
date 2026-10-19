-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorResidualLaw

/-! Actual continuous residual fields on a unit transverse parameterization,
with the physical sqrt(N/d) and sqrt(d) sphere-coordinate factors retained. -/

@[expose] public section
namespace SlowEquilibration.SphericalCriticalLatitude
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalTaylorRemainder SphericalTwoPointCovariance
open GaussianContinuousFieldLaw
open scoped RealInnerProductSpace
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

omit [CompactSpace K] in
theorem physical_sphere_parameter_continuous {d : ℕ} (x : K → Vector d)
    (hx : Continuous x) : Continuous (fun v => Real.sqrt (d : ℝ) • x v) :=
  (hx.const_smul (Real.sqrt (d : ℝ))).congr (fun _ => rfl)

/-- The actual physical residual mixture, fixed before both dimensions. -/
def physicalResidualContinuousField (θ : FiniteMixture) (N d : ℕ)
    (x : K → Vector d) (hx : Continuous x) : EuclideanDisorder d θ.maxDegree →L[ℝ] C(K,ℝ) :=
  Real.sqrt ((N : ℝ)/(d : ℝ)) • modelContinuousField (mixtureCoefficients θ)
    (fun v => Real.sqrt (d : ℝ) • x v) (physical_sphere_parameter_continuous x hx)

omit [CompactSpace K] in
/-- Actual Gaussian evaluation covariance of the true finite residual
mixture, including its complete physical dimension normalization. -/
theorem physicalResidualContinuousField_covariance (θ : FiniteMixture)
    (N d : ℕ) (hd : 0 < d) (x : K → Vector d) (hx : Continuous x) (v w : K) :
    cov[fun g => physicalResidualContinuousField θ N d x hx g v,
      fun g => physicalResidualContinuousField θ N d x hx g w;
        stdGaussian (EuclideanDisorder d θ.maxDegree)]=
      (N : ℝ)*θ.xi (inner ℝ (x v) (x w)) := by
  have hEval (a : K) : evaluationFeature (physicalResidualContinuousField θ N d x hx) a=
      Real.sqrt ((N : ℝ)/(d : ℝ)) •
        valueObservation (mixtureCoefficients θ) (Real.sqrt (d : ℝ) • x a) := by
    ext g
    rfl
  have hOverlap : overlap (Real.sqrt (d : ℝ) • x v) (Real.sqrt (d : ℝ) • x w)=
      inner ℝ (x v) (x w) := by
    unfold overlap
    simp only [real_inner_smul_left,real_inner_smul_right]
    rw [show Real.sqrt (d : ℝ)*(Real.sqrt (d : ℝ)*inner ℝ (x v) (x w))=
      (Real.sqrt (d : ℝ))^2*inner ℝ (x v) (x w) by ring,
      Real.sq_sqrt (Nat.cast_nonneg d)]
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hd.ne')
  rw [evaluation_covariance,hEval v,hEval w,scalar_coupling_smul,
    value_value_coupling hd _ (mixtureCoefficients_nonnegative θ),
    covariancePolynomial_mixture,hOverlap,
    Real.sq_sqrt (div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg d))]
  field_simp [Nat.cast_ne_zero.mpr hd.ne']

end
end SlowEquilibration.SphericalCriticalLatitude
