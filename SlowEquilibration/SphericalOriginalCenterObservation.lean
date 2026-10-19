-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCriticalLatitudeScoreMean
public import SlowEquilibration.SphericalCriticalLatitudeGradientCross
public import SlowEquilibration.SphericalConditionedEntranceCorrection

/-! Actual original-field observations against center-field conditioning.
Spatial rescaling derives the genuine cross ξ(sqrtQ r), retaining the
original field and its actual score/gradient observation rows. -/

@[expose] public section
namespace SlowEquilibration.SphericalCriticalLatitude
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression SphericalTaylorRemainder
open SphericalParisiConditionedLatitudeCovariance IntrinsicGradientRegression SphericalForm
open SphericalMarkedWindows GaussianRegression
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def originalRescaledPoint {N : ℕ} (Q : ℝ) (x : Vector N) : Vector N := (Real.sqrt Q)⁻¹ • x

def originalSourceCross (μ : FiniteMixture) (Q r : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  scorePairEquiv (μ.xi (Real.sqrt Q*r),Real.sqrt Q*r*μ.xi1 (Real.sqrt Q*r))

private theorem mul_inv_sqrt {Q : ℝ} (hQ : 0<Q) : Q*(Real.sqrt Q)⁻¹=Real.sqrt Q := by
  have hs : Real.sqrt Q≠0 := (Real.sqrt_pos.mpr hQ).ne'
  apply (mul_right_cancel₀ hs)
  rw [mul_assoc,inv_mul_cancel₀ hs,mul_one,Real.mul_self_sqrt hQ.le]

private theorem overlap_originalRescaledPoint {N : ℕ} (Q : ℝ) (u x : Vector N) :
    overlap u (originalRescaledPoint Q x)=(Real.sqrt Q)⁻¹*overlap u x := by
  unfold overlap originalRescaledPoint
  rw [real_inner_smul_right]
  ring

/-- Original field observation is the literal center-field observation at x/sqrtQ. -/
theorem original_valueObservation_eq_center_rescaled {N : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (x : Vector N) :
    valueObservation (mixtureCoefficients μ) x=
      valueObservation (centerCoefficients (mixtureCoefficients μ) Q) (originalRescaledPoint Q x) := by
  have hs : Real.sqrt Q≠0 := (Real.sqrt_pos.mpr hQ).ne'
  ext g
  simp only [valueObservation,flatJetCLM_apply,jet,iteratedFDeriv_zero_apply]
  rw [field_center_scale _ (mixtureCoefficients_nonnegative μ) hQ.le]
  simp only [originalRescaledPoint,smul_smul,mul_inv_cancel₀ hs,one_smul]

/-- Literal source cross vector follows from the true all-point center covariance. -/
theorem sourceCross_original_rescaling {N : ℕ} (μ : FiniteMixture) {Q : ℝ} (hQ : 0<Q)
    (u x : Vector N) :
    sourceCross μ Q (overlap u (originalRescaledPoint Q x))=originalSourceCross μ Q (overlap u x) := by
  have he : Q*overlap u (originalRescaledPoint Q x)=Real.sqrt Q*overlap u x := by
    rw [overlap_originalRescaledPoint,←mul_assoc,mul_inv_sqrt hQ]
  apply PiLp.ext
  intro i
  fin_cases i
  · change μ.xi (Q*overlap u (originalRescaledPoint Q x))=μ.xi (Real.sqrt Q*overlap u x)
    rw [he]
  · change overlap u (originalRescaledPoint Q x)*(Q*μ.xi1 (Q*overlap u (originalRescaledPoint Q x)))=
      Real.sqrt Q*overlap u x*μ.xi1 (Real.sqrt Q*overlap u x)
    rw [he,overlap_originalRescaledPoint]
    calc
      _=(Q*(Real.sqrt Q)⁻¹)*overlap u x*μ.xi1 (Real.sqrt Q*overlap u x) := by ring
      _=_ := by rw [mul_inv_sqrt hQ]

/-- Actual original-field/center-score row covariance, not a covariance-law premise. -/
theorem original_score_value_cross {N : ℕ} (hN : 0<N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (u x : Vector N) :
    scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u
      ((valueObservation (mixtureCoefficients μ) x).adjoint 1)=
      (N : ℝ) • originalSourceCross μ Q (overlap u x) := by
  rw [original_valueObservation_eq_center_rescaled μ hQ x,
    center_score_value_cross hN μ hQ.le,sourceCross_original_rescaling μ hQ]

/-- Actual original-field/center-gradient covariance gives the precise
source tangent multiplier, with ξ′ evaluated at sqrtQ r. -/
theorem original_gradient_value_cross {N : ℕ} (hN : 0<N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (u x : Vector N) :
    intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) u
      ((valueObservation (mixtureCoefficients μ) x).adjoint 1)=
      (Real.sqrt Q*μ.xi1 (Real.sqrt Q*overlap u x)) • (tangentPlane u).orthogonalProjectionOnto x := by
  have he : Q*overlap u (originalRescaledPoint Q x)=Real.sqrt Q*overlap u x := by
    rw [overlap_originalRescaledPoint,←mul_assoc,mul_inv_sqrt hQ]
  rw [original_valueObservation_eq_center_rescaled μ hQ x,
    center_gradient_value_cross hN μ hQ.le,he]
  simp only [originalRescaledPoint,map_smul,smul_smul]
  congr 1
  calc
    _=(Q*(Real.sqrt Q)⁻¹)*μ.xi1 (Real.sqrt Q*overlap u x) := by ring
    _=_ := by rw [mul_inv_sqrt hQ]

end
end SlowEquilibration.SphericalCriticalLatitude
