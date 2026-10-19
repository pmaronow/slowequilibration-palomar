-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureConditionalPointVariance

@[expose] public section

/-! Exact original-disorder pointwise conditional Gibbs factor at a pure
critical point, with the manuscript's latitude residual polynomial. -/

namespace SlowEquilibration.SphericalPureConditionalPointMean
noncomputable section
open MeasureTheory Set SphericalModel SphericalCriticalLatitude
open SphericalParisiPureLatitudeCovariance
open SphericalTAPCriticalPureLatitudeVariance
open SphericalPureConditionalPointMGF
open SphericalPureConditionalPointVariance
open SphericalGaussianJet WholeFieldRegression
open SphericalMarkedWindows SphericalTaylorRemainder
open SphericalPosteriorMaps
set_option autoImplicit false

theorem valueConditioned_pure_point_exp_mean
    (n p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q r : ℝ} (hQ : 0 < Q)
    (u w : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (hw : ‖w‖^2=(n+1 : ℕ)) (hr : overlap u w=r)
    (β e : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫ J, Real.exp (β*field c J w) ∂valueConditionedLaw c u hu e) =
      Real.exp ((n+1 : ℕ)*
        (β*e*r^p+β^2*Q^p*sourcePureLatitudeVariance p alpha r/2)) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let f := (valueObservation c w).comp (valueCriticalCoefficientResidual n μ Q u)
  have hm : valueObservation c w (valueLift n μ Q u ((n+1 : ℕ)*e)) =
      (n+1 : ℕ)*e*r^p := by
    rw [valueLift_eq n μ hQ.le u hu]
    rw [center_value_only_lift n μ hQ u hu w e,hr]
    dsimp only [μ]
    rw [mul_div_assoc]
    rw [pure_center_value_ratio p hp alpha halpha hQ]
    ring
  have hv : ‖f.adjoint 1‖^2 = (n+1 : ℕ)*Q^p*
      sourcePureLatitudeVariance p alpha r :=
    valueConditioned_pure_point_variance n p hp alpha halpha hQ u w hu hw hr
  rw [valueConditioned_exp_point n μ hQ u hu w β e,hm,hv]
  congr 1
  ring

end
end SlowEquilibration.SphericalPureConditionalPointMean
