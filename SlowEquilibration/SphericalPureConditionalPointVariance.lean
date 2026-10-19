-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureConditionalPointMGF
public import SlowEquilibration.SphericalTAPCriticalPureLatitudeVariance
public import SlowEquilibration.SphericalParisiPureLatitudeCovariance

@[expose] public section

/-! The conditioned pure point variance is the literal source residual
polynomial at the physical latitude. -/

namespace SlowEquilibration.SphericalPureConditionalPointVariance
noncomputable section
open Set SphericalModel SphericalCriticalLatitude
open SphericalGaussianJet WholeFieldRegression
open SphericalTaylorRemainder
open SphericalParisiConditionedLatitudeCovariance
open SphericalParisiPureLatitudeCovariance
open SphericalTAPCriticalPureLatitudeVariance
open SphericalPureConditionalPointMGF
open scoped RealInnerProductSpace
set_option autoImplicit false

private theorem sourceValueTau_pure_self_eq
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q) (r : ℝ) :
    sourceValueTau (FiniteMixture.pure p hp alpha halpha) Q r 1 =
      Q^p*sourcePureLatitudeVariance p alpha r := by
  have hpow1 : (r^2)^p = r^(2*p) := by rw [←pow_mul]
  have hpow2 : (r^2)^(p-1)=r^(2*p-2) := by
    rw [←pow_mul]
    congr 1
    omega
  unfold sourceValueTau sourcePureLatitudeVariance
  rw [show r^2+(1-r^2)*1=1 by ring]
  simp only [mul_one]
  rw [pure_value_correction p hp alpha halpha hQ,
    mul_div_assoc,
    pure_gradient_correction p hp alpha halpha hQ,
    pure_centerCovariance p hp alpha halpha,
    pure_centerCovariance p hp alpha halpha,
    pure_centerFirst p hp alpha halpha]
  rw [hpow1,hpow2]
  ring

/-- Genuine pure posterior variance at any original spin of prescribed
latitude; the natural dimension factor is the actual sphere dimension. -/
theorem valueConditioned_pure_point_variance
    (n p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q r : ℝ} (hQ : 0 < Q)
    (u w : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (hw : ‖w‖^2=(n+1 : ℕ)) (hr : overlap u w=r) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let f := (valueObservation c w).comp (valueCriticalCoefficientResidual n μ Q u)
    ‖f.adjoint 1‖^2 = (n+1 : ℕ)*Q^p*sourcePureLatitudeVariance p alpha r := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let f := (valueObservation c w).comp (valueCriticalCoefficientResidual n μ Q u)
  have hself : overlap w w = r^2+(1-r^2)*1 := by
    rw [overlap_self (by omega) w hw]
    ring
  have hv := actual_value_critical_residual_kernel n μ hQ u hu w w hr hr hself
  dsimp only at hv
  have hnorm : ‖f.adjoint 1‖^2 = f (f.adjoint 1) := by
    rw [←real_inner_self_eq_norm_sq,f.adjoint_inner_left]
    simp
  rw [hnorm]
  calc
    f (f.adjoint 1) = (n+1 : ℕ)*sourceValueTau μ Q r 1 := by
      convert hv using 1
      simp only [sourceValueTau]
    _ = (n+1 : ℕ)*Q^p*sourcePureLatitudeVariance p alpha r := by
      rw [sourceValueTau_pure_self_eq p hp alpha halpha hQ]
      ring

end
end SlowEquilibration.SphericalPureConditionalPointVariance
