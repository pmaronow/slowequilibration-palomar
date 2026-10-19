-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCenterFieldScale

@[expose] public section

/-! The literal conditional mean of `exp(β H_N)` at a spin of latitude r,
under value-and-gradient conditioning at an original pure critical point. -/

namespace SlowEquilibration.SphericalPureOriginalConditionalPointMean
noncomputable section
open MeasureTheory Set SphericalModel SphericalMarkedWindows
open SphericalGaussianJet SphericalTAPCriticalPureLatitudeVariance
open SphericalPureConditionalPointMean SphericalPureCenterFieldScale
set_option autoImplicit false

theorem pure_original_conditioned_point_exp_mean
    (n p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q r : ℝ} (hQ : 0 < Q)
    (u w : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (hw : ‖w‖^2=(n+1 : ℕ)) (hr : overlap u w=r)
    (β H : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let s := (Real.sqrt Q)^p
    (∫ J, Real.exp (β*field (mixtureCoefficients μ) J w)
      ∂valueConditionedLaw c u hu (s*H/(n+1 : ℕ))) =
      Real.exp (β*H*r^p+(n+1 : ℕ)*β^2*sourcePureLatitudeVariance p alpha r/2) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let s := (Real.sqrt Q)^p
  have hs : 0 < s := by dsimp [s]; positivity
  have hs2 : s^2 = Q^p := by
    dsimp [s]
    calc
      ((Real.sqrt Q)^p)^2 = ((Real.sqrt Q)^2)^p := by
        rw [←pow_mul,←pow_mul,Nat.mul_comm]
      _ = Q^p := by rw [Real.sq_sqrt hQ.le]
  have hdim : (0:ℝ)<(n+1 : ℕ) := by positivity
  have hpoint (J : Disorder (n+1) μ.maxDegree) :
      β*field (mixtureCoefficients μ) J w =
        (β/s)*field c J w := by
    rw [pure_center_field_eq_original_scale p hp alpha halpha hQ.le]
    dsimp only [s,μ]
    field_simp
  have hfunc :
      (fun J : Disorder (n+1) μ.maxDegree =>
        Real.exp (β*field (mixtureCoefficients μ) J w)) =
      (fun J => Real.exp ((β/s)*field c J w)) := by
    funext J
    rw [hpoint]
  change (∫ J, Real.exp (β*field (mixtureCoefficients μ) J w)
    ∂valueConditionedLaw c u hu (s*H/(n+1 : ℕ))) = _
  rw [hfunc]
  rw [valueConditioned_pure_point_exp_mean n p hp alpha halpha hQ
    u w hu hw hr (β/s) (s*H/(n+1 : ℕ))]
  congr 1
  rw [← hs2]
  field_simp

end
end SlowEquilibration.SphericalPureOriginalConditionalPointMean
