-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedGradientSecond

@[expose] public section

/-! The literal two-score covariance reduction has the printed contact
second derivative. The proof differentiates its symmetric quadratic form
once, then uses the already verified contact regression row. -/

namespace SlowEquilibration.SphericalTAPMixedScoreSecond
noncomputable section
open SphericalTAPMixedBandExponent SphericalTAPMixedCrossSecond SphericalMarkedWindows
open SphericalTAPMixedContactDerivatives ConditionedEntrance
set_option autoImplicit false

def sourceMixedScoreReduction (μ : FiniteMixture) (Q a : ℝ) : ℝ :=
  sourceMixedCross μ Q a 0*valueTheta μ Q a+
    sourceMixedCross μ Q a 1*radialTheta μ Q a

private theorem score_quadratic (μ : FiniteMixture) (Q a : ℝ) :
    sourceMixedScoreReduction μ Q a =
      (secondScore μ Q*(μ.xi (Real.sqrt Q*a))^2-
        2*aScore μ Q*μ.xi (Real.sqrt Q*a)*
          (Real.sqrt Q*a*μ.xi1 (Real.sqrt Q*a))+
        μ.xi Q*(Real.sqrt Q*a*μ.xi1 (Real.sqrt Q*a))^2)/
        (μ.scoreCovariance Q).det := by
  unfold sourceMixedScoreReduction sourceMixedCross
  simp only [scorePairEquiv_apply, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [valueTheta_eq, radialTheta_eq]
  ring

theorem sourceMixedScoreReduction_first (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 ≤ Q) (a : ℝ) :
    deriv (sourceMixedScoreReduction μ Q) a =
      2*(Real.sqrt Q*μ.xi1 (Real.sqrt Q*a)*valueTheta μ Q a+
        (Real.sqrt Q*μ.xi1 (Real.sqrt Q*a)+
          Q*a*μ.xi2 (Real.sqrt Q*a))*radialTheta μ Q a) := by
  let f : ℝ → ℝ := fun t => μ.xi (Real.sqrt Q*t)
  let g : ℝ → ℝ := fun t => Real.sqrt Q*t*μ.xi1 (Real.sqrt Q*t)
  let A := aScore μ Q
  let C := secondScore μ Q
  let V := μ.xi Q
  let D := (μ.scoreCovariance Q).det
  have hf : HasDerivAt f (Real.sqrt Q*μ.xi1 (Real.sqrt Q*a)) a := by
    convert (μ.hasDerivAt_xi (Real.sqrt Q*a)).comp a
      ((hasDerivAt_id a).const_mul (Real.sqrt Q)) using 1 <;> first | rfl | ring
  have hg : HasDerivAt g (Real.sqrt Q*μ.xi1 (Real.sqrt Q*a)+
      Q*a*μ.xi2 (Real.sqrt Q*a)) a := by
    have hh := ((hasDerivAt_id a).const_mul (Real.sqrt Q)).mul
      ((μ.hasDerivAt_xi1 (Real.sqrt Q*a)).comp a
        ((hasDerivAt_id a).const_mul (Real.sqrt Q)))
    convert hh using 1
    · funext t
      rfl
    · simp only [Function.comp_apply, id_eq]
      ring_nf
      rw [Real.sq_sqrt hQ]
      ring
  have hquad : sourceMixedScoreReduction μ Q =
      fun t => (C*(f t)^2-2*A*f t*g t+V*(g t)^2)/D := by
    funext t
    exact score_quadratic μ Q t
  have hder : HasDerivAt (fun t => (C*(f t)^2-2*A*f t*g t+V*(g t)^2)/D)
      (2*(Real.sqrt Q*μ.xi1 (Real.sqrt Q*a)*(C*f a-A*g a)/D+
        (Real.sqrt Q*μ.xi1 (Real.sqrt Q*a)+Q*a*μ.xi2 (Real.sqrt Q*a))*
          (V*g a-A*f a)/D)) a := by
    convert ((((hf.pow 2).const_mul C).sub
      (((hf.mul hg).const_mul A).const_mul 2)).add
      ((hg.pow 2).const_mul V)).div_const D using 1
    · funext t
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
      ring
    · dsimp
      ring
  rw [hquad, hder.deriv]
  rw [valueTheta_eq, radialTheta_eq]
  dsimp [f,g,A,C,V,D]
  ring

theorem sourceMixedScoreReduction_second_contact
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) :
    deriv (deriv (sourceMixedScoreReduction μ Q)) (Real.sqrt Q) =
      2*μ.xi1 Q+4*Q*μ.xi2 Q := by
  let q := Real.sqrt Q
  let f : ℝ → ℝ := fun t => μ.xi (q*t)
  let g : ℝ → ℝ := fun t => q*t*μ.xi1 (q*t)
  have hq : q*q=Q := Real.mul_self_sqrt hQ.le
  have hq2 : q^2=Q := Real.sq_sqrt hQ.le
  have hf : HasDerivAt (fun t => q*μ.xi1 (q*t))
      (Q*μ.xi2 Q) q := by
    have hh := ((μ.hasDerivAt_xi1 (q*q)).comp q
      ((hasDerivAt_id q).const_mul q)).const_mul q
    convert hh using 1
    · funext t
      rfl
    · calc
        Q*μ.xi2 Q = μ.xi2 Q*(q*q) := by rw [hq]; ring
        _ = μ.xi2 Q*q^2 := by ring
        _ = q*(μ.xi2 (q*q)*(q*1)) := by
          conv_rhs => rw [hq]
          ring
  have hg : HasDerivAt (fun t => q*μ.xi1 (q*t)+Q*t*μ.xi2 (q*t))
      (2*Q*μ.xi2 Q+Q^2*μ.v1 Q) q := by
    have hh1 := ((μ.hasDerivAt_xi1 (q*q)).comp q
      ((hasDerivAt_id q).const_mul q)).const_mul q
    have hh2 := ((hasDerivAt_id q).const_mul Q).mul
      ((μ.hasDerivAt_xi2 (q*q)).comp q
        ((hasDerivAt_id q).const_mul q))
    convert hh1.add hh2 using 1
    · funext t
      rfl
    · simp only [Function.comp_apply, id_eq]
      rw [← hq]
      ring
  have hθ0 := valueTheta_hasDerivAt μ Q q
  have hθ1 := radialTheta_hasDerivAt μ Q q
  have hmain := ((hf.mul hθ0).add (hg.mul hθ1)).const_mul 2
  have hfun : deriv (sourceMixedScoreReduction μ Q) =
      fun t => 2*((q*μ.xi1 (q*t))*valueTheta μ Q t+
        (q*μ.xi1 (q*t)+Q*t*μ.xi2 (q*t))*radialTheta μ Q t) := by
    funext t
    exact sourceMixedScoreReduction_first μ hQ.le t
  rw [hfun]
  change HasDerivAt (fun t => 2*((q*μ.xi1 (q*t))*valueTheta μ Q t+
    (q*μ.xi1 (q*t)+Q*t*μ.xi2 (q*t))*radialTheta μ Q t)) _ q at hmain
  rw [hmain.deriv]
  have hv : valueTheta μ Q q=1 := by
    have hh := sourceMixedMean_contact μ hQ hnp 1 0
    simpa [sourceMixedMean,q] using hh
  have hr : radialTheta μ Q q=0 := by
    have hh := sourceMixedMean_contact μ hQ hnp 0 1
    simpa [sourceMixedMean,q] using hh
  obtain ⟨hvd,hrd⟩ := mixed_regression_row_derivative_contact μ hQ hnp
  rw [hv,hr,hvd,hrd,hq]
  have hqn : q ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  field_simp
  ring

end
end SlowEquilibration.SphericalTAPMixedScoreSecond
