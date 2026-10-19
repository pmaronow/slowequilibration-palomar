-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedContactHessian

@[expose] public section

/-! First contact derivatives of the literal mixed original-field regression
row. In particular the mixed radial-latitude Hessian entry is β/√Q. -/

namespace SlowEquilibration.SphericalTAPMixedContactDerivatives
noncomputable section
open Set SphericalMarkedWindows ConditionedEntrance
open SphericalTAPMixedBandExponent
set_option autoImplicit false

private theorem regression_row_first (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (a : ℝ) :
    valueTheta μ Q a*μ.xi Q+radialTheta μ Q a*(Q*μ.xi1 Q)=
      μ.xi (Real.sqrt Q*a) := by
  have hh := congrFun (regression_score_row_correct μ hQ hnp a) (0 : Fin 2)
  simpa [Matrix.vecMul,dotProduct,Fin.sum_univ_two,
    FiniteMixture.scoreCovariance] using hh

private theorem regression_row_second (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (a : ℝ) :
    valueTheta μ Q a*(Q*μ.xi1 Q)+
      radialTheta μ Q a*(Q*μ.xi1 Q+Q^2*μ.xi2 Q)=
      Real.sqrt Q*a*μ.xi1 (Real.sqrt Q*a) := by
  have hh := congrFun (regression_score_row_correct μ hQ hnp a) (1 : Fin 2)
  simpa [Matrix.vecMul,dotProduct,Fin.sum_univ_two,
    FiniteMixture.scoreCovariance] using hh

/-- Differentiating the true score regression row at the physical contact
latitude yields the second covariance row divided by √Q. -/
theorem mixed_regression_row_derivative_contact (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) :
    valueThetaDerivative μ Q (Real.sqrt Q)=0 ∧
      radialThetaDerivative μ Q (Real.sqrt Q)=1/Real.sqrt Q := by
  let q := Real.sqrt Q
  have hq : 0 < q := Real.sqrt_pos.mpr hQ
  have hq2 : q*q=Q := Real.mul_self_sqrt hQ.le
  have hcomp : HasDerivAt (fun a : ℝ => q*a) q q :=
    by simpa only [id_eq,mul_one] using (hasDerivAt_id q).const_mul q
  have hfirst := congrArg (fun f : ℝ → ℝ => deriv f q)
    (funext (regression_row_first μ hQ hnp))
  have hleft1 : HasDerivAt
      (fun a => valueTheta μ Q a*μ.xi Q+radialTheta μ Q a*(Q*μ.xi1 Q))
      (valueThetaDerivative μ Q q*μ.xi Q+
        radialThetaDerivative μ Q q*(Q*μ.xi1 Q)) q :=
    ((valueTheta_hasDerivAt μ Q q).mul_const _).add
      ((radialTheta_hasDerivAt μ Q q).mul_const _)
  have hright1 : HasDerivAt (fun a : ℝ => μ.xi (q*a))
      (μ.xi1 Q*q) q := by
    simpa only [hq2,Function.comp_def] using
      (μ.hasDerivAt_xi (q*q)).comp q hcomp
  have hEq1 : valueThetaDerivative μ Q q*μ.xi Q+
      radialThetaDerivative μ Q q*(Q*μ.xi1 Q)=μ.xi1 Q*q := by
    exact hleft1.deriv.symm.trans (hfirst.trans hright1.deriv)
  have hsecond := congrArg (fun f : ℝ → ℝ => deriv f q)
    (funext (regression_row_second μ hQ hnp))
  have hleft2 : HasDerivAt
      (fun a => valueTheta μ Q a*(Q*μ.xi1 Q)+
        radialTheta μ Q a*(Q*μ.xi1 Q+Q^2*μ.xi2 Q))
      (valueThetaDerivative μ Q q*(Q*μ.xi1 Q)+
        radialThetaDerivative μ Q q*(Q*μ.xi1 Q+Q^2*μ.xi2 Q)) q :=
    ((valueTheta_hasDerivAt μ Q q).mul_const _).add
      ((radialTheta_hasDerivAt μ Q q).mul_const _)
  have hright2 : HasDerivAt (fun a : ℝ => q*a*μ.xi1 (q*a))
      (q*μ.xi1 Q+Q*q*μ.xi2 Q) q := by
    have hm := (hasDerivAt_const q q).mul (hasDerivAt_id q)
    have hxi := (μ.hasDerivAt_xi1 (q*q)).comp q hcomp
    have hh := hm.mul hxi
    change HasDerivAt (fun a => q*a*μ.xi1 (q*a)) _ q at hh
    convert hh using 1
    simp only [Pi.mul_apply,id_eq,Function.comp_apply,zero_mul,zero_add,mul_one]
    rw [hq2]
    ring
  have hEq2 : valueThetaDerivative μ Q q*(Q*μ.xi1 Q)+
      radialThetaDerivative μ Q q*(Q*μ.xi1 Q+Q^2*μ.xi2 Q)=
      q*μ.xi1 Q+Q*q*μ.xi2 Q := by
    exact hleft2.deriv.symm.trans (hsecond.trans hright2.deriv)
  have hdet : (μ.scoreCovariance Q).det ≠ 0 :=
    (μ.scoreCovariance_det_pos hQ hnp).ne'
  have hdetEq : (μ.scoreCovariance Q).det =
      μ.xi Q*(Q*μ.xi1 Q+Q^2*μ.xi2 Q)-(Q*μ.xi1 Q)^2 := by
    simp only [Matrix.det_fin_two,FiniteMixture.scoreCovariance,
      Fin.isValue,Fin.reduceEq,ite_true,ite_false]
    ring
  let V := valueThetaDerivative μ Q q
  let R := radialThetaDerivative μ Q q
  let a := Q*μ.xi1 Q
  let c := Q*μ.xi1 Q+Q^2*μ.xi2 Q
  have hmul1 := congrArg (fun z : ℝ => q*z) hEq1
  have hmul2 := congrArg (fun z : ℝ => q*z) hEq2
  have hlin1 : (q*V)*μ.xi Q+(q*R-1)*a=0 := by
    dsimp [V,R,a]
    linear_combination hmul1 + μ.xi1 Q*hq2
  have hlin2 : (q*V)*a+(q*R-1)*c=0 := by
    dsimp [V,R,a,c]
    linear_combination hmul2 + (μ.xi1 Q+Q*μ.xi2 Q)*hq2
  have hT : q*R-1=0 := by
    have hdetzero : (q*R-1)*(μ.scoreCovariance Q).det=0 := by
      rw [hdetEq]
      dsimp [a,c] at hlin1 hlin2
      linear_combination μ.xi Q*hlin2-(Q*μ.xi1 Q)*hlin1
    exact (mul_eq_zero.mp hdetzero).resolve_right hdet
  have hR : R=1/q := by
    apply (eq_div_iff hq.ne').mpr
    linarith [hT]
  have hV : valueThetaDerivative μ Q q=0 := by
    have hxi : 0 < μ.xi Q := μ.xi_pos hQ
    have hzero : (q*V)*μ.xi Q=0 := by rw [hT] at hlin1; linarith [hlin1]
    have hqV : q*V=0 := (mul_eq_zero.mp hzero).resolve_right hxi.ne'
    change V=0
    exact (mul_eq_zero.mp hqV).resolve_left hq.ne'
  exact ⟨hV,hR⟩

private theorem sourceMixedBandExponent_k_hasDerivAt
    (μ : FiniteMixture) (β : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (e k a : ℝ) (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    HasDerivAt (fun kk => sourceMixedBandExponent μ β Q e kk a)
      (sourceRadialProfileDerivative μ Q e k+β*radialTheta μ Q a) k := by
  have hm : HasDerivAt (fun kk => sourceMixedMean μ Q e kk a)
      (radialTheta μ Q a) k := by
    unfold sourceMixedMean
    convert (hasDerivAt_const k (valueTheta μ Q a*e)).add
      ((hasDerivAt_id k).const_mul (radialTheta μ Q a)) using 1
    · funext kk
      rfl
    · ring
  have hxi : HasDerivAt (fun kk => sourceMixedXi μ β Q e kk a)
      (β*radialTheta μ Q a) k := by
    unfold sourceMixedXi
    convert (hm.const_mul β).add_const (β^2/2*sourceMixedVariance μ Q a) using 1
  have hg := (sourceRadialProfile_hasDerivAt μ hQ e k hk).add hxi
  convert hg.add_const (Real.log (1-a^2)/2) using 1
  · funext kk
    rfl
  · unfold sourceRadialProfileDerivative
    simp only [div_eq_mul_inv]

/-- The literal joint exponent has the printed mixed `(k,a)` Hessian entry
`β/√Q` at the contact latitude. -/
theorem sourceMixedBandExponent_mixed_contact
    (μ : FiniteMixture) (β : ℝ) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (e k : ℝ) (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    deriv (fun a => deriv (fun kk => sourceMixedBandExponent μ β Q e kk a) k)
      (Real.sqrt Q)=β/Real.sqrt Q := by
  have hfun : (fun a => deriv (fun kk => sourceMixedBandExponent μ β Q e kk a) k)=
      (fun a => sourceRadialProfileDerivative μ Q e k+β*radialTheta μ Q a) := by
    funext a
    exact (sourceMixedBandExponent_k_hasDerivAt μ β hQ e k a hk).deriv
  rw [hfun]
  have hder := ((radialTheta_hasDerivAt μ Q (Real.sqrt Q)).const_mul β).const_add
    (sourceRadialProfileDerivative μ Q e k)
  rw [hder.deriv,(mixed_regression_row_derivative_contact μ hQ hnp).2]
  ring

end
end SlowEquilibration.SphericalTAPMixedContactDerivatives
