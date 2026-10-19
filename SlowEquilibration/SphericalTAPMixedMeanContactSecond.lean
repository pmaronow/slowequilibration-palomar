-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedCrossSecond
public import SlowEquilibration.SphericalCriticalLatitudeContactMean

@[expose] public section

/-! The literal mixed regression mean has the printed contact-mark profile
and second latitude derivative. -/

namespace SlowEquilibration.SphericalTAPMixedMeanContactSecond
noncomputable section
open Set SphericalMarkedWindows SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPMixedBandExponent SphericalTAPMixedCrossSecond
open scoped Matrix
set_option autoImplicit false

theorem sourceMixedMean_eq_scoreSlopes (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (e k a : ℝ) :
    sourceMixedMean μ Q e k a =
      μ.xi (Real.sqrt Q*a)*sourceEnergySlope μ Q e k+
        (Real.sqrt Q*a*μ.xi1 (Real.sqrt Q*a))*sourceRadialSlope μ Q e k := by
  have hs : (μ.scoreCovariance Q).IsSymm := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hp := hs.inv.apply 1 0
  rw [sourceMixedMean_eq_score_inverse μ hQ hnp]
  simp only [sourceMixedCross,scorePairEquiv_apply,dotProduct,
    Matrix.mulVec,Fin.sum_univ_two]
  change μ.xi (Real.sqrt Q*a)*
      (((μ.scoreCovariance Q)⁻¹) 0 0*e+((μ.scoreCovariance Q)⁻¹) 0 1*k)+
    (Real.sqrt Q*a*μ.xi1 (Real.sqrt Q*a))*
      (((μ.scoreCovariance Q)⁻¹) 1 0*e+((μ.scoreCovariance Q)⁻¹) 1 1*k)=_
  unfold sourceEnergySlope sourceRadialSlope sourceEnergyCurvature sourceRadialCurvature
  rw [hp]
  ring

/-- At certified contact marks the actual source conditional mean has the
closed profile `(b₁(a)+z b₀(a))/y`. -/
theorem sourceMixedMean_contact_marks (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (a : ℝ) :
    sourceMixedMean μ Q (markE μ β x Q) (markK μ β Q) a =
      (Real.sqrt Q*a*μ.xi1 (Real.sqrt Q*a)+
        markZ x Q*μ.xi (Real.sqrt Q*a))/markY β Q := by
  rw [sourceMixedMean_eq_scoreSlopes μ h.overlap_range.1 hnp,
    sourceEnergySlope_at_contact μ h hnp,
    sourceRadialSlope_at_contact μ h hnp,
    ← markZ_div_markY h.beta_pos h.overlap_range]
  ring

/-- Second latitude derivative of the true contact regression mean. -/
theorem sourceMixedMean_second_contact_marks (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    deriv (deriv (sourceMixedMean μ Q (markE μ β x Q) (markK μ β Q)))
      (Real.sqrt Q) =
      ((2*Q*μ.xi2 Q+Q^2*μ.v1 Q)+
        markZ x Q*(Q*μ.xi2 Q))/markY β Q := by
  let z := markZ x Q
  let y := markY β Q
  let f0 : ℝ → ℝ := fun a => μ.xi (Real.sqrt Q*a)
  let f1 : ℝ → ℝ := fun a => Real.sqrt Q*a*μ.xi1 (Real.sqrt Q*a)
  have hf : sourceMixedMean μ Q (markE μ β x Q) (markK μ β Q) =
      fun a => (f1 a+z*f0 a)/y :=
    funext (sourceMixedMean_contact_marks μ h hnp)
  rw [hf]
  have h0 (a : ℝ) : DifferentiableAt ℝ f0 a := by
    dsimp [f0]
    exact (μ.hasDerivAt_xi (Real.sqrt Q*a)).comp a
      ((hasDerivAt_id a).const_mul (Real.sqrt Q)) |>.differentiableAt
  have h1 (a : ℝ) : DifferentiableAt ℝ f1 a := by
    dsimp [f1]
    unfold FiniteMixture.xi1
    fun_prop
  have hfun : deriv (fun a => (f1 a+z*f0 a)/y) =
      (fun a => (deriv f1 a+z*deriv f0 a)/y) := by
    funext a
    convert ((h1 a).hasDerivAt.add ((h0 a).hasDerivAt.const_mul z)).div_const y |>.deriv using 1
  rw [hfun]
  have h0' (a : ℝ) : DifferentiableAt ℝ (deriv f0) a := by
    rw [show deriv f0 = fun t => Real.sqrt Q*μ.xi1 (Real.sqrt Q*t) from
      funext (cross_value_first μ Q)]
    unfold FiniteMixture.xi1
    fun_prop
  have h1' (a : ℝ) : DifferentiableAt ℝ (deriv f1) a := by
    rw [show deriv f1 = fun t => Real.sqrt Q*μ.xi1 (Real.sqrt Q*t)+
      Q*t*μ.xi2 (Real.sqrt Q*t) from
      funext (cross_radial_first μ h.overlap_range.1.le)]
    unfold FiniteMixture.xi1 FiniteMixture.xi2
    fun_prop
  have hh := (((h1' (Real.sqrt Q)).hasDerivAt).add
    (((h0' (Real.sqrt Q)).hasDerivAt).const_mul z)).div_const y
  have he : deriv (fun a => (deriv f1 a+z*deriv f0 a)/y) (Real.sqrt Q)=
      (deriv (deriv f1) (Real.sqrt Q)+
        z*deriv (deriv f0) (Real.sqrt Q))/y := by
    convert hh.deriv using 1
  rw [he]
  rw [cross_radial_second μ h.overlap_range.1.le,
    cross_value_second μ h.overlap_range.1.le,
    Real.mul_self_sqrt h.overlap_range.1.le]
  dsimp [z,y]
  ring_nf
  rw [Real.sq_sqrt h.overlap_range.1.le]
  ring

end
end SlowEquilibration.SphericalTAPMixedMeanContactSecond
