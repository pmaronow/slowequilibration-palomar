-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedActualLatitudeHessian

@[expose] public section

/-! The literal mixed Laplace exponent is stationary in latitude at the
certified physical contact mark. -/

namespace SlowEquilibration.SphericalTAPMixedActualLatitudeStationarity
noncomputable section
open Set SphericalMarkedWindows SphericalTAPCertificate TwoAtomStationarity
open ConditionedEntrance SphericalTAPMixedBandExponent
open SphericalTAPMixedScoreSecond SphericalTAPMixedGradientSecond
open SphericalTAPMixedContactDerivatives
set_option autoImplicit false

theorem sourceMixedMean_first_contact (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (e k : ℝ) :
    deriv (sourceMixedMean μ Q e k) (Real.sqrt Q) =
      k/Real.sqrt Q := by
  let q := Real.sqrt Q
  have hh := ((valueTheta_hasDerivAt μ Q q).mul_const e).add
    ((radialTheta_hasDerivAt μ Q q).mul_const k)
  change HasDerivAt (sourceMixedMean μ Q e k) _ q at hh
  rw [hh.deriv]
  obtain ⟨hv,hr⟩ := mixed_regression_row_derivative_contact μ hQ hnp
  rw [hv,hr]
  ring

theorem sourceMixedVariance_first_contact (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) :
    deriv (sourceMixedVariance μ Q) (Real.sqrt Q) =
      -2*(1-Q)*Real.sqrt Q*μ.xi2 Q := by
  let q := Real.sqrt Q
  have hq : q*q=Q := Real.mul_self_sqrt hQ.le
  have hv : valueTheta μ Q q=1 := by
    have hh := sourceMixedMean_contact μ hQ hnp 1 0
    simpa [sourceMixedMean,q] using hh
  have hr : radialTheta μ Q q=0 := by
    have hh := sourceMixedMean_contact μ hQ hnp 0 1
    simpa [sourceMixedMean,q] using hh
  have hscore : DifferentiableAt ℝ (sourceMixedScoreReduction μ Q) q := by
    unfold sourceMixedScoreReduction sourceMixedCross
    simp only [scorePairEquiv_apply, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    unfold valueTheta radialTheta monomialSum FiniteMixture.xi FiniteMixture.xi1
    fun_prop
  have hgrad : DifferentiableAt ℝ (sourceMixedGradientReduction μ Q) q := by
    unfold sourceMixedGradientReduction FiniteMixture.xi1
    fun_prop
  have hmain := (((hasDerivAt_const q (μ.xi 1)).sub hscore.hasDerivAt).sub
    hgrad.hasDerivAt)
  change HasDerivAt (sourceMixedVariance μ Q) _ q at hmain
  rw [hmain.deriv, sourceMixedScoreReduction_first μ hQ.le,
    sourceMixedGradientReduction_first μ Q]
  rw [hv,hr,hq]
  have hxi : μ.xi1 Q ≠ 0 := (μ.xi1_pos hQ).ne'
  field_simp
  rw [show q^2=Q from Real.sq_sqrt hQ.le]
  ring

private theorem sourceMixedBandExponent_first_contact_raw
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree) :
    deriv (sourceMixedBandExponent μ β Q (markE μ β x Q) (markK μ β Q))
      (Real.sqrt Q) =
      β*markK μ β Q/Real.sqrt Q-
        β^2*(1-Q)*Real.sqrt Q*μ.xi2 Q-
        Real.sqrt Q/(1-Q) := by
  let q := Real.sqrt Q
  have hq : q^2=Q := Real.sq_sqrt h.overlap_range.1.le
  have hden : 1-q^2 ≠ 0 := by rw [hq]; exact ne_of_gt (sub_pos.mpr h.overlap_range.2)
  have hfac : HasDerivAt (fun t : ℝ => 1-t^2) (-2*q) q := by
    convert (hasDerivAt_const q 1).sub ((hasDerivAt_id q).pow 2) using 1
    · funext t
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq]
      ring
  have hlog : HasDerivAt (fun t : ℝ => Real.log (1-t^2)/2)
      (-q/(1-q^2)) q := by
    have hpos : 0 < 1-q^2 := by rw [hq]; linarith [h.overlap_range.2]
    convert (hfac.log hpos.ne').div_const 2 using 1
    ring
  have hm : DifferentiableAt ℝ
      (sourceMixedMean μ Q (markE μ β x Q) (markK μ β Q)) q :=
    (SphericalTAPMixedLatitudeSmooth.sourceMixedMean_smooth μ Q
      (markE μ β x Q) (markK μ β Q)).differentiable (by simp) q
  have hv : DifferentiableAt ℝ (sourceMixedVariance μ Q) q :=
    (SphericalTAPMixedLatitudeSmooth.sourceMixedVariance_smooth μ Q).differentiable
      (by simp) q
  have hh := ((hasDerivAt_const q
      (sourceRadialProfile μ Q (markE μ β x Q) (markK μ β Q))).add
      (((hm.hasDerivAt).const_mul β).add
        ((hv.hasDerivAt).const_mul (β^2/2)))).add hlog
  change HasDerivAt
    (sourceMixedBandExponent μ β Q (markE μ β x Q) (markK μ β Q)) _ q at hh
  rw [hh.deriv, sourceMixedMean_first_contact μ h.overlap_range.1 hnp,
    sourceMixedVariance_first_contact μ h.overlap_range.1 hnp, hq]
  ring

/-- Actual latitude stationarity `∂ₐg(E₀,K₀,√Q)=0` from the contact score
and certificate scale relation. -/
theorem sourceMixedBandExponent_latitude_deriv_contact
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree) :
    deriv (sourceMixedBandExponent μ β Q (markE μ β x Q) (markK μ β Q))
      (Real.sqrt Q) = 0 := by
  rw [sourceMixedBandExponent_first_contact_raw μ h hnp]
  have hβ0 : β ≠ 0 := h.beta_pos.ne'
  have hQ0 : Q ≠ 0 := h.overlap_range.1.ne'
  have hs0 : 1-Q ≠ 0 := ne_of_gt (sub_pos.mpr h.overlap_range.2)
  have hq0 : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.mpr h.overlap_range.1).ne'
  unfold markK markY markB
  field_simp [hβ0,hQ0,hs0,hq0]
  rw [Real.sq_sqrt h.overlap_range.1.le]
  ring

end
end SlowEquilibration.SphericalTAPMixedActualLatitudeStationarity
