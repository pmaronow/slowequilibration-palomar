-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMarkedRadialSaddle
public import SlowEquilibration.SemicircleModifiedConcavity

/-! Genuine scalar coefficients of the actual mixed exterior saddle
equation, derived from the original finite-mixture score covariance. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set SphericalSequentialRegression
set_option maxHeartbeats 400000

def sourceSaddleParameter (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  2*(Q^2*μ.xi2 Q)*sourceModifiedRadialCurvature μ Q

def sourceSaddleEnergyCoefficient (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  -2*(Q^2*μ.xi2 Q)*sourceEnergyRadialCross μ Q

theorem sourceEnergyRadial_gt_value_variance (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) :
    μ.xi Q < Q*μ.xi1 Q := by
  rw [μ.score_first_moment]
  unfold FiniteMixture.xi
  apply Finset.sum_lt_sum
  · intro p hp
    have hweight : 0 < μ.coeff p*Q^p := mul_pos (μ.coeff_pos hp) (pow_pos hQ _)
    have hp2 := μ.degree_ge_two hp
    have hdegree : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (show 1 < p by omega)
    nlinarith
  · obtain ⟨p,hp⟩ := μ.support_nonempty
    refine ⟨p,hp,?_⟩
    have hweight : 0 < μ.coeff p*Q^p := mul_pos (μ.coeff_pos hp) (pow_pos hQ _)
    have hp2 := μ.degree_ge_two hp
    have hdegree : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (show 1 < p by omega)
    nlinarith

private theorem saddle_parameter_algebra {V a b D : ℝ} (hb : 0 < b) (hD : 0 < D)
    (ha : 0 < a) (hav : V < a) (hdet : D=V*(a+b)-a^2) :
    1 < 2*b*(V/D-1/(2*b)) := by
  have heq : 2*b*(V/D-1/(2*b))=2*b*V/D-1 := by field_simp [hb.ne',hD.ne']
  rw [heq]
  have hBD : D < b*V := by nlinarith [mul_pos ha (sub_pos.mpr hav)]
  have hh : 2 < 2*b*V/D := (lt_div_iff₀ hD).mpr (by nlinarith)
  linarith

theorem sourceSaddleParameter_gt_one (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) : 1 < sourceSaddleParameter μ Q := by
  unfold sourceSaddleParameter sourceModifiedRadialCurvature
  rw [sourceRadialCurvature_eq]
  exact saddle_parameter_algebra (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ))
    (μ.scoreCovariance_det_pos hQ hnp) (mul_pos hQ (μ.xi1_pos hQ))
    (sourceEnergyRadial_gt_value_variance μ hQ) (sourceScoreCovariance_det_eq μ Q)

theorem sourceSaddleEnergyCoefficient_pos (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) : 0 < sourceSaddleEnergyCoefficient μ Q := by
  have hb := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hB := sourceEnergyRadialCross_neg μ hQ hnp
  unfold sourceSaddleEnergyCoefficient
  rw [show -2*(Q^2*μ.xi2 Q)*sourceEnergyRadialCross μ Q=
    2*(Q^2*μ.xi2 Q)*(-sourceEnergyRadialCross μ Q) by ring]
  exact mul_pos (mul_pos (by norm_num) hb) (neg_pos.mpr hB)

/-- The genuine scalar radial derivative is exactly the unsquared exterior
saddle equation. All coefficient and square-root normalizations are literal. -/
theorem sourceRadialProfileDerivative_root_eq (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (e k : ℝ) (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    sourceRadialProfileDerivative μ Q e k=
      (sourceSaddleEnergyCoefficient μ Q*e-sourceSaddleParameter μ Q*k-
        Real.sqrt (k^2-4*(Q^2*μ.xi2 Q)))/(2*(Q^2*μ.xi2 Q)) := by
  let b := Q^2*μ.xi2 Q
  let s := Real.sqrt b
  have hb : 0 < b := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hs : 0 < s := Real.sqrt_pos.mpr hb
  have hs2 : s^2=b := Real.sq_sqrt hb.le
  have hz : 2 < k/s := (lt_div_iff₀ hs).mpr hk
  have hdisc : 0 < k^2-4*b := by
    have hkpos : 0 < k := lt_trans (by positivity) hk
    nlinarith
  have hscale : (k/s)^2-4=(k^2-4*b)/b := by rw [div_pow,hs2]; field_simp [hb.ne']
  have hR : SemicirclePotential.resolvent (k/s)/s=(k-Real.sqrt (k^2-4*b))/(2*b) := by
    rw [SemicirclePotential.resolvent_explicit_root hz,hscale,Real.sqrt_div hdisc.le]
    change ((k/s-Real.sqrt (k^2-4*b)/s)/2)/s=(k-Real.sqrt (k^2-4*b))/(2*b)
    calc
      _=(k-Real.sqrt (k^2-4*b))/(2*s^2) := by ring
      _=_ := by rw [hs2]
  change -sourceRadialSlope μ Q e k+SemicirclePotential.resolvent (k/s)/s=_
  rw [hR]
  unfold sourceRadialSlope sourceSaddleEnergyCoefficient sourceSaddleParameter sourceModifiedRadialCurvature
  change -(sourceEnergyRadialCross μ Q*e+sourceRadialCurvature μ Q*k)+
    (k-Real.sqrt (k^2-4*b))/(2*b)=_
  dsimp [b]
  field_simp [(μ.xi2_pos hQ).ne',hQ.ne']
  ring

end SlowEquilibration.SphericalMarkedWindows
