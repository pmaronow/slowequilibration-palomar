-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SemicircleQuadraticTangent
public import SlowEquilibration.SphericalMarkedSchurCurvature

/-! Global complexity loss for the actual mixed source marks. The supporting
bound holds on the entire radial line, including inside the semicircle support. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open TwoAtomStationarity SphericalSequentialRegression
set_option maxHeartbeats 400000

theorem source_scoreQuadratic_precision_form (μ : FiniteMixture) (Q e k : ℝ) :
    scoreQuadratic μ Q (scorePairEquiv (e,k))=
      sourceEnergyCurvature μ Q*e^2+2*sourceEnergyRadialCross μ Q*e*k+
        sourceRadialCurvature μ Q*k^2 := by
  rw [source_scoreQuadratic_eq_slopes]
  unfold sourceEnergySlope sourceEnergyRadialCross sourceRadialSlope
  ring

theorem sourceScoreQuadratic_coercivity (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (e k : ℝ) :
    sourceMarkedLeastCurvature μ Q*(e^2+k^2) ≤ scoreQuadratic μ Q (scorePairEquiv (e,k)) := by
  have hq := sourceMarkedPrecision_quadratic_lower μ Q e k
  have hb := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hpen : 0 ≤ 1/(2*(Q^2*μ.xi2 Q))*k^2 := by positivity
  rw [source_scoreQuadratic_precision_form]
  unfold sourceModifiedRadialCurvature at hq
  nlinarith

theorem source_scoreQuadratic_joint_expansion (μ : FiniteMixture) (Q e0 k0 e k : ℝ) :
    scoreQuadratic μ Q (scorePairEquiv (e,k))=
      scoreQuadratic μ Q (scorePairEquiv (e0,k0))+
        2*sourceEnergySlope μ Q e0 k0*(e-e0)+2*sourceRadialSlope μ Q e0 k0*(k-k0)+
        sourceEnergyCurvature μ Q*(e-e0)^2+
        2*sourceEnergyRadialCross μ Q*(e-e0)*(k-k0)+sourceRadialCurvature μ Q*(k-k0)^2 := by
  rw [source_scoreQuadratic_eq_slopes,source_scoreQuadratic_eq_slopes]
  unfold sourceEnergySlope sourceEnergyRadialCross sourceRadialSlope
  ring

theorem source_semicircle_contact_global_support (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (k : ℝ) :
    SemicirclePotential.potential (k/Real.sqrt (Q^2*μ.xi2 Q)) ≤
      SemicirclePotential.potential (markK μ β Q/Real.sqrt (Q^2*μ.xi2 Q))+
        sourceRadialSlope μ Q (markE μ β x Q) (markK μ β Q)*(k-markK μ β Q)+
        (k-markK μ β Q)^2/(4*(Q^2*μ.xi2 Q)) := by
  have hb := mul_pos (sq_pos_of_pos h.overlap_range.1) (μ.xi2_pos h.overlap_range.1)
  have hs := Real.sqrt_pos.mpr hb
  have hs2 := Real.sq_sqrt hb.le
  have hm := (lt_div_iff₀ hs).mpr (sourceContact_markK_above_edge μ h)
  have hSupport := SemicirclePotential.potential_global_quadratic_tangent hm
    (k/Real.sqrt (Q^2*μ.xi2 Q))
  have hStationary := sourceContact_radial_profile_derivative_zero μ h hnp
  change -sourceRadialSlope μ Q (markE μ β x Q) (markK μ β Q)+
    SemicirclePotential.resolvent (markK μ β Q/Real.sqrt (Q^2*μ.xi2 Q))/
      Real.sqrt (Q^2*μ.xi2 Q)=0 at hStationary
  have hLin : SemicirclePotential.resolvent (markK μ β Q/Real.sqrt (Q^2*μ.xi2 Q))*
      (k/Real.sqrt (Q^2*μ.xi2 Q)-markK μ β Q/Real.sqrt (Q^2*μ.xi2 Q))=
      sourceRadialSlope μ Q (markE μ β x Q) (markK μ β Q)*(k-markK μ β Q) := by
    rw [show k/Real.sqrt (Q^2*μ.xi2 Q)-markK μ β Q/Real.sqrt (Q^2*μ.xi2 Q)=
      (k-markK μ β Q)/Real.sqrt (Q^2*μ.xi2 Q) by ring]
    rw [show SemicirclePotential.resolvent (markK μ β Q/Real.sqrt (Q^2*μ.xi2 Q))*
      ((k-markK μ β Q)/Real.sqrt (Q^2*μ.xi2 Q))=
      (SemicirclePotential.resolvent (markK μ β Q/Real.sqrt (Q^2*μ.xi2 Q))/
        Real.sqrt (Q^2*μ.xi2 Q))*(k-markK μ β Q) by ring]
    rw [show SemicirclePotential.resolvent (markK μ β Q/Real.sqrt (Q^2*μ.xi2 Q))/
      Real.sqrt (Q^2*μ.xi2 Q)=sourceRadialSlope μ Q (markE μ β x Q) (markK μ β Q)
      by linarith]
  have hQuad : (k/Real.sqrt (Q^2*μ.xi2 Q)-markK μ β Q/Real.sqrt (Q^2*μ.xi2 Q))^2/4=
      (k-markK μ β Q)^2/(4*(Q^2*μ.xi2 Q)) := by
    rw [←sub_div,div_pow,hs2]
    ring
  rw [hLin,hQuad] at hSupport
  exact hSupport

/-- The actual complexity lies below its contact plane minus the full
modified-precision quadratic form, with no radial restriction. -/
theorem sourceMarkedComplexity_global_precision_loss (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (e k : ℝ) :
    sourceRadialProfile μ Q e k ≤ -(β*x)*(e-markE μ β x Q)-
      (sourceEnergyCurvature μ Q*(e-markE μ β x Q)^2+
        2*sourceEnergyRadialCross μ Q*(e-markE μ β x Q)*(k-markK μ β Q)+
        sourceModifiedRadialCurvature μ Q*(k-markK μ β Q)^2)/2 := by
  have hPot := source_semicircle_contact_global_support μ h hnp k
  rw [show (k-markK μ β Q)^2/(4*(Q^2*μ.xi2 Q))=
    (1/(2*(Q^2*μ.xi2 Q)))*(k-markK μ β Q)^2/2 by ring] at hPot
  have hZero := sourceContact_markedComplexity_zero μ h hnp
  have hExp := source_scoreQuadratic_joint_expansion μ Q (markE μ β x Q) (markK μ β Q) e k
  rw [sourceEnergySlope_at_contact μ h hnp] at hExp
  change 1/2+Real.log ((Q^2*μ.xi2 Q)/(Q*μ.xi1 Q))/2-
    scoreQuadratic μ Q (scorePairEquiv (markE μ β x Q,markK μ β Q))/2+
    SemicirclePotential.potential (markK μ β Q/Real.sqrt (Q^2*μ.xi2 Q))=0 at hZero
  change 1/2+Real.log ((Q^2*μ.xi2 Q)/(Q*μ.xi1 Q))/2-
    scoreQuadratic μ Q (scorePairEquiv (e,k))/2+
    SemicirclePotential.potential (k/Real.sqrt (Q^2*μ.xi2 Q)) ≤ _
  rw [hExp]
  unfold sourceModifiedRadialCurvature
  nlinarith [hPot,hZero]

/-- The manuscript's global loss, using the genuine smallest eigenvalue
of its literal modified score precision. -/
theorem sourceMarkedComplexity_global_loss (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (e k : ℝ) :
    sourceRadialProfile μ Q e k ≤ -(β*x)*(e-markE μ β x Q)-
      sourceMarkedLeastCurvature μ Q*((e-markE μ β x Q)^2+(k-markK μ β Q)^2)/2 := by
  have hp := sourceMarkedComplexity_global_precision_loss μ h hnp e k
  have hq := sourceMarkedPrecision_quadratic_lower μ Q (e-markE μ β x Q) (k-markK μ β Q)
  linarith

def sourceMarkedCoercivityConstant (μ : FiniteMixture) (β x Q : ℝ) : ℝ :=
  (β*x)^2/sourceMarkedLeastCurvature μ Q+
    sourceMarkedLeastCurvature μ Q/4*((markE μ β x Q)^2+(markK μ β Q)^2)+1

theorem sourceMarkedCoercivityConstant_pos (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    0 < sourceMarkedCoercivityConstant μ β x Q := by
  have hp := sourceMarkedLeastCurvature_pos μ h.overlap_range.1 (by have hd := h.min_degree; omega) hnp
  unfold sourceMarkedCoercivityConstant
  positivity

/-- The true contact bound supplies a global Gaussian coercivity constant,
chosen before every marked window and every dimension. -/
theorem sourceMarkedComplexity_global_coercivity (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (e k : ℝ) :
    sourceRadialProfile μ Q e k ≤ sourceMarkedCoercivityConstant μ β x Q-
      sourceMarkedLeastCurvature μ Q/8*(e^2+k^2) := by
  let κ := sourceMarkedLeastCurvature μ Q
  let E0 := markE μ β x Q
  let K0 := markK μ β Q
  have hp : 0 < κ := sourceMarkedLeastCurvature_pos μ h.overlap_range.1 (by have hd := h.min_degree; omega) hnp
  have hLoss := sourceMarkedComplexity_global_loss μ h hnp e k
  have hYoungEq : κ/4*(e-E0+2*(β*x)/κ)^2=
      κ/4*(e-E0)^2+(β*x)*(e-E0)+(β*x)^2/κ := by field_simp [hp.ne']; ring
  have hYoung : 0 ≤ κ/4*(e-E0)^2+(β*x)*(e-E0)+(β*x)^2/κ := by
    rw [←hYoungEq]
    positivity
  have hShiftE : e^2/2-E0^2 ≤ (e-E0)^2 := by nlinarith [sq_nonneg (e-2*E0)]
  have hShiftK : k^2/2-K0^2 ≤ (k-K0)^2 := by nlinarith [sq_nonneg (k-2*K0)]
  have hSE := mul_le_mul_of_nonneg_left hShiftE (show 0 ≤ κ/4 by positivity)
  have hSK := mul_le_mul_of_nonneg_left hShiftK (show 0 ≤ κ/4 by positivity)
  change sourceRadialProfile μ Q e k ≤ (β*x)^2/κ+κ/4*(E0^2+K0^2)+1-κ/8*(e^2+k^2)
  change sourceRadialProfile μ Q e k ≤ -(β*x)*(e-E0)-κ*((e-E0)^2+(k-K0)^2)/2 at hLoss
  nlinarith [mul_nonneg hp.le (sq_nonneg (k-K0))]

/-- A source-admissible excluded radial mark has a uniform actual negative
complexity at every energy above the source lower threshold. -/
theorem sourceMarkedComplexity_excluded_radial_loss (μ : FiniteMixture) {β x Q δ u : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hA3 : δ ≤ sourceMarkedLeastCurvature μ Q*u^2/(8*(β*x)))
    {e k : ℝ} (he : markE μ β x Q-δ ≤ e) (hk : u ≤ |k-markK μ β Q|) (hu : 0 ≤ u) :
    sourceRadialProfile μ Q e k ≤ -3*sourceMarkedLeastCurvature μ Q*u^2/8 := by
  have hc := mul_pos h.beta_pos h.weight_range.1
  have hp := sourceMarkedLeastCurvature_pos μ h.overlap_range.1 (by have hd := h.min_degree; omega) hnp
  have hLoss := sourceMarkedComplexity_global_loss μ h hnp e k
  have hδ : (β*x)*δ ≤ sourceMarkedLeastCurvature μ Q*u^2/8 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8) hc)).mp hA3
    nlinarith
  have hk2 : u^2 ≤ (k-markK μ β Q)^2 := by
    nlinarith [sq_abs (k-markK μ β Q),abs_nonneg (k-markK μ β Q)]
  have hEnergy : -(β*x)*(e-markE μ β x Q) ≤ (β*x)*δ := by
    nlinarith [mul_nonneg hc.le (sub_nonneg.mpr he)]
  nlinarith [mul_nonneg hp.le (sq_nonneg (e-markE μ β x Q)),
    mul_nonneg hp.le (sub_nonneg.mpr hk2)]

end SlowEquilibration.SphericalMarkedWindows
