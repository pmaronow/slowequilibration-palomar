-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LatitudeGroundTrialCalculus
public import SlowEquilibration.SphericalCriticalLatitudeSourceTau
public import SlowEquilibration.MixtureCurvature

/-! The actual conditioned latitude covariance and the literal manuscript
trial. No trial value or gap estimate is included in the hypotheses. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.LatitudeGroundTrial
open MeasureTheory Set SphericalParisiConditionedLatitudeCovariance
set_option maxHeartbeats 600000

def centeredCovariance (μ : FiniteMixture) (Q r t : ℝ) : ℝ :=
  sourceTau μ Q r t-sourceTau μ Q r 0

def centeredFirst (μ : FiniteMixture) (Q r t : ℝ) : ℝ :=
  (1-r^2)*(centerFirst μ Q (r^2+(1-r^2)*t)-(centerFirst μ Q r)^2/gradientVariance μ Q)

def centeredSecond (μ : FiniteMixture) (Q r t : ℝ) : ℝ :=
  (1-r^2)^2*Q^2*μ.xi2 (Q*(r^2+(1-r^2)*t))

def D (z r : ℝ) : ℝ := 1+(1-r)*z
def location (r : ℝ) : ℝ := r/(1+r)
def height (y z r : ℝ) : ℝ := D z r/((1-r^2)*y)

def slack (μ : FiniteMixture) (Q z r : ℝ) : ℝ :=
  μ.xi Q-centerCovariance μ Q r-
    gradientVariance μ Q*((1+z)/z^2*Real.log (D z r)-(1-r)/z)

theorem centered_hasDerivAt (μ : FiniteMixture) (Q r t : ℝ) :
    HasDerivAt (centeredCovariance μ Q r) (centeredFirst μ Q r t) t := by
  have ha := (((hasDerivAt_id t).const_mul (1-r^2)).const_add (r^2)).const_mul Q
  have hh := (((μ.hasDerivAt_xi (Q*(r^2+(1-r^2)*t))).comp t ha).sub_const
    (sourceScoreCorrection μ Q r)).sub
      ((hasDerivAt_id t).const_mul ((1-r^2)*(centerFirst μ Q r)^2/gradientVariance μ Q))
  convert hh.sub_const (sourceTau μ Q r 0) using 1
  · rfl
  · unfold centeredFirst centerFirst
    ring

theorem centeredFirst_hasDerivAt (μ : FiniteMixture) (Q r t : ℝ) :
    HasDerivAt (centeredFirst μ Q r) (centeredSecond μ Q r t) t := by
  have ha := (((hasDerivAt_id t).const_mul (1-r^2)).const_add (r^2)).const_mul Q
  have hh := ((((μ.hasDerivAt_xi1 (Q*(r^2+(1-r^2)*t))).comp t ha).const_mul Q).sub_const
    ((centerFirst μ Q r)^2/gradientVariance μ Q)).const_mul (1-r^2)
  convert hh using 1
  · rfl
  · unfold centeredSecond
    ring

theorem centeredSecond_continuous (μ : FiniteMixture) (Q r : ℝ) :
    Continuous (centeredSecond μ Q r) := by
  have hc : Continuous μ.xi2 := continuous_iff_continuousAt.mpr
    (fun t => (μ.hasDerivAt_xi2 t).continuousAt)
  exact continuous_const.mul (hc.comp
    (continuous_const.mul (continuous_const.add (continuous_const.mul continuous_id))))

theorem trial_endpoint {y z r : ℝ} (hy : 0 < y) (_hz : 0 < z)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    location r ∈ Icc (0 : ℝ) 1 ∧
      height y z r-(z/y)*(1-location r)=((1-r^2)*y)⁻¹ ∧
      0 < height y z r-(z/y)*(1-location r) := by
  have hden : 0 < 1+r := by linarith [hr.1]
  have hs : location r ∈ Icc (0 : ℝ) 1 := by
    unfold location
    exact ⟨div_nonneg hr.1.le hden.le, (div_le_one hden).mpr (by linarith)⟩
  have hS : 0 < 1-r^2 := by nlinarith [hr.1,hr.2]
  have he : height y z r-(z/y)*(1-location r)=((1-r^2)*y)⁻¹ := by
    unfold height location D
    field_simp [hy.ne',hden.ne',hS.ne']
    ring
  refine ⟨hs,he,?_⟩
  rw [he]
  exact inv_pos.mpr (mul_pos hS hy)

theorem source_trial_evaluation (μ : FiniteMixture) (Q : ℝ) {y z r : ℝ}
    (hy : 0 < y) (hz : 0 < z) (hr : r ∈ Ioo (0 : ℝ) 1)
    (ha : 0 < gradientVariance μ Q) :
    functional (centeredFirst μ Q r) (centeredSecond μ Q r)
      (height y z r) (z/y) (location r)=
    ((gradientVariance μ Q ^ 2+z*gradientVariance μ Q*(μ.xi Q-centerCovariance μ Q r)-
       D z r*(centerFirst μ Q r)^2)/(y*gradientVariance μ Q)+
       r*(1-r)*y/D z r+y/z*Real.log (D z r))/2 := by
  obtain ⟨hs,he,hb⟩ := trial_endpoint hy hz hr
  have hS : 0 < 1-r^2 := by nlinarith [hr.1,hr.2]
  have hD : 0 < D z r := by
    have hr1 : 0 < 1-r := sub_pos.mpr hr.2
    unfold D
    positivity
  have hden : 0 < 1+r := by linarith [hr.1]
  rw [functional_eq (centeredCovariance μ Q r) (centeredFirst μ Q r)
    (centeredSecond μ Q r) (centered_hasDerivAt μ Q r)
    (centeredFirst_hasDerivAt μ Q r) (centeredSecond_continuous μ Q r)
    (div_pos hz hy) hs hb, he]
  have heq : r^2+(1-r^2)*location r=r := by
    unfold location
    field_simp [hden.ne']
    ring
  have hlog : height y z r/((1-r^2)*y)⁻¹=D z r := by
    unfold height
    field_simp [hS.ne',hy.ne']
  rw [hlog]
  unfold centeredCovariance centeredFirst sourceTau
  rw [heq, show r^2+(1-r^2)*(1 : ℝ)=1 by ring]
  have ha' : Q*μ.xi1 Q ≠ 0 := by
    simpa only [gradientVariance,centerFirst,mul_one] using ha.ne'
  have hQne := (mul_ne_zero_iff.mp ha').1
  have hξne := (mul_ne_zero_iff.mp ha').2
  have hDne : 1+z-z*r ≠ 0 := by
    convert hD.ne' using 1
    unfold D
    ring
  unfold location height centerCovariance gradientVariance centerFirst D
  simp only [mul_one, mul_zero, add_zero]
  field_simp [ha',hQne,hξne,hy.ne',hz.ne',hS.ne',hD.ne',hDne,hden.ne']
  ring

theorem completed_square (μ : FiniteMixture) (Q : ℝ) {y z r : ℝ}
    (hy : 0 < y) (hz : 0 < z) (hr : r ∈ Ioo (0 : ℝ) 1)
    (ha : 0 < gradientVariance μ Q) (hscale : y^2=(1+z)*gradientVariance μ Q) :
    (r*centerFirst μ Q r+z*centerCovariance μ Q r)/y+
      functional (centeredFirst μ Q r) (centeredSecond μ Q r)
        (height y z r) (z/y) (location r)=
      (gradientVariance μ Q+z*μ.xi Q)/y-z/(2*y)*slack μ Q z r-
        (r*gradientVariance μ Q-D z r*centerFirst μ Q r)^2/
          (2*y*gradientVariance μ Q*D z r) := by
  rw [source_trial_evaluation μ Q hy hz hr ha]
  have hD : 0 < D z r := by
    have hr1 : 0 < 1-r := sub_pos.mpr hr.2
    unfold D
    positivity
  have hz1 : 0 < 1+z := by linarith
  have hea : gradientVariance μ Q=y^2/(1+z) := by
    apply (eq_div_iff hz1.ne').mpr
    nlinarith [hscale]
  unfold slack
  rw [hea]
  field_simp [hy.ne',hz.ne',hz1.ne',hD.ne']
  unfold D
  ring

end SlowEquilibration.LatitudeGroundTrial
