-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LatitudeGroundTrialContact
public import SlowEquilibration.SphericalCriticalLatitudeContactMean

/-! The printed positive minimum gap and the literal critical latitude
ground-mark trial inequality. Compactness is applied to the actual source
slack proved from the strict one-step certificate. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.LatitudeGroundTrial
open Set TwoAtomStationarity SphericalTAPCertificate
open SphericalParisiConditionedLatitudeCovariance
set_option maxHeartbeats 600000

def gap (μ : FiniteMixture) (Q y z ε η : ℝ) : ℝ :=
  z/(2*y)*sInf (slack μ Q z '' Icc ε (1-η))

theorem slack_continuousOn (μ : FiniteMixture) (Q : ℝ) {z ε η : ℝ}
    (hz : 0 < z) (hη : 0 < η) :
    ContinuousOn (slack μ Q z) (Icc ε (1-η)) := by
  have hlog : ContinuousOn (fun r => Real.log (D z r)) (Icc ε (1-η)) := by
    apply ContinuousOn.log
    · unfold D
      fun_prop
    · intro r hr
      have hr1 : 0 < 1-r := by linarith [hr.2]
      have hD : 0 < D z r := by unfold D; positivity
      exact hD.ne'
  have hξ : Continuous μ.xi := continuous_iff_continuousAt.mpr
    (fun r => (μ.hasDerivAt_xi r).continuousAt)
  unfold slack centerCovariance
  exact (continuousOn_const.sub ((hξ.comp (continuous_const.mul continuous_id)).continuousOn)).sub
    (continuousOn_const.mul ((continuousOn_const.mul hlog).sub
      ((continuous_const.sub continuous_id).continuousOn.div_const z)))

theorem gap_positive (μ : FiniteMixture) {β x Q ε η : ℝ}
    (h : Certificate μ β x Q) (hε : 0 < ε) (hη : 0 < η) (hεη : ε < 1-η) :
    0 < gap μ Q (markY β Q) (markZ x Q) ε η ∧
      ∀ r ∈ Icc ε (1-η), gap μ Q (markY β Q) (markZ x Q) ε η ≤
        markZ x Q/(2*markY β Q)*slack μ Q (markZ x Q) r := by
  have hy := markY_pos h.beta_pos h.overlap_range
  have hz : 0 < markZ x Q := div_pos
    (mul_pos h.weight_range.1 h.overlap_range.1) (sub_pos.mpr h.overlap_range.2)
  obtain ⟨r₀,hr₀,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc ε (1-η)).Nonempty from ⟨ε,le_rfl,hεη.le⟩)
    (slack_continuousOn μ Q hz hη)
  have hleast : IsLeast (slack μ Q (markZ x Q) '' Icc ε (1-η))
      (slack μ Q (markZ x Q) r₀) := by
    refine ⟨⟨r₀,hr₀,rfl⟩,?_⟩
    rintro v ⟨r,hr,rfl⟩
    exact hmin hr
  have he := hleast.csInf_eq
  have hr₀' : r₀ ∈ Ioo (0 : ℝ) 1 := ⟨hε.trans_le hr₀.1,by linarith [hr₀.2]⟩
  have hc : 0 < markZ x Q/(2*markY β Q) := div_pos hz (by positivity)
  constructor
  · unfold gap
    rw [he]
    exact mul_pos hc (slack_positive μ h hr₀')
  · intro r hr
    unfold gap
    rw [he]
    exact mul_le_mul_of_nonneg_left (hmin hr) hc.le

/-- Both source10.12(c) and10.12(d), for the literal actual mixed critical
latitude covariance and actual conditional mean at certified ground marks. -/
theorem source_trial_gap (μ : FiniteMixture) {β x Q ε η : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hε : 0 < ε) (hη : 0 < η) (hεη : ε < 1-η) :
    0 < gap μ Q (markY β Q) (markZ x Q) ε η ∧
      ∀ r ∈ Icc ε (1-η),
        sourceConditionalMean μ Q (markE μ β x Q) (markK μ β Q) r+
          functional (centeredFirst μ Q r) (centeredSecond μ Q r)
            (height (markY β Q) (markZ x Q) r) (markZ x Q/markY β Q) (location r) ≤
          markE μ β x Q-gap μ Q (markY β Q) (markZ x Q) ε η := by
  obtain ⟨hgap,hbound⟩ := gap_positive μ h hε hη hεη
  refine ⟨hgap,?_⟩
  intro r hr
  have hr' : r ∈ Ioo (0 : ℝ) 1 := ⟨hε.trans_le hr.1,by linarith [hr.2]⟩
  have hy := markY_pos h.beta_pos h.overlap_range
  have hz : 0 < markZ x Q := div_pos
    (mul_pos h.weight_range.1 h.overlap_range.1) (sub_pos.mpr h.overlap_range.2)
  have ha : 0 < gradientVariance μ Q := by
    change 0 < Q*μ.xi1 (Q*1)
    rw [mul_one]
    exact mul_pos h.overlap_range.1 (μ.xi1_pos h.overlap_range.1)
  have hscale : (markY β Q)^2=(1+markZ x Q)*gradientVariance μ Q := by
    simpa only [gradientVariance,centerFirst,mul_one,markA] using
      markY_sq_from_contact μ h.beta_pos h.weight_range h.overlap_range
        h.contact_value h.contact_derivative
  rw [SphericalCriticalLatitude.sourceConditionalMean_at_contact μ h hnp r]
  have he := completed_square μ Q hy hz hr' ha hscale
  have hE : (gradientVariance μ Q+markZ x Q*μ.xi Q)/markY β Q=markE μ β x Q := by
    simp only [gradientVariance,centerFirst,mul_one,markE,markA]
  rw [hE] at he
  rw [he]
  have hD : 0 < D (markZ x Q) r := by
    have hr1 : 0 < 1-r := sub_pos.mpr hr'.2
    unfold D
    positivity
  have hn : 0 ≤ (r*gradientVariance μ Q-D (markZ x Q) r*centerFirst μ Q r)^2/
      (2*markY β Q*gradientVariance μ Q*D (markZ x Q) r) := by positivity
  linarith [hbound r hr]

end SlowEquilibration.LatitudeGroundTrial
