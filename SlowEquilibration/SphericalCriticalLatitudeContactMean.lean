-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCriticalLatitudeScoreMean
public import SlowEquilibration.SphericalOnePointContactSaddle

/-! The actual conditional latitude mean at the literal certified ground
marks has the manuscript closed form. It follows from the true inverse
score covariance and the independently proved contact slope identities. -/

@[expose] public section
namespace SlowEquilibration.SphericalCriticalLatitude
noncomputable section
open SphericalModel SphericalMarkedWindows SphericalSequentialRegression
open SphericalParisiConditionedLatitudeCovariance SphericalTAPCertificate TwoAtomStationarity
open scoped Matrix
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The source mean is paired with the literal energy and radial score
slopes; symmetry of the actual physical precision matrix is proved. -/
theorem sourceConditionalMean_eq_scoreSlopes (μ : FiniteMixture) (Q e k r : ℝ) :
    sourceConditionalMean μ Q e k r=
      centerCovariance μ Q r*sourceEnergySlope μ Q e k+
        r*centerFirst μ Q r*sourceRadialSlope μ Q e k := by
  have hs : (μ.scoreCovariance Q).IsSymm := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hp := hs.inv.apply 1 0
  simp only [sourceConditionalMean,sourceCross,scorePairEquiv_apply,dotProduct,
    Matrix.mulVec,Fin.sum_univ_two]
  change centerCovariance μ Q r*(((μ.scoreCovariance Q)⁻¹) 0 0*e+
      ((μ.scoreCovariance Q)⁻¹) 0 1*k)+
    r*centerFirst μ Q r*(((μ.scoreCovariance Q)⁻¹) 1 0*e+
      ((μ.scoreCovariance Q)⁻¹) 1 1*k)=_
  unfold sourceEnergySlope sourceRadialSlope sourceEnergyCurvature sourceRadialCurvature
  rw [hp]
  ring

/-- Source10.12(a), the exact ground-mark conditional latitude mean. -/
theorem sourceConditionalMean_at_contact (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) (r : ℝ) :
    sourceConditionalMean μ Q (markE μ β x Q) (markK μ β Q) r=
      (r*centerFirst μ Q r+markZ x Q*centerCovariance μ Q r)/markY β Q := by
  rw [sourceConditionalMean_eq_scoreSlopes,sourceEnergySlope_at_contact μ h hnp,
    sourceRadialSlope_at_contact μ h hnp,←markZ_div_markY h.beta_pos h.overlap_range]
  ring

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

omit [CompactSpace K] in
/-- The actual finite-coefficient continuous-field mean has the same
literal source formula at every point of a certified ground-state latitude. -/
theorem actual_criticalContinuousMean_at_contact (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) (n : ℕ)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (z : K → Vector (n+1)) (hz : Continuous z) (v : K) {r : ℝ}
    (hr : overlap u (z v)=r) :
    criticalContinuousMean n μ Q u z hz (scorePairEquiv (markE μ β x Q,markK μ β Q)) v=
      (n+1 : ℕ)*(r*centerFirst μ Q r+markZ x Q*centerCovariance μ Q r)/markY β Q := by
  rw [criticalContinuousMean_eq_source n μ h.overlap_range.1 hnp u hu z hz,
    hr,sourceConditionalMean_at_contact μ h hnp]
  ring

end
end SlowEquilibration.SphericalCriticalLatitude
