-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMaximumGlobalTail
public import SlowEquilibration.SphericalMarkedPrecisionIdentification

/-! All six original-field source microscopic maximum conclusions. Actual
centering and window counts are joined to an original Borel localization set
and the genuine global-maximum probability tail. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel SphericalGaussianJet SphericalForm
open scoped ENNReal Topology
set_option maxHeartbeats 300000

structure SourceMaximumAllConclusions (μ : FiniteMixture) (β x Q L R δ : ℝ) where
  first_moments : SourceMaximumFirstMomentConclusions μ β x Q L R
  good_set : ∀ n : ℕ,Set (Disorder (n+2) μ.maxDegree)
  good_set_measurable : ∀ n : ℕ,MeasurableSet (good_set n)
  good_set_failure_bound : ∃ c : ℝ,0 < c ∧ ∀ᶠ n : ℕ in atTop,
    disorderLaw (n+2) μ.maxDegree (good_set n)ᶜ ≤ ENNReal.ofReal (Real.exp (-c*(n+2 : ℕ)))
  high_maximizer_localized : ∀ n : ℕ,∀ J ∈ good_set n,∀ y : Vector (n+2),
    ‖y‖^2=(n+2 : ℕ) →
    IsMaxOn (field (centerCoefficients (mixtureCoefficients μ) Q) J)
      {z : Vector (n+2) | ‖z‖^2=(n+2 : ℕ)} y →
    (n+2 : ℕ)*(markE μ β x Q-δ) ≤ field (centerCoefficients (mixtureCoefficients μ) Q) J y →
    IsLocalMaxOn (field (centerCoefficients (mixtureCoefficients μ) Q) J)
      {z : Vector (n+2) | ‖z‖^2=(n+2 : ℕ)} y ∧
      actualScore (centerCoefficients (mixtureCoefficients μ) Q) J y 1 ∈ Ioo L R
  maximum_probability_limsup : ∀ t : ℝ,
    Filter.limsup (fun n : ℕ => (disorderLaw (n+2) μ.maxDegree).real
      {J | first_moments.center n+t ≤ sourceSphereMaximum n μ Q J}) atTop ≤ Real.exp (-(β*x)*t)

/-- Source `thm:mo-microscopic(a–f)` for the literal mixed tensor field and
its original disorder. All probabilistic conclusions are proved internally
from the actual one-step certificate and primitive source admissibility. -/
theorem sourceMaximum_all_six_conclusions (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (hδ : 0 < δ)
    (hScore : ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),∀ k ∈ Icc L R,
      (β*x)/2 ≤ sourceEnergySlope μ Q e k ∧ sourceEnergySlope μ Q e k ≤ (β*x+β)/2)
    (hA3 : δ ≤ sourceMarkedLeastCurvature μ Q*(sourceRadialClearance μ β Q (Ioo L R))^2/(8*(β*x))) :
    Nonempty (SourceMaximumAllConclusions μ β x Q L R δ) := by
  obtain ⟨d⟩ := sourceMaximum_first_moments μ h hnp hL hm hδ hScore
  refine ⟨{
    first_moments := d
    good_set := fun n => sourceHighCriticalGoodSet n μ Q (markE μ β x Q-δ) (Ioo L R)
    good_set_measurable := fun n => sourceHighCriticalGoodSet_measurable n μ Q _ _
    good_set_failure_bound := sourceHighCriticalGoodSet_exponential μ h hnp hm hA3
    high_maximizer_localized := ?_
    maximum_probability_limsup := sourceSphereMaximum_centered_probability_limsup μ h hnp hL hm hδ hA3 d
  }⟩
  intro n J hJ y hy hmax hhigh
  exact sourceHighCriticalGoodSet_localizes_maxima n μ Q (markE μ β x Q-δ) (Ioo L R)
    hJ hy hmax hhigh

end SlowEquilibration.SphericalMarkedWindows
