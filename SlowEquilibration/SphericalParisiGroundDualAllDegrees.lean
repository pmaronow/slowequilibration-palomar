-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiPositiveDegreeRestriction
public import SlowEquilibration.SphericalParisiSphereNetGround

@[expose] public section

/-! True one-step dual ground upper for the original finite Gaussian field
with any nonnegative degrees, including its genuine random constant block.
The expected constant contribution is removed by the proved equality of
actual Gaussian expected maxima, not by replacing the physical field. -/

namespace SlowEquilibration.SphericalParisiGroundDualAllDegrees
noncomputable section
open MeasureTheory Filter Set
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance SphericalParisiGroundRSUpper
open SphericalParisiOneStepDualScalar SphericalParisiPositiveDegreeRestriction
open scoped Topology
set_option maxHeartbeats 600000
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem eventual_actual_ground_oneStepDual_upper_all_degrees
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i)
    {α κ q : ℝ} (hα : 0 < α) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hmargin : 0 < κ-α*(xi1 d c 1-xi1 d c q))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      (∫ g,actualMaximum (N := N) d c g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))/(N : ℝ) ≤
        oneStepDual d c α q κ+δ := by
  have hmargin' : 0 < κ-α*(xi1 (positiveDegree d) (positiveCoefficient d c) 1-
      xi1 (positiveDegree d) (positiveCoefficient d c) q) := by
    rw [← xi1_eq_positive d c 1,← xi1_eq_positive d c q]
    exact hmargin
  have HU := SphericalParisiSphereNet.eventual_actual_ground_oneStepDual_upper
    (positiveDegree d) (positiveCoefficient d c) (positive_coefficient_nonnegative d c hc)
    (positive_degree_ge_one d) hα hq hq1 hmargin' hδ
  filter_upwards [HU,eventually_gt_atTop (0 : ℕ)] with N hU hN
  rw [actual_expected_maximum_eq_positive hN d c hc,oneStepDual_eq_positive d c]
  exact hU

end
end SlowEquilibration.SphericalParisiGroundDualAllDegrees
