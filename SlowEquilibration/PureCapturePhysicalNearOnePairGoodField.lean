-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalGibbsCapFromField
public import SlowEquilibration.SphericalReplicaFromCaps
public import SlowEquilibration.SphericalFieldSupremum
public import SlowEquilibration.PureCapturePhysicalReplicaExclusionLimit

/-! The literal same-disorder two-replica Gibbs pair has exponentially small
near-one overlap mass on a whole-sphere field-bound event. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalNearOnePairGoodField
open SlowEquilibration SlowEquilibration.SphericalModel
open SlowEquilibration.PureCapturePhysicalGibbsCapFromField
open SlowEquilibration.PureCapturePhysicalFullOverlapArray
open SlowEquilibration.PureCapturePhysicalReplicaExclusionLimit
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

/-- Conditional two-replica near-one mass from the original spherical field
bound, with the axis-uniform Gibbs cap estimate proved in imports. -/
theorem physical_pair_near_one_le_of_field_bound
    (μ : FiniteMixture) {n : ℕ} (hn : 2 ≤ n)
    {β K : ℝ} (hβ : 0 ≤ β)
    (J : Disorder (n+1) μ.maxDegree)
    (hfield : ∀ x : Vector (n+1), ‖x‖^2 = ((n+1 : ℕ) : ℝ) →
      |field (mixtureCoefficients μ) J x| ≤ K*((n+1 : ℕ) : ℝ))
    {a s : ℝ} (ha : 0 < a) (has : a < s) (hs : s < 1) :
    ((gibbsLaw (n+1) β (field (mixtureCoefficients μ) J)).prod
      (gibbsLaw (n+1) β (field (mixtureCoefficients μ) J))).real
      (absoluteReplicaOverlapEvent s) ≤
      2*(Real.exp (2*β*K*((n+1 : ℕ) : ℝ)) *
        (4*Real.sqrt (n : ℝ)*(Real.sqrt (1-a^2))^(n-2))) := by
  let π := gibbsLaw (n+1) β (field (mixtureCoefficients μ) J)
  letI : IsProbabilityMeasure π :=
    gibbsLaw_probability (by omega) β
      (field_contDiff (mixtureCoefficients μ) J).continuous
  have hb : 0 ≤ Real.exp (2*β*K*((n+1 : ℕ) : ℝ)) *
      (4*Real.sqrt (n : ℝ)*(Real.sqrt (1-a^2))^(n-2)) := by positivity
  apply replica_mass_le_of_uniform_caps π (gibbsLaw_support (by omega) β
    (field (mixtureCoefficients μ) J)) hb
  intro u hu
  exact gibbsLaw_near_one_cap_bound hn hβ
    (field_contDiff (mixtureCoefficients μ) J).continuous hfield
    u hu ha has hs

end SlowEquilibration.PureCapturePhysicalNearOnePairGoodField
