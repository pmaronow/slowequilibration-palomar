-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalNormFromPressureAndDecayDS
public import SlowEquilibration.PureCapturePhysicalNearOneDecay

/-! Physical norm-Q directing conclusion with both DS representation and
near-one pair exclusion derived from the original Gibbs ensemble. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalNormFromPressureAndExclusionDS

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalFullToScore
open PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalReplicaExclusionLimit
open PureCapturePhysicalNormFromPressureAndDecayDS
open PureCapturePhysicalNearOneDecay
open PureCapturePhysicalReplicaExclusionDirecting
open PureCaptureRandomDirectingScoreArray
open SlowEquilibration.DirectingPhysical
open GaussianGGEnsemble
open OverlapPaper
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The original-temperature covariance GG and physical near-one cap follow
from the pressure limit and Gaussian spherical entropy. The remaining
source inputs are replica exclusion away from Q and the pair covariance
mean. -/
theorem asymptoticPhysicalFullLimit_norm_Q_of_pressure_exclusion_mean
    {k : ℕ} (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β) {x Q : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hphysicalExclude : ∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q →
      ∃ m : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
        Tendsto (fun n : ℕ =>
          (physicalFullOverlapLaw (n := n) (m := m) μ β :
            Measure (FullOverlapCoordinates m)) (fullEquilateralEvent m q ρ))
          atTop (𝓝 0))
    (hphysicalMean : Tendsto (fun n : ℕ =>
      ∫ c, μ.xi (c 0 1) ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1 - x) * μ.xi Q)))
    (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (p t)))
    (hpdiff : DifferentiableAt ℝ p β) :
    ∀ z ∈ physicalFullAsymptoticLimitSet μ β,
      ∃ R : RandomDirectingData (ProbabilityMeasure DSHilbert) DSHilbert,
        (∀ᵐ ω ∂(R.disorderLaw),
          ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ^ 2 = Q) ∧
        ∀ T, fullToScoreArray k z T = R.scoreLaw k T := by
  exact asymptoticPhysicalFullLimit_norm_Q_of_pressure_and_decay_DS
    μ hβ hx hQ hphysicalExclude
    (physical_pair_near_one_decay μ hβ.le) hphysicalMean
    p hp hpdiff

end SlowEquilibration.PureCapturePhysicalNormFromPressureAndExclusionDS
