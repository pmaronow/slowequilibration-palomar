-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalNormFromReplicaDecay
public import SlowEquilibration.PureCapturePhysicalPairMeanDirecting

/-! Norm-Q directing support from physical finite-volume replica
exclusion, pair-cap decay, and the physical pair-covariance mean. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalNormFromPhysicalMean

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalFullToScore
open PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalReplicaExclusionLimit
open PureCapturePhysicalReplicaExclusionDirecting
open PureCapturePhysicalNormFromReplicaDecay
open PureCapturePhysicalPairMeanDirecting
open PureCaptureRandomDirectingScoreArray
open SlowEquilibration.DirectingPhysical
open GaussianGGEnsemble
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem asymptoticPhysicalFullLimit_norm_Q_of_physical_mean_and_decay
    {Ξ H : Type*} [MeasurableSpace Ξ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    {k : ℕ} (μ : FiniteMixture) (β : ℝ) {x Q : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hphysicalExclude : ∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q →
      ∃ m : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
        Tendsto (fun n : ℕ =>
          (physicalFullOverlapLaw (n := n) (m := m) μ β :
            Measure (FullOverlapCoordinates m)) (fullEquilateralEvent m q ρ))
          atTop (𝓝 0))
    (hphysicalCap : ∃ a < (1 : ℝ),
      Tendsto (fun n : ℕ =>
        (physicalFullOverlapLaw (n := n) (m := 2) μ β :
          Measure (FullOverlapCoordinates 2)) (fullPairCapEvent a))
        atTop (𝓝 0))
    (hphysicalMean : Tendsto (fun n : ℕ =>
      ∫ c, μ.xi (c 0 1) ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1 - x) * μ.xi Q)))
    (hDS : ∀ z ∈ physicalFullAsymptoticLimitSet μ β,
      ∃ R : RandomDirectingData Ξ H,
        (∀ m, z m = directingDataFullLaw R m) ∧
        (∀ᵐ ω ∂(R.disorderLaw),
          ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ≤ 1) ∧
        CovarianceGG R.disorderLaw R.directingKernel μ.xi) :
    ∀ z ∈ physicalFullAsymptoticLimitSet μ β,
      ∃ R : RandomDirectingData Ξ H,
        (∀ᵐ ω ∂(R.disorderLaw),
          ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ^ 2 = Q) ∧
        ∀ T, fullToScoreArray k z T = R.scoreLaw k T := by
  apply asymptoticPhysicalFullLimit_norm_Q_of_replica_decay
    μ β hx hQ hphysicalExclude hphysicalCap
  intro z hz
  obtain ⟨R, hrep, hball, hGG⟩ := hDS z hz
  exact ⟨R, hrep, hball, hGG,
    directingPairCovarianceMean_eq_of_physical_tendsto μ β _
      hphysicalMean hz R hrep hball⟩

end SlowEquilibration.PureCapturePhysicalNormFromPhysicalMean
