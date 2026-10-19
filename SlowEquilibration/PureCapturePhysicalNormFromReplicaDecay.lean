-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalReplicaExclusionDirecting

/-! The source directing norm-Q conclusion, with replica exclusion and
near-one pair exclusion stated for actual finite physical Gibbs samples.
Their transfer through weak limits and the full DS representation is
proved in imports. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalNormFromReplicaDecay

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalFullToScore
open PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalReplicaExclusionLimit
open PureCaptureDirectingFullToScore
open PureCapturePhysicalReplicaExclusionDirecting
open PureCaptureRandomDirectingScoreArray
open SlowEquilibration.DirectingPhysical
open GaussianReplicaKernel
open GaussianGGEnsemble
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-- For every asymptotic physical full-array limit, the directing norm
is Q once the genuine full DS representation, the finite-volume thermal
replica decay, and the source covariance GG/mean inputs are available.
The finite-volume decay is required along all dimensions, as in source
Lemma 6.5, rather than along one convenient subsequence. -/
theorem asymptoticPhysicalFullLimit_norm_Q_of_replica_decay
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
    (hDS : ∀ z ∈ physicalFullAsymptoticLimitSet μ β,
      ∃ R : RandomDirectingData Ξ H,
        (∀ m, z m = directingDataFullLaw R m) ∧
        (∀ᵐ ω ∂(R.disorderLaw),
          ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ≤ 1) ∧
        CovarianceGG R.disorderLaw R.directingKernel μ.xi ∧
        (∫ r, μ.xi r ∂overlapLaw R.disorderLaw R.directingKernel) =
          (1 - x) * μ.xi Q) :
    ∀ z ∈ physicalFullAsymptoticLimitSet μ β,
      ∃ R : RandomDirectingData Ξ H,
        (∀ᵐ ω ∂(R.disorderLaw),
          ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ^ 2 = Q) ∧
        ∀ T, fullToScoreArray k z T = R.scoreLaw k T := by
  intro z hz
  obtain ⟨R, hrep, hball, hGG, hmean⟩ := hDS z hz
  letI : IsProbabilityMeasure R.disorderLaw := R.disorderProbability
  letI : IsMarkovKernel R.directingKernel := R.directingMarkov
  have hexclude : ∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q →
      ∃ m : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
        law R.disorderLaw R.directingKernel m
          (equilateralEvent (H := H) m q ρ) = 0 := by
    intro q hq hqQ
    obtain ⟨m, ρ, hρ, hdecay⟩ := hphysicalExclude q hq hqQ
    exact ⟨m, ρ, hρ,
      directing_equilateral_zero_of_physical_decay μ β hz R hrep m q ρ hdecay⟩
  obtain ⟨a, ha, hcapDecay⟩ := hphysicalCap
  have hcap : ∃ a < (1 : ℝ),
      law R.disorderLaw R.directingKernel 2
        (pairCapEvent (H := H) a) = 0 :=
    ⟨a, ha, directing_pairCap_zero_of_physical_decay μ β a hz R hrep hcapDecay⟩
  have hnorm := directing_norm_Q_of_source_inputs R.disorderLaw
    R.directingKernel μ hx hQ hball hexclude hcap hGG hmean
  exact ⟨R, hnorm,
    fullToScoreArray_eq_of_directing_full_representation R k z hrep⟩

end SlowEquilibration.PureCapturePhysicalNormFromReplicaDecay
