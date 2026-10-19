-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalNormFromEnergyAndDecay
public import SlowEquilibration.PureCapturePhysicalPanchenkoUnconditionalEnergy

/-! Source directing norm-Q support with the original physical energy budget
proved from a differentiable pointwise pressure limit. Replica decay, the
physical pair mean and Dovbysh--Sudakov representation remain explicit. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalNormFromPressureAndDecay

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalFullToScore
open PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalReplicaExclusionLimit
open PureCapturePhysicalNormFromPhysicalMean
open PureCapturePhysicalNormFromEnergyAndDecay
open PureCapturePhysicalPanchenkoUnconditionalEnergy
open PureCapturePhysicalGGBorelDirectingTransfer
open PureCaptureDirectingFullToScore
open PureCapturePhysicalReplicaExclusionDirecting
open PureCaptureRandomDirectingScoreArray
open SlowEquilibration.DirectingPhysical
open GaussianGGEnsemble
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The source Theorem 6.3 norm conclusion for every physical full-array
weak limit. Its physical energy self-averaging and covariance GG now follow
from pressure convergence and differentiability at the original β. -/
theorem asymptoticPhysicalFullLimit_norm_Q_of_pressure_and_decay
    {Ξ H : Type*} [MeasurableSpace Ξ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    {k : ℕ} (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β) {x Q : ℝ}
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
    (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (p t)))
    (hpdiff : DifferentiableAt ℝ p β)
    (hDS : ∀ z ∈ physicalFullAsymptoticLimitSet μ β,
      ∃ R : RandomDirectingData Ξ H,
        (∀ m, z m = directingDataFullLaw R m) ∧
        (∀ᵐ ω ∂(R.disorderLaw),
          ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ≤ 1)) :
    ∀ z ∈ physicalFullAsymptoticLimitSet μ β,
      ∃ R : RandomDirectingData Ξ H,
        (∀ᵐ ω ∂(R.disorderLaw),
          ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ^ 2 = Q) ∧
        ∀ T, fullToScoreArray k z T = R.scoreLaw k T := by
  exact asymptoticPhysicalFullLimit_norm_Q_of_energy_and_decay
    μ hβ hx hQ hphysicalExclude hphysicalCap hphysicalMean
    (physical_total_energy_budget_tendsto_zero μ β p hp hpdiff) hDS

end SlowEquilibration.PureCapturePhysicalNormFromPressureAndDecay
