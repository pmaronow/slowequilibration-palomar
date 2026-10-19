-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalNormFromPhysicalMean
public import SlowEquilibration.PureCapturePhysicalGGBorelDirectingTransfer

/-! Source directing norm-Q support from the genuine physical energy budget,
physical pair mean, replica exclusion and near-one cap exclusion. Covariance
GG is proved from the physical array rather than postulated on the directing
kernel. The Dovbysh--Sudakov representation remains an explicit input. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalNormFromEnergyAndDecay

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalFullToScore
open PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalReplicaExclusionLimit
open PureCapturePhysicalNormFromPhysicalMean
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
weak limit, using the original Hamiltonian's o(N) thermal and quenched
energy deviations to prove covariance GG. -/
theorem asymptoticPhysicalFullLimit_norm_Q_of_energy_and_decay
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
    (hbudget : Tendsto (fun n : ℕ =>
      (GaussianPerturbationDeviation.meanThermalDeviation
          (PureCapturePhysicalShellGG.shellLaw (n+2))
          (PureCapturePhysicalShellGG.shellLinear (mixtureCoefficients μ))
          (fun _ => true) β +
        GaussianPerturbationIntegrated.energyFluctuation
          (PureCapturePhysicalShellGG.shellLaw (n+2))
          (PureCapturePhysicalShellGG.shellLinear (mixtureCoefficients μ))
          (fun _ => true) β) / ((n+2 : ℕ) : ℝ)) atTop (𝓝 0))
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
  apply asymptoticPhysicalFullLimit_norm_Q_of_physical_mean_and_decay
    μ β hx hQ hphysicalExclude hphysicalCap hphysicalMean
  intro z hz
  obtain ⟨R, hrep, hball⟩ := hDS z hz
  exact ⟨R, hrep, hball,
    covarianceGG_of_physical_sublinear_budget μ hβ hbudget hz R hrep hball⟩

end SlowEquilibration.PureCapturePhysicalNormFromEnergyAndDecay
