-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalAsymptoticFullCompletion
public import SlowEquilibration.DirectingPhysicalNorm

/-! Source-9.16 coarse cover with the norm-Q directing conclusion derived
from the five preceding inputs of manuscript Theorem 6.3, all stated only
for genuine asymptotic physical full overlap-array limits. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalAsymptoticNormSourceCompletion

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet
open SphericalAging.HardSphereDynamics
open PureCaptureOverlapScoreCoordinates
open PureCapturePhysicalScoreTightness
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalFullToScore
open PureCapturePhysicalAsymptoticFullLift
open PureCaptureRandomDirectingScoreArray
open PureCapturePhysicalAsymptoticFullCompletion
open PureCapturePhysicalCoarseTransfer
open PureCapturePhysicalFiniteEnsembleTransfer
open PureCapturePhysicalCoarseLimit
open PureCapturePhysicalLowEnergyMeasurability
open PureCapturePhysicalDiagonalBridge
open SlowEquilibration.DirectingPhysical
open GaussianReplicaKernel GaussianGGEnsemble
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-- Dovbysh--Sudakov existence plus the five source inputs of Theorem 6.3
imply a norm-Q representation on every genuine physical asymptotic array
limit. Each source input is indexed by the same limit and its directing
kernel; the norm-Q conclusion is proved, not assumed. -/
theorem norm_Q_representation_of_asymptotic_source_inputs
    {Ξ H : Type*} [MeasurableSpace Ξ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    {k : ℕ} (μ : FiniteMixture) (β : ℝ) {x Q : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hDS : ∀ z ∈ physicalFullAsymptoticLimitSet μ β,
      ∃ R : RandomDirectingData Ξ H,
        (∀ T, fullToScoreArray k z T = R.scoreLaw k T) ∧
        (∀ᵐ ω ∂(R.disorderLaw), ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ≤ 1) ∧
        (∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q →
          ∃ j : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
            law R.disorderLaw R.directingKernel j
              (equilateralEvent (H := H) j q ρ) = 0) ∧
        (∃ a < (1 : ℝ), law R.disorderLaw R.directingKernel 2
          (pairCapEvent (H := H) a) = 0) ∧
        CovarianceGG R.disorderLaw R.directingKernel μ.xi ∧
        (∫ r, μ.xi r ∂overlapLaw R.disorderLaw R.directingKernel) =
          (1 - x) * μ.xi Q) :
    ∀ z ∈ physicalFullAsymptoticLimitSet μ β,
      ∃ R : RandomDirectingData Ξ H,
        (∀ᵐ ω ∂(R.disorderLaw),
          ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ^ 2 = Q) ∧
        ∀ T, fullToScoreArray k z T = R.scoreLaw k T := by
  intro z hz
  obtain ⟨R, hscore, hball, hexclude, hcap, hGG, hmean⟩ := hDS z hz
  letI : IsProbabilityMeasure R.disorderLaw := R.disorderProbability
  letI : IsMarkovKernel R.directingKernel := R.directingMarkov
  have hnorm := directing_norm_Q_of_source_inputs R.disorderLaw
    R.directingKernel μ hx hQ hball hexclude hcap hGG hmean
  exact ⟨R, hnorm, hscore⟩

/-- Corrected physical source-9.16 implication with the source norm-Q
argument exposed as DS existence, unit-ball support, replica exclusion,
cap exclusion, covariance GG, and the pair covariance mean. -/
theorem expectedUncoveredGibbsMass_tendsto_zero_of_asymptotic_source_norm_inputs
    {Ξ H : Type*} [MeasurableSpace Ξ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    {k : ℕ} (μ : FiniteMixture) (β : ℝ)
    {x Q θ a a₁ r e τ τ₁ : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hθ : 0 < θ) (hτ : τ₁ ≤ τ) (ha : a < a₁-r)
    (hscore : ∀ n : ℕ, ∀ y : Vector (n+2), ∀ σ : Fin k → Vector (n+2),
      OnSphere y → (∀ i, OnSphere (σ i)) →
      goodCompanionBlock Q θ y σ →
      ‖physicalTrainingCenter σ‖ ^ 2 = (n+2 : ℕ) ∧
        a₁ < overlap y (physicalTrainingCenter σ))
    (Ω : ∀ n : ℕ, Set (Disorder (n+2) μ.maxDegree))
    (hΩ : ∀ n, MeasurableSet (Ω n))
    (hrelocate : ∀ n, ∀ J ∈ Ω n, ∀ w : Vector (n+2),
      ‖w‖ ^ 2 = (n+2 : ℕ) →
      (n+2 : ℕ) * (e-τ₁) ≤ field (mixtureCoefficients μ) J w →
      ∃ u : Vector (n+2),
        ‖u‖ ^ 2 = (n+2 : ℕ) ∧
        surfaceGradient (field (mixtureCoefficients μ) J) u = 0 ∧
        ‖u-w‖ ≤ r*Real.sqrt (n+2 : ℕ) ∧
        field (mixtureCoefficients μ) J w ≤
          field (mixtureCoefficients μ) J u)
    (hrelocateProb : Tendsto (fun n : ℕ =>
      (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ) atTop (𝓝 0))
    (hDS : ∀ z ∈ physicalFullAsymptoticLimitSet μ β,
      ∃ R : RandomDirectingData Ξ H,
        (∀ T, fullToScoreArray k z T = R.scoreLaw k T) ∧
        (∀ᵐ ω ∂(R.disorderLaw), ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ≤ 1) ∧
        (∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q →
          ∃ j : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
            law R.disorderLaw R.directingKernel j
              (equilateralEvent (H := H) j q ρ) = 0) ∧
        (∃ a < (1 : ℝ), law R.disorderLaw R.directingKernel 2
          (pairCapEvent (H := H) a) = 0) ∧
        CovarianceGG R.disorderLaw R.directingKernel μ.xi ∧
        (∫ r, μ.xi r ∂overlapLaw R.disorderLaw R.directingKernel) =
          (1 - x) * μ.xi Q)
    (hlow : ∀ T : ℕ, Tendsto (fun n : ℕ =>
      expectedFiniteLowEnergy (n := n) (k := k) (T := T)
        μ β Q θ e τ₁) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      expectedUncoveredGibbsMass n μ β a e τ) atTop (𝓝 0) := by
  exact expectedUncoveredGibbsMass_tendsto_zero_of_asymptotic_full_array_source_inputs
    μ β hθ hτ ha hscore Ω hΩ hrelocate hrelocateProb
    (norm_Q_representation_of_asymptotic_source_inputs μ β hx hQ hDS) hlow

end SlowEquilibration.PureCapturePhysicalAsymptoticNormSourceCompletion
