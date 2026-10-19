-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalAsymptoticFullLift
public import SlowEquilibration.PureCapturePhysicalAsymptoticCoarseCompletion

/-! The asymptotic full-array formulation of the remaining Dovbysh--Sudakov
representation input in source Proposition 9.16. The physical full-array
limit, all its finite Gram/exchangeability properties, and its exact
projection to capture scores are proved in imports. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalAsymptoticFullCompletion

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet
open SphericalAging.HardSphereDynamics
open PureCaptureOverlapScoreCoordinates
open PureCapturePhysicalScoreTightness
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalFullToScore
open PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalAsymptoticScoreLimits
open PureCaptureRandomDirectingScoreArray
open PureCapturePhysicalCoarseTransfer
open PureCapturePhysicalFiniteEnsembleTransfer
open PureCapturePhysicalCoarseLimit
open PureCapturePhysicalLowEnergyMeasurability
open PureCapturePhysicalDiagonalBridge
open PureCapturePhysicalAsymptoticCoarseCompletion
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The only still-unproved limiting input for the capture score is now
posed on actual exchangeable positive-semidefinite physical full-array
weak limits, rather than on arbitrary score-coordinate limits. -/
theorem pointwise_scoreFailure_of_asymptotic_full_directing_representation
    {Ξ H : Type*} [MeasurableSpace Ξ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    {k : ℕ} (μ : FiniteMixture) (β Q θ : ℝ) (hθ : 0 < θ)
    (hDS : ∀ x ∈ physicalFullAsymptoticLimitSet μ β,
      ∃ R : RandomDirectingData Ξ H,
        (∀ᵐ ω ∂(R.disorderLaw), ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ^ 2 = Q) ∧
        ∀ T, fullToScoreArray k x T = R.scoreLaw k T) :
    ∀ y ∈ physicalScoreAsymptoticLimitSet k μ β,
      Tendsto (fun T =>
        ((y T : Measure (ScoreCoordinates k T)) (scoreFailure Q θ)).toReal)
        atTop (𝓝 0) := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := physicalAsymptoticScoreLimit_exists_fullAsymptoticLimit k μ β hy
  obtain ⟨R, hQ, hrepr⟩ := hDS x hx
  have heq : (fun T =>
      ((y T : Measure (ScoreCoordinates k T)) (scoreFailure Q θ)).toReal) =
      (fun T =>
        ((R.scoreLaw k T : Measure (ScoreCoordinates k T))
          (scoreFailure Q θ)).toReal) := by
    funext T
    rw [← hxy, hrepr T]
  rw [heq]
  exact R.scoreLaw_failure_tendsto_zero k hθ hQ

/-- The actual original-disorder uncovered Gibbs mass tends to zero
assuming the source Dovbysh--Sudakov/norm-Q representation of full
physical overlap-array limits, replicated-center low-energy decay, and
high-energy critical-point relocation. -/
theorem expectedUncoveredGibbsMass_tendsto_zero_of_asymptotic_full_array_source_inputs
    {Ξ H : Type*} [MeasurableSpace Ξ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    {k : ℕ} (μ : FiniteMixture) (β : ℝ)
    {Q θ a a₁ r e τ τ₁ : ℝ} (hθ : 0 < θ)
    (hτ : τ₁ ≤ τ) (ha : a < a₁-r)
    (hscore : ∀ n : ℕ, ∀ x : Vector (n+2), ∀ σ : Fin k → Vector (n+2),
      OnSphere x → (∀ i, OnSphere (σ i)) →
      goodCompanionBlock Q θ x σ →
      ‖physicalTrainingCenter σ‖ ^ 2 = (n+2 : ℕ) ∧
        a₁ < overlap x (physicalTrainingCenter σ))
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
    (hDS : ∀ x ∈ physicalFullAsymptoticLimitSet μ β,
      ∃ R : RandomDirectingData Ξ H,
        (∀ᵐ ω ∂(R.disorderLaw), ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ^ 2 = Q) ∧
        ∀ T, fullToScoreArray k x T = R.scoreLaw k T)
    (hlow : ∀ T : ℕ, Tendsto (fun n : ℕ =>
      expectedFiniteLowEnergy (n := n) (k := k) (T := T)
        μ β Q θ e τ₁) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      expectedUncoveredGibbsMass n μ β a e τ) atTop (𝓝 0) := by
  exact expectedUncoveredGibbsMass_tendsto_zero_of_asymptotic_source_inputs
    μ β hτ ha hscore Ω hΩ hrelocate hrelocateProb
    (pointwise_scoreFailure_of_asymptotic_full_directing_representation μ β Q θ hθ hDS) hlow

end SlowEquilibration.PureCapturePhysicalAsymptoticFullCompletion
