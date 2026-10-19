-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalAsymptoticScoreLimits
public import SlowEquilibration.PureCapturePhysicalLowEnergyMeasurability

/-! Asymptotic physical source-9.16 implication with the three remaining
analytic inputs displayed explicitly: pointwise companion extraction on
physical asymptotic score-law limits, replicated-center low-energy decay, and
high-energy relocation. All finite Gibbs, measurability, compactness,
uniformization, and limiting transfer steps are proved in imports. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalAsymptoticCoarseCompletion

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet
open SphericalAging.HardSphereDynamics
open PureCaptureOverlapScoreCoordinates
open PureCapturePhysicalScoreTightness
open PureCaptureScorePrefixConsistency
open PureCapturePhysicalAsymptoticScoreLimits
open PureCapturePhysicalCoarseTransfer
open PureCapturePhysicalFiniteEnsembleTransfer
open PureCapturePhysicalCoarseLimit
open PureCapturePhysicalLowEnergyMeasurability
open PureCapturePhysicalDiagonalBridge
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The genuine disorder-averaged Gibbs mass outside critical-point caps
tends to zero after the three remaining source-specific analytic inputs
are supplied. The physical finite failure term is handled by the proved
asymptotic score-array compactness and projective consistency. -/
theorem expectedUncoveredGibbsMass_tendsto_zero_of_asymptotic_source_inputs
    {k : ℕ} (μ : FiniteMixture) (β : ℝ)
    {Q θ a a₁ r e τ τ₁ : ℝ} (hτ : τ₁ ≤ τ) (ha : a < a₁-r)
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
    (hpoint : ∀ x ∈ physicalScoreAsymptoticLimitSet k μ β,
      Tendsto (fun T =>
        ((x T : Measure (ScoreCoordinates k T)) (scoreFailure Q θ)).toReal)
        atTop (𝓝 0))
    (hlow : ∀ T : ℕ, Tendsto (fun n : ℕ =>
      expectedFiniteLowEnergy (n := n) (k := k) (T := T)
        μ β Q θ e τ₁) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      expectedUncoveredGibbsMass n μ β a e τ) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact Filter.Eventually.of_forall fun n =>
      hc.trans_le (expectedUncoveredGibbsMass_nonneg n μ β a e τ)
  · intro ε hε
    have hthird : 0 < ε / 3 := by positivity
    obtain ⟨T, hfailure⟩ :=
      expectedFiniteFailure_eventually_small_of_asymptotic_limits
        μ β Q θ hpoint (ε/3) hthird
    have hreloc := hrelocateProb.eventually (gt_mem_nhds hthird)
    have henergy := (hlow T).eventually (gt_mem_nhds hthird)
    filter_upwards [hfailure, hreloc, henergy] with n hF hR hE
    have hbound :=
      expectedUncovered_le_finiteFailure_add_lowEnergy_add_relocationFailure
        (n := n) (k := k) (T := T) μ β hτ ha (hscore n)
        (Ω n) (hΩ n) (hrelocate n)
        (finiteFailureProbability_integrable μ β Q θ)
        (finiteLowEnergyProbability_integrable μ β Q θ e τ₁)
    linarith

end SlowEquilibration.PureCapturePhysicalAsymptoticCoarseCompletion
