-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalFiniteEnsembleTransfer

/-! The disorder-integrated finite-ensemble inequality in source Proposition
9.16. Its hypotheses expose the remaining analytic tasks: overlap-score
failure, replicated-mean low-energy mass, and high-energy relocation. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalCoarseLimit

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet
open SphericalAging.HardSphereDynamics
open PureCapturePhysicalDiagonalBridge
open PureCapturePhysicalCoarseTransfer
open PureCapturePhysicalFiniteEnsembleTransfer
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def expectedFiniteFailure {n k T : ℕ} (μ : FiniteMixture)
    (β Q θ : ℝ) : ℝ :=
  ∫ J : Disorder (n+2) μ.maxDegree,
    (physicalEnsembleLaw (k := k) (T := T) μ β J).real
      (allBlocksFail Q θ) ∂disorderLaw (n+2) μ.maxDegree

def expectedFiniteLowEnergy {n k T : ℕ} (μ : FiniteMixture)
    (β Q θ e τ₁ : ℝ) : ℝ :=
  ∫ J : Disorder (n+2) μ.maxDegree,
    (physicalEnsembleLaw (k := k) (T := T) μ β J).real
      (someSuccessfulBlockLowEnergy μ J Q θ e τ₁)
      ∂disorderLaw (n+2) μ.maxDegree

/-- A fixed-dimensional physical source-9.16 bound, averaged over the
original disorder. The finite replica probabilities are actual Gibbs product
probabilities. All source-specific probability estimates can be inserted
without changing the deterministic geometric argument. -/
theorem expectedUncovered_le_finiteFailure_add_lowEnergy_add_relocationFailure
    {n k T : ℕ} (μ : FiniteMixture) (β : ℝ)
    {Q θ a a₁ r e τ τ₁ : ℝ} (hτ : τ₁ ≤ τ) (ha : a < a₁-r)
    (hscore : ∀ x : Vector (n+2), ∀ σ : Fin k → Vector (n+2),
      OnSphere x → (∀ i, OnSphere (σ i)) →
      goodCompanionBlock Q θ x σ →
      ‖physicalTrainingCenter σ‖ ^ 2 = (n+2 : ℕ) ∧
        a₁ < overlap x (physicalTrainingCenter σ))
    (Ω : Set (Disorder (n+2) μ.maxDegree)) (hΩ : MeasurableSet Ω)
    (hrelocate : ∀ J ∈ Ω, ∀ w : Vector (n+2),
      ‖w‖ ^ 2 = (n+2 : ℕ) →
      (n+2 : ℕ) * (e-τ₁) ≤ field (mixtureCoefficients μ) J w →
      ∃ u : Vector (n+2),
        ‖u‖ ^ 2 = (n+2 : ℕ) ∧
        surfaceGradient (field (mixtureCoefficients μ) J) u = 0 ∧
        ‖u-w‖ ≤ r*Real.sqrt (n+2 : ℕ) ∧
        field (mixtureCoefficients μ) J w ≤
          field (mixtureCoefficients μ) J u)
    (hfailure : Integrable (fun J : Disorder (n+2) μ.maxDegree =>
      (physicalEnsembleLaw (k := k) (T := T) μ β J).real
        (allBlocksFail Q θ)) (disorderLaw (n+2) μ.maxDegree))
    (hlow : Integrable (fun J : Disorder (n+2) μ.maxDegree =>
      (physicalEnsembleLaw (k := k) (T := T) μ β J).real
        (someSuccessfulBlockLowEnergy μ J Q θ e τ₁))
        (disorderLaw (n+2) μ.maxDegree)) :
    expectedUncoveredGibbsMass n μ β a e τ ≤
      (disorderLaw (n+2) μ.maxDegree).real Ωᶜ +
        expectedFiniteFailure (n := n) (k := k) (T := T) μ β Q θ +
        expectedFiniteLowEnergy (n := n) (k := k) (T := T) μ β Q θ e τ₁ := by
  let d := disorderLaw (n+2) μ.maxDegree
  let B : Disorder (n+2) μ.maxDegree → ℝ := fun J =>
    (physicalEnsembleLaw (k := k) (T := T) μ β J).real (allBlocksFail Q θ)
  let E : Disorder (n+2) μ.maxDegree → ℝ := fun J =>
    (physicalEnsembleLaw (k := k) (T := T) μ β J).real
      (someSuccessfulBlockLowEnergy μ J Q θ e τ₁)
  let I : Disorder (n+2) μ.maxDegree → ℝ := Ωᶜ.indicator (fun _ => 1)
  have hI : Integrable I d := (integrable_const 1).indicator hΩ.compl
  have hB : Integrable B d := hfailure
  have hE : Integrable E d := hlow
  have hbound (J : Disorder (n+2) μ.maxDegree) :
      uncoveredGibbsMass n μ β a e τ J ≤ I J + B J + E J := by
    by_cases hJ : J ∈ Ω
    · have hfinite := physical_uncoveredGibbsMass_le_failure_add_lowEnergy (T := T)
        μ β J hτ ha hscore (hrelocate J hJ)
      have hIzero : I J = 0 := by
        apply Set.indicator_of_notMem
        simpa using hJ
      rw [hIzero,zero_add]
      exact hfinite
    · have hmass := (uncoveredGibbsMass_mem_unit n μ β a e τ J).2
      have hB : 0 ≤ B J := measureReal_nonneg
      have hE : 0 ≤ E J := measureReal_nonneg
      have hJc : J ∈ Ωᶜ := hJ
      simp only [I,Set.indicator_of_mem hJc,B,E]
      linarith
  have hintegral := integral_mono (uncoveredGibbsMass_integrable n μ β a e τ)
    ((hI.add hB).add hE) hbound
  change expectedUncoveredGibbsMass n μ β a e τ ≤ _ at hintegral
  have hIeq : (∫ J, I J ∂d) = d.real Ωᶜ := by
    change (∫ J, Ωᶜ.indicator (fun _ => (1 : ℝ)) J ∂d) = _
    rw [integral_indicator_const 1 hΩ.compl, smul_eq_mul, mul_one]
  change expectedUncoveredGibbsMass n μ β a e τ ≤
    ∫ J, ((I + B) J + E J) ∂d at hintegral
  rw [integral_add (hI.add hB) hE] at hintegral
  change expectedUncoveredGibbsMass n μ β a e τ ≤
    (∫ J, I J + B J ∂d) + ∫ J, E J ∂d at hintegral
  rw [integral_add hI hB, hIeq] at hintegral
  simpa only [expectedFiniteFailure, expectedFiniteLowEnergy,d,B,E] using hintegral

end SlowEquilibration.PureCapturePhysicalCoarseLimit
