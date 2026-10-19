-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPanchenkoOriginalSphere
public import SlowEquilibration.PureCapturePhysicalPanchenkoThermalLimit
public import SlowEquilibration.PureCapturePhysicalFullArrayGGBorelExtension
public import SlowEquilibration.PureCapturePhysicalGGBorelDirectingTransfer

/-! Physical energy self-averaging and full-array covariance GG at every
differentiability point of a pointwise quenched pressure limit. The finite-
volume measures, disorder, and Hamiltonian are the original spherical model. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalPanchenkoUnconditionalEnergy

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalShellGG
open PureCapturePhysicalPanchenkoThermalLimit
open PureCapturePhysicalPanchenkoEnergyToGG
open PureCapturePhysicalPanchenkoActualDeviation
open PureCapturePhysicalPanchenkoOriginalSphere
open PureCapturePhysicalFullArrayGGBorelExtension
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalFiniteGGDefinitions
open PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalFullArrayGGTransfer
open PureCapturePhysicalGGBorelDirectingTransfer
open PureCaptureRandomDirectingScoreArray
open PureCapturePhysicalReplicaExclusionDirecting
open SlowEquilibration.DirectingPhysical
open GaussianPerturbationDeviation GaussianPerturbationIntegrated
open GaussianPerturbationSelfAveraging
open scoped Topology
set_option autoImplicit false

theorem physical_total_energy_budget_tendsto_zero
    (μ : FiniteMixture) (β : ℝ) (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (p t)))
    (hpdiff : DifferentiableAt ℝ p β) :
    Tendsto (fun n : ℕ =>
      (meanThermalDeviation (shellLaw (n+2))
          (shellLinear (mixtureCoefficients μ)) (fun _ => true) β +
        energyFluctuation (shellLaw (n+2))
          (shellLinear (mixtureCoefficients μ)) (fun _ => true) β) /
            ((n+2 : ℕ) : ℝ)) atTop (𝓝 0) :=
  physical_total_energy_budget_tendsto_zero_of_thermal μ β p hp hpdiff
    (physical_normalized_thermal_energy_fluctuation_tendsto_zero μ β p hp hpdiff)

theorem physical_mean_absolute_energy_deviation_tendsto_zero
    (μ : FiniteMixture) (β : ℝ) (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (p t)))
    (hpdiff : DifferentiableAt ℝ p β) :
    Tendsto (fun n : ℕ =>
      meanAbsoluteEnergyDeviation (shellLaw (n+2))
        (shellLinear (mixtureCoefficients μ)) (fun _ => true) β /
          ((n+2 : ℕ) : ℝ)) atTop (𝓝 0) :=
  physical_mean_absolute_energy_deviation_tendsto_zero_of_thermal
    μ β p hp hpdiff
    (physical_normalized_thermal_energy_fluctuation_tendsto_zero μ β p hp hpdiff)

theorem physical_original_sphere_energy_deviation_tendsto_zero
    (μ : FiniteMixture) (β : ℝ) (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (p t)))
    (hpdiff : DifferentiableAt ℝ p β) :
    Tendsto (fun n : ℕ =>
      (∫ g : EuclideanDisorder (n+2) μ.maxDegree,
        (∫ x : Vector (n+2),
          |field (mixtureCoefficients μ) (unpackDisorder g) x -
            meanScore (shellLaw (n+2))
              (shellLinear (mixtureCoefficients μ)) (fun _ => true) β|
            ∂gibbsLaw (n+2) β
              (field (mixtureCoefficients μ) (unpackDisorder g)))
        ∂SYK.standardGaussianMeasureOnEuclidean
          (Coordinate (n+2) μ.maxDegree)) / ((n+2 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have h := physical_mean_absolute_energy_deviation_tendsto_zero μ β p hp hpdiff
  convert h using 1
  funext n
  rw [physical_shell_deviation_eq_original_sphere (by omega : 1 ≤ n+2)]

theorem physical_covariance_gg_tendsto
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β) (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (p t)))
    (hpdiff : DifferentiableAt ℝ p β)
    (m : ℕ)
    (f : (n : ℕ) → (Fin (m+1) → Vector (n+2)) → ℝ)
    (hf : ∀ n, Measurable (f n))
    (hfb : ∀ n σ, |f n σ| ≤ 1) :
    Tendsto (fun n : ℕ => physicalCovarianceGGDefect μ β n m (f n))
      atTop (𝓝 0) :=
  physical_covariance_gg_tendsto_of_pressure_and_thermal μ hβ p hp hpdiff
    (physical_normalized_thermal_energy_fluctuation_tendsto_zero μ β p hp hpdiff)
    m f hf hfb

theorem physical_full_array_gg_borel
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β) (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (p t)))
    (hpdiff : DifferentiableAt ℝ p β)
    (m : ℕ) (f : FullOverlapCoordinates (m+1) → ℝ)
    (hf : Measurable f) (hfb : ∀ c, |f c| ≤ 1)
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β) :
    fullArrayCovarianceGGDefect μ m f x = 0 :=
  fullArrayCovarianceGGDefect_eq_zero_borel_of_sublinear_budget
    μ hβ m f hf hfb
    (physical_total_energy_budget_tendsto_zero μ β p hp hpdiff) hx

theorem physical_directing_covariance_gg
    {Ξ H : Type*} [MeasurableSpace Ξ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β) (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (p t)))
    (hpdiff : DifferentiableAt ℝ p β)
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β)
    (R : RandomDirectingData Ξ H)
    (hrep : ∀ m, x m = directingDataFullLaw R m)
    (hball : ∀ᵐ ω ∂(R.disorderLaw),
      ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ≤ 1) :
    CovarianceGG R.disorderLaw R.directingKernel μ.xi :=
  covarianceGG_of_physical_sublinear_budget μ hβ
    (physical_total_energy_budget_tendsto_zero μ β p hp hpdiff)
    hx R hrep hball

end SlowEquilibration.PureCapturePhysicalPanchenkoUnconditionalEnergy
