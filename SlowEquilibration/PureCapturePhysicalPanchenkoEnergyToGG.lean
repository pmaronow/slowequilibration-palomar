-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPanchenkoQuenchedEnergy
public import SlowEquilibration.PureCapturePhysicalFullArrayGGWeakLimit

/-! The original physical disorder-energy theorem is combined with the
thermal term in exactly the normalization needed for finite and limiting
Ghirlanda–Guerra covariance identities. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalPanchenkoEnergyToGG

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalShellGG
open PureCapturePhysicalPanchenkoQuenchedEnergy
open PureCapturePhysicalAsymptoticGGFromBudget
open PureCapturePhysicalFullArrayGGWeakLimit
open PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalFullArrayGGTransfer
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalFiniteGGDefinitions
open GaussianPerturbationDeviation GaussianPerturbationIntegrated
open scoped Topology
set_option autoImplicit false

theorem physical_total_energy_budget_tendsto_zero_of_thermal
    (μ : FiniteMixture) (β : ℝ) (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (p t)))
    (hpdiff : DifferentiableAt ℝ p β)
    (hthermal : Tendsto (fun n : ℕ =>
      meanThermalDeviation (shellLaw (n+2))
        (shellLinear (mixtureCoefficients μ)) (fun _ => true) β /
          ((n+2 : ℕ) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (meanThermalDeviation (shellLaw (n+2))
          (shellLinear (mixtureCoefficients μ)) (fun _ => true) β +
        energyFluctuation (shellLaw (n+2))
          (shellLinear (mixtureCoefficients μ)) (fun _ => true) β) /
            ((n+2 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hq := physical_normalized_quenched_energy_fluctuation_tendsto_zero
    μ β p hp hpdiff
  simpa only [add_div, zero_add] using hthermal.add hq

theorem physical_covariance_gg_tendsto_of_pressure_and_thermal
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β) (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (p t)))
    (hpdiff : DifferentiableAt ℝ p β)
    (hthermal : Tendsto (fun n : ℕ =>
      meanThermalDeviation (shellLaw (n+2))
        (shellLinear (mixtureCoefficients μ)) (fun _ => true) β /
          ((n+2 : ℕ) : ℝ)) atTop (𝓝 0))
    (m : ℕ)
    (f : (n : ℕ) → (Fin (m+1) → Vector (n+2)) → ℝ)
    (hf : ∀ n, Measurable (f n))
    (hfb : ∀ n σ, |f n σ| ≤ 1) :
    Tendsto (fun n : ℕ => physicalCovarianceGGDefect μ β n m (f n))
      atTop (𝓝 0) :=
  physicalCovarianceGGDefect_tendsto_zero_of_sublinear_budget μ hβ m f hf hfb
    (physical_total_energy_budget_tendsto_zero_of_thermal μ β p hp hpdiff hthermal)

theorem physical_full_array_gg_of_pressure_and_thermal
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β) (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (p t)))
    (hpdiff : DifferentiableAt ℝ p β)
    (hthermal : Tendsto (fun n : ℕ =>
      meanThermalDeviation (shellLaw (n+2))
        (shellLinear (mixtureCoefficients μ)) (fun _ => true) β /
          ((n+2 : ℕ) : ℝ)) atTop (𝓝 0))
    (m : ℕ) (g : FullOverlapCoordinates (m+1) → ℝ)
    (hg : Continuous g) (hgb : ∀ c, |g c| ≤ 1)
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β) :
    fullArrayCovarianceGGDefect μ m g x = 0 :=
  fullArrayCovarianceGGDefect_eq_zero_of_sublinear_budget μ hβ m g hg hgb
    (physical_total_energy_budget_tendsto_zero_of_thermal μ β p hp hpdiff hthermal)
    hx

end SlowEquilibration.PureCapturePhysicalPanchenkoEnergyToGG
