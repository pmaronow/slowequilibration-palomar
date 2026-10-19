-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.PureCapturePhysicalPanchenkoThermalPhysical
public import SlowEquilibration.NatLogWindowScales

/-! Fixed-temperature thermal self-averaging for the original spherical
finite-mixture field. The only asymptotic input is the pointwise physical
pressure limit at a differentiability point. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalPanchenkoThermalLimit
open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalShellGG
open PureCapturePhysicalPanchenkoThermalPhysical
open PureCapturePhysicalPanchenkoPressureTransport
open PureCapturePhysicalPanchenkoSymmetricSpread
open GaussianPerturbationDeviation GaussianPerturbationParameter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

/-- Exact finite-volume thermal estimate from the true physical pressure. -/
theorem physical_normalized_thermal_energy_fluctuation_le_symmetric_spread
    (μ : FiniteMixture) (β : ℝ) (n : ℕ) {δ : ℝ}
    (hδ : 0 < δ) :
    meanThermalDeviation (shellLaw (n+2))
      (shellLinear (mixtureCoefficients μ)) (fun _ => true) β /
        ((n+2 : ℕ) : ℝ) ≤
      symmetricSecantSpread (quenchedPressure (n+2) μ) β δ +
        (Real.log 2/((n+2 : ℕ) : ℝ))/δ := by
  let N := n+2
  let L := shellLinear (N := N) (mixtureCoefficients μ)
  let K := Real.sqrt ((N : ℝ)*μ.xi 1)
  letI : IsProbabilityMeasure (shellLaw N) := shellLaw_probability (by omega)
  have hN : 0 < (N : ℝ) := by positivity
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hb : ∀ᵐ x ∂shellLaw N, ‖L x‖ ≤ K := by
    apply Filter.Eventually.of_forall
    intro x
    simpa only [L, K, covariancePolynomial_mixture] using
      shellLinear_bound (by omega : 1 ≤ N) (mixtureCoefficients μ)
        (mixtureCoefficients_nonnegative μ) x
  have hraw := full_meanThermalDeviation_le_parameterMean_second_difference
    (shellLaw N) L (shellLinear_measurable (mixtureCoefficients μ)) hK hb β δ
  have hmean (t : ℝ) :
      parameterMean (shellLaw N) L (fun _ => true) t =
        (N : ℝ)*quenchedPressure N μ t := by
    have hp := parameterMean_full_div_eq_quenchedPressure
      (N := N) (by omega) μ t
    simpa only [L, mul_comm] using (div_eq_iff hN.ne').mp hp
  change δ * meanThermalDeviation (shellLaw N) L (fun _ => true) β ≤ _ at hraw
  rw [hmean (β+δ), hmean (β-δ), hmean β] at hraw
  change meanThermalDeviation (shellLaw N) L (fun _ => true) β / (N : ℝ) ≤ _
  calc
    _ = (δ*meanThermalDeviation (shellLaw N) L (fun _ => true) β)/
          (δ*(N : ℝ)) := by field_simp
    _ ≤ (Real.log 2+(N : ℝ)*quenchedPressure N μ (β+δ)+
          (N : ℝ)*quenchedPressure N μ (β-δ)-
          2*((N : ℝ)*quenchedPressure N μ β))/(δ*(N : ℝ)) :=
      div_le_div_of_nonneg_right hraw (by positivity)
    _ = symmetricSecantSpread (quenchedPressure N μ) β δ +
          (Real.log 2/(N : ℝ))/δ := by
      unfold symmetricSecantSpread
      field_simp
      ring

/-- The normalized absolute thermal energy deviation vanishes at each
differentiability point of a pointwise physical pressure limit. -/
theorem physical_normalized_thermal_energy_fluctuation_tendsto_zero
    (μ : FiniteMixture) (β : ℝ) (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (p t)))
    (hpdiff : DifferentiableAt ℝ p β) :
    Tendsto (fun n : ℕ =>
      meanThermalDeviation (shellLaw (n+2))
        (shellLinear (mixtureCoefficients μ)) (fun _ => true) β /
          ((n+2 : ℕ) : ℝ)) atTop (𝓝 0) := by
  let concentration : ℕ → ℝ := fun n => Real.log 2/((n+2 : ℕ) : ℝ)
  have hc : Tendsto concentration atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ => 1/((n+2 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [one_div, Function.comp_def] using
        tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
    simpa only [concentration, div_eq_mul_inv, one_mul, mul_zero] using
      hbase.const_mul (Real.log 2)
  have herr (n : ℕ) :
      0 ≤ meanThermalDeviation (shellLaw (n+2))
        (shellLinear (mixtureCoefficients μ)) (fun _ => true) β /
          ((n+2 : ℕ) : ℝ) := by
    unfold meanThermalDeviation thermalDeviation
    exact div_nonneg (integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _)
      (by positivity)
  apply error_tendsto_zero_of_symmetric_spread
    (fun n t => quenchedPressure (n+2) μ t) p β
    (fun n => meanThermalDeviation (shellLaw (n+2))
      (shellLinear (mixtureCoefficients μ)) (fun _ => true) β /
        ((n+2 : ℕ) : ℝ)) concentration
  · exact herr
  · exact hp
  · exact hpdiff
  · exact hc
  · intro n δ hδ _
    exact physical_normalized_thermal_energy_fluctuation_le_symmetric_spread μ β n hδ

end SlowEquilibration.PureCapturePhysicalPanchenkoThermalLimit
