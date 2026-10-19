-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPanchenkoArbitraryTemperature
public import SlowEquilibration.NatLogWindowScales

/-! Vanishing of the unperturbed quenched Gibbs-energy fluctuation from a
pointwise physical pressure limit and differentiability at the selected
inverse temperature. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalPanchenkoQuenchedEnergy

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalShellGG
open PureCapturePhysicalPanchenkoConvexSpread
open PureCapturePhysicalPanchenkoPressureTransport
open PureCapturePhysicalPanchenkoArbitraryTemperature
open GaussianPerturbationIntegrated GaussianPerturbationSelfAveraging
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

theorem physical_feature_bound_over_dimension_tendsto_zero (μ : FiniteMixture) :
    Tendsto (fun n : ℕ =>
      Real.sqrt (((n+2 : ℕ) : ℝ)*μ.xi 1)/((n+2 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have h := NatLogWindowScales.inverse_sqrt_dimension_tendsto_zero.const_mul
    (Real.sqrt (μ.xi 1))
  have heq (n : ℕ) :
      Real.sqrt (((n+2 : ℕ) : ℝ)*μ.xi 1)/((n+2 : ℕ) : ℝ) =
      Real.sqrt (μ.xi 1)*(1/Real.sqrt ((n+2 : ℕ) : ℝ)) := by
    have hN : (0 : ℝ) < ((n+2 : ℕ) : ℝ) := by positivity
    have hs : (Real.sqrt ((n+2 : ℕ) : ℝ))^2 = ((n+2 : ℕ) : ℝ) :=
      Real.sq_sqrt hN.le
    have hr : Real.sqrt ((n+2 : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
    rw [Real.sqrt_mul hN.le]
    calc
      Real.sqrt ((n+2 : ℕ) : ℝ) * Real.sqrt (μ.xi 1) /
          ((n+2 : ℕ) : ℝ) =
        Real.sqrt ((n+2 : ℕ) : ℝ) * Real.sqrt (μ.xi 1) /
          (Real.sqrt ((n+2 : ℕ) : ℝ))^2 := by rw [hs]
      _ = _ := by field_simp
  simpa only [heq, mul_zero] using h

/-- Finite-volume Panchenko comparison for the *unperturbed* original
spherical model, at any inverse temperature. The right side uses only the
true physical pressure and its Gaussian feature scale. -/
theorem physical_normalized_quenched_energy_fluctuation_le_spread
    (μ : FiniteMixture) (β : ℝ) (n : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    energyFluctuation (shellLaw (n+2))
      (shellLinear (mixtureCoefficients μ)) (fun _ => true) β /
        ((n+2 : ℕ) : ℝ) ≤
      deriv (quenchedPressure (n+2) μ) (β+δ) -
        deriv (quenchedPressure (n+2) μ) (β-δ) +
      (2*Real.exp (1/2)*
        Real.sqrt (((n+2 : ℕ) : ℝ)*μ.xi 1)*(5+3*|β|) /
          ((n+2 : ℕ) : ℝ))/δ := by
  let N := n+2
  let L := shellLinear (N := N) (mixtureCoefficients μ)
  let K := Real.sqrt ((N : ℝ)*μ.xi 1)
  let C := 2*Real.exp (1/2)*K
  letI : IsProbabilityMeasure (shellLaw N) := shellLaw_probability (by omega)
  have hN : (0 : ℝ) < N := by positivity
  have hK : 0 < K := Real.sqrt_pos.mpr
    (mul_pos hN (μ.xi_pos (by norm_num)))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : ∀ᵐ x ∂shellLaw N, ‖L x‖ ≤ K := by
    apply Filter.Eventually.of_forall
    intro x
    simpa only [L, K, covariancePolynomial_mixture] using
      shellLinear_bound (by omega : 1 ≤ N) (mixtureCoefficients μ)
        (mixtureCoefficients_nonnegative μ) x
  have hs : (1+|β+δ|)+(1+|β-δ|)+(1+|β|) ≤ 5+3*|β| := by
    have hp := abs_add_le β δ
    have hm := abs_add_le β (-δ)
    rw [abs_of_pos hδ] at hp
    simp only [← sub_eq_add_neg, abs_neg, abs_of_pos hδ] at hm
    linarith
  have hraw := integral_score_fluctuation_le_any
    (shellLaw N) L (shellLinear_measurable (mixtureCoefficients μ))
    hK hb (fun _ => true) β hδ
  have hraw' : energyFluctuation (shellLaw N) L (fun _ => true) β ≤
      meanScore (shellLaw N) L (fun _ => true) (β+δ)-
        meanScore (shellLaw N) L (fun _ => true) (β-δ)+
        C*(5+3*|β|)/δ := by
    exact hraw.trans (add_le_add le_rfl
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hC) hδ.le))
  have hp := meanScore_full_div_eq_deriv_quenchedPressure
    (N := N) (by omega) μ (β+δ)
  have hm := meanScore_full_div_eq_deriv_quenchedPressure
    (N := N) (by omega) μ (β-δ)
  change energyFluctuation (shellLaw N) L (fun _ => true) β / (N : ℝ) ≤ _
  calc
    _ ≤ (meanScore (shellLaw N) L (fun _ => true) (β+δ)-
          meanScore (shellLaw N) L (fun _ => true) (β-δ)+
          C*(5+3*|β|)/δ)/(N : ℝ) :=
      div_le_div_of_nonneg_right hraw' hN.le
    _ = meanScore (shellLaw N) L (fun _ => true) (β+δ)/(N : ℝ)-
          meanScore (shellLaw N) L (fun _ => true) (β-δ)/(N : ℝ)+
          (C*(5+3*|β|)/(N : ℝ))/δ := by field_simp
    _ = _ := by rw [hp, hm]

/-- The original, unperturbed Gibbs-energy disorder fluctuation is
sublinear in dimension at every differentiability point of a pointwise
physical pressure limit. -/
theorem physical_normalized_quenched_energy_fluctuation_tendsto_zero
    (μ : FiniteMixture) (β : ℝ) (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (p t)))
    (hpdiff : DifferentiableAt ℝ p β) :
    Tendsto (fun n : ℕ =>
      energyFluctuation (shellLaw (n+2))
        (shellLinear (mixtureCoefficients μ)) (fun _ => true) β /
          ((n+2 : ℕ) : ℝ)) atTop (𝓝 0) := by
  let c : ℕ → ℝ := fun n =>
    (2*Real.exp (1/2)*(5+3*|β|))*
      (Real.sqrt (((n+2 : ℕ) : ℝ)*μ.xi 1)/((n+2 : ℕ) : ℝ))
  have hc : Tendsto c atTop (𝓝 0) := by
    simpa only [c, mul_zero] using
      (physical_feature_bound_over_dimension_tendsto_zero μ).const_mul
        (2*Real.exp (1/2)*(5+3*|β|))
  have herr (n : ℕ) :
      0 ≤ energyFluctuation (shellLaw (n+2))
        (shellLinear (mixtureCoefficients μ)) (fun _ => true) β /
          ((n+2 : ℕ) : ℝ) := by
    unfold energyFluctuation
    exact div_nonneg (integral_nonneg fun _ => abs_nonneg _)
      (by positivity)
  apply error_tendsto_zero_of_convex_spread
    (fun n t => quenchedPressure (n+2) μ t) p β
    (fun n => energyFluctuation (shellLaw (n+2))
      (shellLinear (mixtureCoefficients μ)) (fun _ => true) β /
        ((n+2 : ℕ) : ℝ)) c
  · exact herr
  · intro n
    exact PureCapturePhysicalPressureConvex.quenchedPressure_convexOn μ (by omega)
  · intro n t
    exact quenchedPressure_differentiable (by omega) μ t
  · exact hp
  · exact hpdiff
  · exact hc
  · intro n δ hδ hδ1
    have h := physical_normalized_quenched_energy_fluctuation_le_spread
      μ β n hδ hδ1
    dsimp only [c]
    convert h using 1
    all_goals ring

end SlowEquilibration.PureCapturePhysicalPanchenkoQuenchedEnergy
