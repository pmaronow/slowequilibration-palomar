-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiBound
public import SlowEquilibration.SphericalBaseGibbsPartitionFamily

/-! The lower pressure deviation used in the proof of `prop:pc-replica-means`
in manuscript section `09-purecover`: convergence of the physical quenched
pressure and Gaussian concentration make every fixed lower deviation vanish. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.PhysicalPressureLowerDeviation

open Filter MeasureTheory SphericalModel
open scoped Topology

set_option autoImplicit false

/-- The physical lower pressure deviation is a measurable disorder event,
including the real-division convention at dimension zero. -/
theorem pressure_lower_deviation_measurable (μ : FiniteMixture) (β F t : ℝ) (N : ℕ) :
    MeasurableSet {J : Disorder N μ.maxDegree |
      Real.log (mixturePartition μ β J) / (N : ℝ) < F - t} := by
  by_cases hN : N = 0
  · simp only [hN, Nat.cast_zero, div_zero]
    exact measurableSet_lt measurable_const measurable_const
  · exact measurableSet_lt
      (((mixturePartition_continuous (by omega) μ β).measurable.log).div_const _)
      measurable_const

/-- Exponential lower deviations of the physical pressure, as used in source
`prop:pc-replica-means`. -/
theorem pressure_lower_deviation_exponential (μ : FiniteMixture) {β F : ℝ} (hβ : 0 < β)
    (hlim : Tendsto (fun N : ℕ => quenchedPressure N μ β) atTop (𝓝 F))
    {t : ℝ} (ht : 0 < t) :
    ∀ᶠ N : ℕ in atTop,
      (disorderLaw N μ.maxDegree).real
        {J | Real.log (mixturePartition μ β J) / (N : ℝ) < F - t} ≤
          2 * Real.exp (-(t ^ 2 / (8 * β ^ 2 * μ.xi 1)) * (N : ℝ)) := by
  have hxi : 0 < μ.xi 1 := μ.xi_pos (by norm_num)
  let c : ℝ := t ^ 2 / (8 * β ^ 2 * μ.xi 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hmean : ∀ᶠ N : ℕ in atTop, F - t / 2 < quenchedPressure N μ β :=
    hlim.eventually_const_lt (by linarith)
  have hbound : ∀ᶠ N : ℕ in atTop,
      (disorderLaw N μ.maxDegree).real
        {J | Real.log (mixturePartition μ β J) / (N : ℝ) < F - t} ≤
          2 * Real.exp (-c * (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), hmean] with N hN hm
    have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    let M := ∫ J : Disorder N μ.maxDegree, Real.log (mixturePartition μ β J)
      ∂disorderLaw N μ.maxDegree
    have hm' : F - t / 2 < M / (N : ℝ) := hm
    have hsubset : {J : Disorder N μ.maxDegree |
        Real.log (mixturePartition μ β J) / (N : ℝ) < F - t} ⊆
        {J | |Real.log (mixturePartition μ β J) - M| > t * (N : ℝ) / 2} := by
      intro J hJ
      have hdiff : t / 2 < (M - Real.log (mixturePartition μ β J)) / (N : ℝ) := by
        rw [sub_div]
        change Real.log (mixturePartition μ β J) / (N : ℝ) < F - t at hJ
        linarith
      have hscaled := (lt_div_iff₀ hNr).mp hdiff
      have habs := neg_le_abs (Real.log (mixturePartition μ β J) - M)
      change t * (N : ℝ) / 2 < |Real.log (mixturePartition μ β J) - M|
      linarith
    have hcov : 0 < covariancePolynomial (mixtureCoefficients μ) 1 := by
      rw [covariancePolynomial_mixture]
      exact hxi
    have hcon := logPartition_concentration hN (mixtureCoefficients μ)
      (mixtureCoefficients_nonnegative μ) hcov hβ
      (show 0 < t * (N : ℝ) / 2 by positivity)
    have hexponent : -(t * (N : ℝ) / 2) ^ 2 /
        (2 * β ^ 2 * (N : ℝ) * μ.xi 1) = -c * (N : ℝ) := by
      dsimp [c]
      field_simp
      ring
    rw [covariancePolynomial_mixture, hexponent] at hcon
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcon
    rw [ENNReal.toReal_ofReal (by positivity)] at hreal
    exact (measureReal_mono hsubset).trans hreal
  simpa only [c] using hbound

/-- Source `prop:pc-replica-means`: a fixed lower deviation of the actual
physical pressure has probability tending to zero when its mean tends to `F`. -/
theorem pressure_lower_deviation_tendsto_zero (μ : FiniteMixture) {β F : ℝ} (hβ : 0 < β)
    (hlim : Tendsto (fun N : ℕ => quenchedPressure N μ β) atTop (𝓝 F))
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => (disorderLaw N μ.maxDegree).real
      {J | Real.log (mixturePartition μ β J) / (N : ℝ) < F - t}) atTop (𝓝 0) := by
  have hxi : 0 < μ.xi 1 := μ.xi_pos (by norm_num)
  let c : ℝ := t ^ 2 / (8 * β ^ 2 * μ.xi 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hbound := pressure_lower_deviation_exponential μ hβ hlim ht
  have hbound' : ∀ᶠ N : ℕ in atTop,
      (disorderLaw N μ.maxDegree).real
        {J | Real.log (mixturePartition μ β J) / (N : ℝ) < F - t} ≤
          2 * Real.exp (-c * (N : ℝ)) := by
    filter_upwards [hbound] with N hN
    simpa [c] using hN
  have hexp : Tendsto (fun N : ℕ => Real.exp (-c * (N : ℝ))) atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  have hupper : Tendsto (fun N : ℕ => 2 * Real.exp (-c * (N : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hexp.const_mul 2
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => measureReal_nonneg)) hbound' hupper

end SlowEquilibration.PhysicalPressureLowerDeviation
