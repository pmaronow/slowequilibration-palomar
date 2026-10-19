-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalResidualTemperatureLimits
public import SlowEquilibration.SphericalConcentration

@[expose] public section

/-! # Actual corrected residual log-partition lower tails

The actual quenched-pressure limit and genuine Gaussian concentration yield an
exponentially small lower-tail probability under the literal tensor disorder
law. The variance scale is exactly β²(N+j)ξ(1), including static endpoints.
-/

namespace SlowEquilibration
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

namespace SphericalModel

theorem dimensionCorrectedTemperature_pos {β : ℝ} (hβ : 0 < β) (j : ℕ)
    {N : ℕ} (hN : 1 ≤ N) : 0 < dimensionCorrectedTemperature β j N := by
  unfold dimensionCorrectedTemperature
  apply mul_pos hβ
  apply Real.sqrt_pos.mpr
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact div_pos (by exact_mod_cast (show 0 < N+j by omega)) hNr

/-- The physical variance correction is exact, rather than asymptotic. -/
theorem dimensionCorrectedTemperature_sq_mul_dimension (β : ℝ) (j : ℕ)
    {N : ℕ} (hN : 1 ≤ N) :
    (dimensionCorrectedTemperature β j N)^2*(N : ℝ) = β^2*((N+j : ℕ) : ℝ) := by
  unfold dimensionCorrectedTemperature
  rw [mul_pow,Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- A genuine per-ambient pressure limit gives an actual exponential
log-partition lower tail at the dimension-corrected temperatures. -/
theorem dimensionCorrected_logPartition_lower_tail_of_pressure_limit
    (μ : FiniteMixture) {β F ε : ℝ} (hβ : 0 < β) (j : ℕ) (hε : 0 < ε)
    (hmean : Tendsto (fun N : ℕ => ((N : ℝ)/((N+j : ℕ) : ℝ))*
      quenchedPressure N μ (dimensionCorrectedTemperature β j N)) atTop (𝓝 F)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      disorderLaw N μ.maxDegree {J | Real.log
        (mixturePartition μ (dimensionCorrectedTemperature β j N) J)/((N+j : ℕ) : ℝ)
          < F-ε} ≤ ENNReal.ofReal (2*Real.exp (-c*((N+j : ℕ) : ℝ))) := by
  let c : ℝ := ε^2/(8*β^2*μ.xi 1)
  have hc : 0 < c := by dsimp [c]; positivity [μ.xi_pos (show (0 : ℝ) < 1 by norm_num)]
  refine ⟨c,hc,?_⟩
  have hm : ∀ᶠ N : ℕ in atTop, F-ε/2 < ((N : ℝ)/((N+j : ℕ) : ℝ))*
      quenchedPressure N μ (dimensionCorrectedTemperature β j N) :=
    hmean.eventually (Ioi_mem_nhds (by linarith))
  filter_upwards [hm,eventually_ge_atTop 1] with N hm hN
  let b := dimensionCorrectedTemperature β j N
  let M : ℝ := ((N+j : ℕ) : ℝ)
  have hM : 0 < M := by dsimp [M]; exact_mod_cast (show 0 < N+j by omega)
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmeanEq : ((N : ℝ)/M)*quenchedPressure N μ b =
      (∫ K,Real.log (mixturePartition μ b K) ∂disorderLaw N μ.maxDegree)/M := by
    unfold quenchedPressure
    field_simp
  change F-ε/2 < ((N : ℝ)/M)*quenchedPressure N μ b at hm
  rw [hmeanEq] at hm
  have hvariance := dimensionCorrectedTemperature_sq_mul_dimension β j hN
  have hb : 0 < b := dimensionCorrectedTemperature_pos hβ j hN
  have hs : 0 < (ε/2)*M := mul_pos (half_pos hε) hM
  have hconc := logPartition_concentration hN (mixtureCoefficients μ)
    (mixtureCoefficients_nonnegative μ)
    (by simpa only [covariancePolynomial_mixture] using μ.xi_pos (show (0 : ℝ)<1 by norm_num))
    hb hs
  change disorderLaw N μ.maxDegree {J | |Real.log (mixturePartition μ b J)-
      (∫ K,Real.log (mixturePartition μ b K) ∂disorderLaw N μ.maxDegree)| > (ε/2)*M} ≤ _ at hconc
  have hexponent : -((ε/2)*M)^2/(2*b^2*(N : ℝ)*covariancePolynomial (mixtureCoefficients μ) 1) =
      -c*M := by
    rw [covariancePolynomial_mixture]
    have hvariance' : b^2*(N : ℝ)=β^2*M := hvariance
    have hden : 2*b^2*(N : ℝ)*μ.xi 1 = 2*β^2*M*μ.xi 1 := by
      linear_combination 2*μ.xi 1*hvariance'
    rw [hden]
    dsimp [c]
    have hβne : β ≠ 0 := hβ.ne'
    have hξne : μ.xi 1 ≠ 0 := (μ.xi_pos (show (0 : ℝ)<1 by norm_num)).ne'
    have hMne : M ≠ 0 := hM.ne'
    field_simp
    ring
  rw [hexponent] at hconc
  apply (measure_mono ?_).trans hconc
  intro J hJ
  change Real.log (mixturePartition μ b J)/M < F-ε at hJ
  have hlow := (div_lt_iff₀ hM).mp hJ
  have hhigh := (lt_div_iff₀ hM).mp hm
  exact (show (ε/2)*M < -(Real.log (mixturePartition μ b J)-
    (∫ K,Real.log (mixturePartition μ b K) ∂disorderLaw N μ.maxDegree)) by
      nlinarith [mul_pos hε hM]).trans_le (neg_le_abs _)

end SphericalModel

namespace FiniteMixture
open SphericalModel

/-- Literal physical qStar residual lower tails, with the actual static
certificate and fixed endpoint mean limit supplied by proved theorems. -/
theorem qStar_taylorResidual_corrected_logPartition_lower_tail
    (μ : FiniteMixture) (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi)
    {β ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi < β) (j : ℕ) (hε : 0 < ε) :
    let q := Thresholds.qStar μ.xi β
    let ν := μ.taylorResidual (μ.qStar_solves_plateau hβ).1.1
      (sub_pos.mpr (μ.qStar_solves_plateau hβ).1.2)
    let F := (β^2*(μ.xi 1-μ.xi q)-q)/2
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      disorderLaw N ν.maxDegree {J | Real.log
        (mixturePartition ν (dimensionCorrectedTemperature β j N) J)/((N+j : ℕ) : ℝ)
          < F-ε} ≤ ENNReal.ofReal (2*Real.exp (-c*((N+j : ℕ) : ℝ))) := by
  exact dimensionCorrected_logPartition_lower_tail_of_pressure_limit _
    (μ.dynamicalThreshold_pos.trans hβ) j hε
    (μ.qStar_taylorResidual_pressure_per_ambient_tendsto hconv hβ j)

/-- Arbitrary original parity is covered when minimum degree three proves
the true nonnegative residual range. -/
theorem qStar_taylorResidual_corrected_logPartition_lower_tail_of_minDegree
    (μ : FiniteMixture) (hd : 3 ≤ μ.minDegree)
    {β ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi < β) (j : ℕ) (hε : 0 < ε) :
    let q := Thresholds.qStar μ.xi β
    let ν := μ.taylorResidual (μ.qStar_solves_plateau hβ).1.1
      (sub_pos.mpr (μ.qStar_solves_plateau hβ).1.2)
    let F := (β^2*(μ.xi 1-μ.xi q)-q)/2
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      disorderLaw N ν.maxDegree {J | Real.log
        (mixturePartition ν (dimensionCorrectedTemperature β j N) J)/((N+j : ℕ) : ℝ)
          < F-ε} ≤ ENNReal.ofReal (2*Real.exp (-c*((N+j : ℕ) : ℝ))) := by
  exact dimensionCorrected_logPartition_lower_tail_of_pressure_limit _
    (μ.dynamicalThreshold_pos.trans hβ) j hε
    (μ.qStar_taylorResidual_pressure_per_ambient_tendsto_of_minDegree hd hβ j)

end FiniteMixture
end
end SlowEquilibration
