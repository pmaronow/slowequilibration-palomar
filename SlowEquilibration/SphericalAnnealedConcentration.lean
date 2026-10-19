-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLikelihoodTransfer

/-! Concentration at the actual annealed value once the physical mean
pressure is close to that value. The replica-symmetric pressure limit is not
asserted here and remains a separate theorem to be proved. -/

@[expose] public section
namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem annealed_logPartition_concentration_of_pressure_gap {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε)
    (hgap : |quenchedPressure N μ β - β^2*μ.xi 1/2| ≤ ε/2) :
    (disorderLaw N μ.maxDegree).real
      {J | |Real.log (mixturePartition μ β J)/(N : ℝ)-β^2*μ.xi 1/2| > ε} ≤
        2*Real.exp (-(ε^2*(N : ℝ))/(8*β^2*μ.xi 1)) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hxi : 0 < μ.xi 1 := μ.xi_pos (by norm_num)
  let A := β^2*μ.xi 1/2
  let M := ∫ J : Disorder N μ.maxDegree, Real.log (mixturePartition μ β J)
    ∂disorderLaw N μ.maxDegree
  have hgap' : |M/(N : ℝ)-A| ≤ ε/2 := hgap
  have hsubset : {J : Disorder N μ.maxDegree |
      |Real.log (mixturePartition μ β J)/(N : ℝ)-A| > ε} ⊆
      {J | |Real.log (mixturePartition μ β J)-M| > ε*(N : ℝ)/2} := by
    intro J hJ
    have htriangle := abs_sub_le (Real.log (mixturePartition μ β J)/(N : ℝ)) (M/(N : ℝ)) A
    have hden : |Real.log (mixturePartition μ β J)/(N : ℝ)-M/(N : ℝ)| =
        |Real.log (mixturePartition μ β J)-M|/(N : ℝ) := by
      rw [← sub_div, abs_div, abs_of_pos hNr]
    rw [hden] at htriangle
    have hh : ε/2 < |Real.log (mixturePartition μ β J)-M|/(N : ℝ) := by
      change ε < |Real.log (mixturePartition μ β J)/(N : ℝ)-A| at hJ
      linarith
    have hd := (lt_div_iff₀ hNr).mp hh
    change ε*(N : ℝ)/2 < |Real.log (mixturePartition μ β J)-M|
    linarith
  have hcov : 0 < covariancePolynomial (mixtureCoefficients μ) 1 := by
    rw [covariancePolynomial_mixture]
    exact hxi
  have ht := logPartition_concentration hN (mixtureCoefficients μ)
    (mixtureCoefficients_nonnegative μ) hcov hβ (show 0 < ε*(N : ℝ)/2 by positivity)
  have he : -(ε*(N : ℝ)/2)^2/(2*β^2*(N : ℝ)*μ.xi 1) =
      -(ε^2*(N : ℝ))/(8*β^2*μ.xi 1) := by
    field_simp
    <;> ring
  rw [covariancePolynomial_mixture, he] at ht
  have htr := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
  rw [ENNReal.toReal_ofReal (by positivity)] at htr
  exact (measureReal_mono hsubset).trans htr

theorem annealed_logPartition_concentration_eventually_of_pressure_limit
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    (hlim : Tendsto (fun N : ℕ => quenchedPressure N μ β) atTop (𝓝 (β^2*μ.xi 1/2)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (disorderLaw N μ.maxDegree).real
        {J | |Real.log (mixturePartition μ β J)/(N : ℝ)-β^2*μ.xi 1/2| > ε} ≤
          2*Real.exp (-(ε^2*(N : ℝ))/(8*β^2*μ.xi 1)) := by
  have hc := (Metric.tendsto_nhds.mp hlim) (ε/2) (by positivity)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hc] with N hN hg
  apply annealed_logPartition_concentration_of_pressure_gap hN μ hβ hε
  simpa only [Real.dist_eq] using hg.le

end
end SlowEquilibration.SphericalModel
