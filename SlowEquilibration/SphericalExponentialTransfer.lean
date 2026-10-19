-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalAnnealedConcentration

/-! The manuscript's explicit exponential planted-to-Gibbs-reference rate,
derived from the actual finite-volume pressure gap. The separate RS pressure
limit must still be proved before applying this to every beta below beta_s. -/

@[expose] public section
namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def plantedTransferRate (μ : FiniteMixture) (β c : ℝ) : ℝ :=
  min (c/2) (c^2/(32*β^2*μ.xi 1))

theorem plantedTransferRate_pos (μ : FiniteMixture) {β c : ℝ}
    (hβ : 0 < β) (hc : 0 < c) : 0 < plantedTransferRate μ β c := by
  have hx : 0 < μ.xi 1 := μ.xi_pos (by norm_num)
  unfold plantedTransferRate
  positivity

theorem exponential_planted_transfer_of_pressure_gap {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) {β c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (hgap : |quenchedPressure N μ β-β^2*μ.xi 1/2| ≤ c/4)
    {E : Set (Disorder N μ.maxDegree × Vector N)} (hE : MeasurableSet E)
    (hP : (plantedLaw (mixtureCoefficients μ) β).real E ≤ Real.exp (-c*(N : ℝ))) :
    (gibbsReferenceLaw (mixtureCoefficients μ) β).real E ≤
      3*Real.exp (-plantedTransferRate μ β c*(N : ℝ)) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have ht := gibbsReference_event_le_logPartition_split hN (mixtureCoefficients μ)
    (mixtureCoefficients_nonnegative μ) β (c*(N : ℝ)/2) hE
  have hs : {J : Disorder N μ.maxDegree |
      Real.log (partition N β (field (mixtureCoefficients μ) J)) <
        annealedExponent N (mixtureCoefficients μ) β-c*(N : ℝ)/2} ⊆
      {J | |Real.log (mixturePartition μ β J)/(N : ℝ)-β^2*μ.xi 1/2| > c/2} := by
    intro J hJ
    change Real.log (mixturePartition μ β J) <
      annealedExponent N (mixtureCoefficients μ) β-c*(N : ℝ)/2 at hJ
    unfold annealedExponent at hJ
    rw [covariancePolynomial_mixture] at hJ
    have hr : Real.log (mixturePartition μ β J)/(N : ℝ) < β^2*μ.xi 1/2-c/2 := by
      apply (div_lt_iff₀ hNr).mpr
      nlinarith
    change c/2 < |Real.log (mixturePartition μ β J)/(N : ℝ)-β^2*μ.xi 1/2|
    nlinarith [neg_le_abs (Real.log (mixturePartition μ β J)/(N : ℝ)-β^2*μ.xi 1/2)]
  have hconc := annealed_logPartition_concentration_of_pressure_gap hN μ hβ
    (show 0 < c/2 by positivity) (by convert hgap using 1 <;> ring)
  have he : -((c/2)^2*(N : ℝ))/(8*β^2*μ.xi 1) =
      -(c^2/(32*β^2*μ.xi 1))*(N : ℝ) := by ring
  rw [he] at hconc
  have hbad := (measureReal_mono hs).trans hconc
  have hgood := mul_le_mul_of_nonneg_left hP (Real.exp_pos (c*(N : ℝ)/2)).le
  have heg : Real.exp (c*(N : ℝ)/2)*Real.exp (-c*(N : ℝ)) =
      Real.exp (-(c/2)*(N : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heg] at hgood
  have hb : Real.exp (-(c^2/(32*β^2*μ.xi 1))*(N : ℝ)) ≤
      Real.exp (-plantedTransferRate μ β c*(N : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hmin := min_le_right (c/2) (c^2/(32*β^2*μ.xi 1))
    change -(c^2/(32*β^2*μ.xi 1))*(N : ℝ) ≤
      -(min (c/2) (c^2/(32*β^2*μ.xi 1)))*(N : ℝ)
    nlinarith
  have hg : Real.exp (-(c/2)*(N : ℝ)) ≤
      Real.exp (-plantedTransferRate μ β c*(N : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hmin := min_le_left (c/2) (c^2/(32*β^2*μ.xi 1))
    change -(c/2)*(N : ℝ) ≤ -(min (c/2) (c^2/(32*β^2*μ.xi 1)))*(N : ℝ)
    nlinarith
  linarith

theorem exponential_planted_transfer_eventually_of_pressure_limit
    (μ : FiniteMixture) {β c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (hlim : Tendsto (fun N : ℕ => quenchedPressure N μ β) atTop (𝓝 (β^2*μ.xi 1/2)))
    (E : (N : ℕ) → Set (Disorder N μ.maxDegree × Vector N))
    (hE : ∀ N, MeasurableSet (E N))
    (hP : ∀ᶠ N : ℕ in atTop,
      (plantedLaw (mixtureCoefficients μ) β).real (E N) ≤ Real.exp (-c*(N : ℝ))) :
    ∀ᶠ N : ℕ in atTop,
      (gibbsReferenceLaw (mixtureCoefficients μ) β).real (E N) ≤
        3*Real.exp (-plantedTransferRate μ β c*(N : ℝ)) := by
  have hg := (Metric.tendsto_nhds.mp hlim) (c/4) (by positivity)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hg, hP] with N hN hgap hPN
  apply exponential_planted_transfer_of_pressure_gap hN μ hβ hc _ (hE N) hPN
  simpa only [Real.dist_eq] using hgap.le

end
end SlowEquilibration.SphericalModel
