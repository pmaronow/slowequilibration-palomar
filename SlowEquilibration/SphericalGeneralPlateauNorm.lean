-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeWeightedMeanUpper
public import SlowEquilibration.SphericalPlateauAmplitudeLatitudeLocalization
public import SlowEquilibration.SphericalPlateauAmplitudeUniformPhysicalMomentLimit
public import SlowEquilibration.SphericalGeneralPlateauFromPlanted

@[expose] public section

/-! # Genuine source weighted-mean norm convergence for every finite mixture

The actual amplitude bank pressure, sampled coarea bounds, canonical core,
latitude localization, finite Gaussian IBP and exact planting transport
supply the planted squared norm error. Genuine all-finite likelihood
contiguity transfers it to the original disorder.
-/
namespace SlowEquilibration.SphericalWeightedReplicaPlateau
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalBarycenter SphericalPlateauAmplitudeModel
open SphericalMemoryAssembly VaryingProbability
open scoped Topology
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem general_sourceNormError_planted_tendsto (μ : FiniteMixture)
    {β δ q₁ q₂ : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi) (hc : IsAdmissibleCollar μ β q₁ q₂)
    (hδ : 0≤δ) :
    Tendsto (fun N => ∫ z : Disorder N μ.maxDegree × Vector N,
      sourceNormError μ β (plantedCoreCost μ β) δ q₁ q₂ (Thresholds.qStar μ.xi β) z
        ∂plantedLaw (mixtureCoefficients μ) β) atTop (𝓝 (0:ℝ)) := by
  obtain ⟨p,hp⟩ := μ.support_nonempty
  let p₀ : Degree μ.maxDegree := ⟨⟨p,Nat.lt_succ_of_le (μ.degree_bounds hp).2⟩,μ.degree_ge_two hp⟩
  have hp₀ : 0 < mixtureCoefficients μ p₀ := μ.coeff_pos hp
  obtain ⟨ρ,hqρ,hρ,_hρ0,hUpper⟩ := exists_amplitudeExpectedPressure_uniform_envelope_upper μ hβ hβs hc hδ p₀
  apply general_sourceNormError_planted_tendsto_of_uniform_upper_localization μ hβ hβs hc hδ p₀ hp₀ hqρ hρ
  · intro k τ hτ ε hε
    filter_upwards [hUpper ε hε] with n hn
    intro x hx
    exact hn k τ ⟨hτ.1.le,hτ.2.le⟩ x hx
  · exact general_amplitudeLatitudeL1_eventually_le μ hβ hβs hc hδ p₀

/-- Source prop:pl-norm for every finite mixture, including quadratic and
odd terms: the actual Gibbs-reference fluctuation converges in probability. -/
theorem general_sourceNormFluctuation_inProbability (μ : FiniteMixture)
    {β δ q₁ q₂ : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi) (hc : IsAdmissibleCollar μ β q₁ q₂)
    (hδ : 0≤δ) :
    InProbability (fun N => disorderLaw N μ.maxDegree)
      (fun N => sourceNormFluctuation (N := N) μ β (plantedCoreCost μ β) δ q₁ q₂
        (Thresholds.qStar μ.xi β)) 0 := by
  have hq := (μ.qStar_solves_plateau hβ).1
  exact sourceNormFluctuation_inProbability_of_planted μ β (plantedCoreCost μ β) δ q₁ q₂
    ⟨hq.1.le,hq.2.le⟩ (general_likelihoodLowerTailTight μ (μ.dynamicalThreshold_pos.trans hβ) hβs)
    (general_sourceNormError_planted_tendsto μ hβ hβs hc hδ)

/-- The actual weighted two-replica mean converges to qStar under the
original disorder, with every thermodynamic and likelihood input proved. -/
theorem general_sourceWeightedReplicaMoment_inProbability (μ : FiniteMixture)
    {β δ q₁ q₂ : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi) (hc : IsAdmissibleCollar μ β q₁ q₂)
    (hδ : 0≤δ) :
    InProbability (fun N => disorderLaw N μ.maxDegree)
      (fun N D => sourceWeightedReplicaMoment (N := N) μ β D (plantedCoreCost μ β) δ q₁ q₂)
      (Thresholds.qStar μ.xi β) :=
  general_sourceWeightedReplicaMoment_of_planted μ hβ hβs (plantedCoreCost μ β) δ q₁ q₂
    (general_sourceNormError_planted_tendsto μ hβ hβs hc hδ)

end
end SlowEquilibration.SphericalWeightedReplicaPlateau
