-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGeneralLikelihoodContiguity
public import SlowEquilibration.SphericalGeneralPlateauAssembly
public import SlowEquilibration.SphericalWeightedReplicaTransfer
public import SlowEquilibration.SphericalWeightedReplicaProbability

@[expose] public section

/-! # Plateau assembly with actual cubic contiguity consumed internally

For every canonical finite mixture, including degree two and odd terms the sole remaining stochastic
input is the literal planted squared barycenter norm error. The actual proved
likelihood lower-tail tightness, planted-to-Gibbs transfer and five-conclusion assembly
are all proved internally. This remains an assembly reduction until the actual planted error
limit is proved from the perturbed-pressure derivatives.
-/
namespace SlowEquilibration.SphericalMemoryAssembly
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalWeightedReplicaPlateau SphericalBarycenter VaryingProbability
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual primitive planted norm error yields the original-disorder
weighted-replica moment limit; lower-tail tightness is a theorem here. -/
theorem general_sourceWeightedReplicaMoment_of_planted (μ : FiniteMixture)
    {β : ℝ} (hβd : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi) (J δ q₁ q₂ : ℝ)
    (hPlanted : Tendsto (fun N => ∫ z : Disorder N μ.maxDegree × Vector N,
      sourceNormError μ β J δ q₁ q₂ (Thresholds.qStar μ.xi β) z
        ∂plantedLaw (mixtureCoefficients μ) β) atTop (𝓝 (0:ℝ))) :
    InProbability (fun N => disorderLaw N μ.maxDegree)
      (fun N D => sourceWeightedReplicaMoment (N := N) μ β D J δ q₁ q₂)
        (Thresholds.qStar μ.xi β) := by
  have hq := (μ.qStar_solves_plateau hβd).1
  have hTight := general_likelihoodLowerTailTight μ
    (μ.dynamicalThreshold_pos.trans hβd) hβs
  exact sourceWeightedReplicaMoment_inProbability_of_fluctuation μ β J δ q₁ q₂ _
    (sourceNormFluctuation_inProbability_of_planted μ β J δ q₁ q₂ ⟨hq.1.le,hq.2.le⟩ hTight hPlanted)

/-- The exact source five-conclusion plateau assembly now consumes only the
actual planted barycenter error limit in this subclass. The three persistent
conclusions retain the exponential probability rate. -/
theorem general_main_plateau_of_planted_norm_error (μ : FiniteMixture)
    {β b : ℝ}
    (hβd : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi)
    (hb : b∈Ioo (0:ℝ) (Thresholds.qStar μ.xi β))
    (hPlanted : ∀ q₁ q₂ δ : ℝ, IsAdmissibleCollar μ β q₁ q₂ → 0<δ →
      Tendsto (fun N => ∫ z : Disorder N μ.maxDegree × Vector N,
        sourceNormError μ β (plantedCoreCost μ β) δ q₁ q₂ (Thresholds.qStar μ.xi β) z
          ∂plantedLaw (mixtureCoefficients μ) β) atTop (𝓝 (0:ℝ))) :
    ∃ κ γ a c C : ℝ, 0<κ ∧ 0<γ ∧ 0<a ∧ 0<c ∧ 0<C ∧
      (∀ᶠ N : ℕ in atTop, ∃ Ω₀ : Set (Disorder N μ.maxDegree), MeasurableSet Ω₀ ∧
        (disorderLaw N μ.maxDegree).real Ω₀ᶜ≤C*Real.exp (-a*N) ∧
        ∀ D∈Ω₀, ∀ hN : 2≤N, PersistentMemoryConclusions hN μ β D κ γ a c C) ∧
      (∀ η : ℝ, 0<η → ∀ᶠ N : ℕ in atTop, ∃ Ω : Set (Disorder N μ.maxDegree),
        MeasurableSet Ω ∧ (disorderLaw N μ.maxDegree).real Ωᶜ<η ∧
        ∀ D∈Ω, ∀ hN : 2≤N, MemoryConclusions hN μ β D b κ γ a c C) := by
  apply general_main_plateau_of_weightedReplicaMoment μ hβd hβs hb
  intro q₁ q₂ δ hc hδ
  exact general_sourceWeightedReplicaMoment_of_planted μ hβd hβs
    (plantedCoreCost μ β) δ q₁ q₂ (hPlanted q₁ q₂ δ hc hδ)

end
end SlowEquilibration.SphericalMemoryAssembly
