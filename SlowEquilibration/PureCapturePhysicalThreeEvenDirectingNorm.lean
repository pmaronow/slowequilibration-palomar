-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalNormFromThreeActiveEvenDegrees

@[expose] public section
noncomputable section

namespace SlowEquilibration.PureCapturePhysicalThreeEvenDirectingNorm

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalTAPCertificate
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalReplicaExclusionLimit PureCapturePhysicalReplicaExclusionDirecting
open PureCapturePhysicalThreeActiveEvenMoments PureCapturePhysicalPairMeanFromParisi
open PureCapturePhysicalPairMeanDirecting PureCapturePhysicalGGBorelDirectingTransfer
open PureCapturePhysicalPanchenkoUnconditionalEnergy PureCapturePhysicalNearOneDecay
open PureCaptureRandomDirectingScoreArray DirectingPhysical GaussianReplicaKernel
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The norm conclusion holds for every actual full directing representation.
Keeping that representation available permits the source atomic classification. -/
theorem directing_norm_Q_of_three_even_physical_moments
    {Ξ H : Type*} [MeasurableSpace Ξ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (CSParisiMeasure.variationalValue μ t)))
    (a b c : ℕ) (ha0 : 0 < a) (hab : a < b) (hbc : b < c)
    (ha : Even a) (hb : Even b) (hc : Even c)
    (hmoments : ∀ p ∈ ({a, b, c} : Finset ℕ),
      Tendsto (fun n : ℕ => ∫ z, (z 0 1) ^ p ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
        atTop (𝓝 ((1 - x) * Q ^ p)))
    {z : FullOverlapLawArray} (hz : z ∈ physicalFullAsymptoticLimitSet μ β)
    (R : RandomDirectingData Ξ H) (hrep : ∀ m, z m = directingDataFullLaw R m)
    (hball : ∀ᵐ ω ∂(R.disorderLaw), ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ≤ 1) :
    ∀ᵐ ω ∂(R.disorderLaw), ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ^ 2 = Q := by
  let : IsProbabilityMeasure R.disorderLaw := R.disorderProbability
  let : IsMarkovKernel R.directingKernel := R.directingMarkov
  have hbudget := physical_total_energy_budget_tendsto_zero μ β
    (CSParisiMeasure.variationalValue μ) hp
    (certificate_variationalValue_hasDerivAt h).differentiableAt
  have hGG := covarianceGG_of_physical_sublinear_budget μ h.beta_pos hbudget hz R hrep hball
  have hmean := directingPairCovarianceMean_eq_of_physical_tendsto μ β _
    (physicalPairCovarianceMean_tendsto_of_variational_pressure μ h hp) hz R hrep hball
  have hexclude : ∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q →
      ∃ m : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
        law R.disorderLaw R.directingKernel m
          (equilateralEvent (H := H) m q ρ) = 0 := by
    intro q hq hne
    obtain ⟨ρ, hρ, hdecay⟩ := physical_pair_exclusion_of_three_active_even_moments
      μ β x Q h.overlap_range.1 a b c ha0 hab hbc ha hb hc
      (hmoments a (by simp)) (hmoments b (by simp)) (hmoments c (by simp)) q hq hne
    exact ⟨2, ρ, hρ,
      directing_equilateral_zero_of_physical_decay μ β hz R hrep 2 q ρ hdecay⟩
  obtain ⟨t, ht, hdecay⟩ := physical_pair_near_one_decay μ h.beta_pos.le
  have hcap : ∃ t < (1 : ℝ),
      law R.disorderLaw R.directingKernel 2 (pairCapEvent (H := H) t) = 0 :=
    ⟨t, ht, directing_pairCap_zero_of_physical_decay μ β t hz R hrep hdecay⟩
  exact directing_norm_Q_of_source_inputs R.disorderLaw R.directingKernel μ
    h.weight_range h.overlap_range hball hexclude hcap hGG hmean

end SlowEquilibration.PureCapturePhysicalThreeEvenDirectingNorm
