-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPairMeanFromParisi
public import SlowEquilibration.PureCapturePhysicalThreeActiveEvenMoments

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalNormFromThreeActiveEvenDegrees

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open SphericalTAPCertificate
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalFullToScore
open PureCapturePhysicalReplicaExclusionLimit
open PureCapturePhysicalThreeActiveEvenMoments
open PureCapturePhysicalPairMeanFromParisi
open PureCaptureRandomDirectingScoreArray
open OverlapPaper
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The source directing norm conclusion follows from the physical Parisi
pressure formula and any three distinct strictly positive even pair-moment limits. The excluded-overlap
condition is derived from those moments, with two replicas. -/
theorem asymptoticPhysicalFullLimit_norm_Q_of_variational_pressure_three_active_even_moments
    {k : ℕ} (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (CSParisiMeasure.variationalValue μ t)))
    (a b c : ℕ) (ha0 : 0 < a) (hab : a < b) (hbc : b < c)
    (ha : Even a) (hb : Even b) (hc : Even c)
    (hA : Tendsto (fun n : ℕ =>
      ∫ z, (z 0 1) ^ a ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1 - x) * Q ^ a)))
    (hB : Tendsto (fun n : ℕ =>
      ∫ z, (z 0 1) ^ b ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1 - x) * Q ^ b)))
    (hC : Tendsto (fun n : ℕ =>
      ∫ z, (z 0 1) ^ c ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1 - x) * Q ^ c))) :
    ∀ z ∈ physicalFullAsymptoticLimitSet μ β,
      ∃ R : RandomDirectingData (ProbabilityMeasure DSHilbert) DSHilbert,
        (∀ᵐ ω ∂(R.disorderLaw),
          ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ^ 2 = Q) ∧
        ∀ T, fullToScoreArray k z T = R.scoreLaw k T := by
  apply asymptoticPhysicalFullLimit_norm_Q_of_variational_pressure_exclusion μ h _ hp
  intro q hq hne
  obtain ⟨ρ, hρ, hdecay⟩ :=
    physical_pair_exclusion_of_three_active_even_moments μ β x Q h.overlap_range.1
      a b c ha0 hab hbc ha hb hc hA hB hC q hq hne
  exact ⟨2, ρ, hρ, hdecay⟩

end SlowEquilibration.PureCapturePhysicalNormFromThreeActiveEvenDegrees
