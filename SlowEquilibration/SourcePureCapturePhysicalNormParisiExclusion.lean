-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalCoarseDiniAssembly
public import SlowEquilibration.PureCapturePhysicalPairMeanFromParisi
public import SlowEquilibration.PureCapturePhysicalNearOneDecay
public import SlowEquilibration.PureCapturePhysicalPanchenkoUnconditionalEnergy
public import SlowEquilibration.PureCapturePhysicalPairMeanDirecting

/-! The source directing-norm input for physical pure capture, reduced to the
published pressure identity and the manuscript's off-contact replica exclusion.
The latter must be obtained from a strict TAP gap and Subag's replicated-band
results; it is not part of the spherical Parisi formula.  This intermediate
theorem uses all-real-temperature pressure convergence because the existing
pair-mean and GG wrappers have that signature.  Chen's cited Parisi theorem
is stated for nonnegative inverse temperatures.  A final citation adapter
must localize those wrappers to a positive neighborhood of `β` (the local
energy-deviation lemmas already exist) or prove temperature-evenness. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapturePhysicalNormParisiExclusion
noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalTAPCertificate
open PureCapturePhysicalCoarseDiniAssembly
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalReplicaExclusionLimit
open PureCapturePhysicalReplicaExclusionDirecting
open PureCapturePhysicalNearOneDecay
open PureCapturePhysicalPanchenkoUnconditionalEnergy
open PureCapturePhysicalPairMeanFromParisi
open PureCapturePhysicalPairMeanDirecting
open PureCaptureRandomDirectingScoreArray
open SlowEquilibration.DirectingPhysical
open GaussianReplicaKernel GaussianGGEnsemble
open OverlapPaper
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- A source certificate, the full physical Parisi pressure formula, and
physical exclusion of every off-contact equilateral replica group imply the
literal `PhysicalDirectingNormQ` input used by the pure coarse-cover proof.
Every directing representation of every original-disorder array limit is
covered, not just one representation chosen for a score. -/
theorem physical_directing_normQ_of_parisi_and_replica_exclusion
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hparisi : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (CSParisiMeasure.variationalValue μ t)))
    (hexclude : ∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q →
      ∃ m : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
        Tendsto (fun n : ℕ =>
          (physicalFullOverlapLaw (n := n) (m := m) μ β :
            Measure (FullOverlapCoordinates m)) (fullEquilateralEvent m q ρ))
          atTop (𝓝 0)) :
    PhysicalDirectingNormQ μ β Q := by
  intro z hz R hrep hball
  let : IsProbabilityMeasure R.disorderLaw := R.disorderProbability
  let : IsMarkovKernel R.directingKernel := R.directingMarkov
  have hdirExclude : ∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q →
      ∃ m : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
        law R.disorderLaw R.directingKernel m
          (equilateralEvent (H := DSHilbert) m q ρ) = 0 := by
    intro q hq hqQ
    obtain ⟨m,ρ,hρ,hdecay⟩ := hexclude q hq hqQ
    exact ⟨m,ρ,hρ,
      directing_equilateral_zero_of_physical_decay μ β hz R hrep m q ρ hdecay⟩
  obtain ⟨a,ha,hdecay⟩ := physical_pair_near_one_decay μ h.beta_pos.le
  have hdirCap : law R.disorderLaw R.directingKernel 2
      (pairCapEvent (H := DSHilbert) a) = 0 :=
    directing_pairCap_zero_of_physical_decay μ β a hz R hrep hdecay
  have hdiff : DifferentiableAt ℝ (CSParisiMeasure.variationalValue μ) β :=
    (certificate_variationalValue_hasDerivAt h).differentiableAt
  have hGG : CovarianceGG
      R.disorderLaw R.directingKernel μ.xi :=
    physical_directing_covariance_gg μ h.beta_pos
      (CSParisiMeasure.variationalValue μ) hparisi hdiff hz R hrep hball
  have hmean : (∫ r, μ.xi r
      ∂overlapLaw R.disorderLaw R.directingKernel) =
      (1-x)*μ.xi Q :=
    directingPairCovarianceMean_eq_of_physical_tendsto μ β _
      (physicalPairCovarianceMean_tendsto_of_variational_pressure μ h hparisi)
      hz R hrep hball
  exact directing_norm_Q_of_source_inputs R.disorderLaw R.directingKernel μ
    h.weight_range h.overlap_range hball hdirExclude ⟨a,ha,hdirCap⟩ hGG hmean

end
end SlowEquilibration.SourcePureCapturePhysicalNormParisiExclusion
