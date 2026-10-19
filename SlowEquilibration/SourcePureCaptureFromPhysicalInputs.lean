-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCaptureFromCoarseCover
public import SlowEquilibration.PureCapturePhysicalCoarseDiniAssembly

/-! Actual pure critical-band capture, with all marked Kac--Rice,
Laplace, denominator, maximum, finite-score compactness, and parameter
selection steps discharged. The remaining hypotheses are the three
physical inputs to source Proposition 9.16. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCaptureFromPhysicalInputs
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory SphericalModel
open SphericalTAPCertificate PureStationarity
open SourcePureCaptureFixedCapEstimates SourcePureCaptureFromCoarseCover
open PureCapturePhysicalCoarseDiniAssembly
open PureCapturePhysicalAsymptoticFullLift PureCapturePhysicalFullToScore
open PureCaptureRandomDirectingScoreArray OverlapPaper
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Both source pure capture conclusions for the literal original-field
critical bands, assuming only the named physical coarse-cover inputs. -/
theorem pure_original_capture_of_three_physical_inputs
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hNorm : PhysicalDirectingNormQ
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q)
    (hMean : PhysicalReplicaMeanEnergy
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q
      (pureEnergyConstant p (by omega)))
    (hRelocate : PhysicalHighEnergyRelocation
      (FiniteMixture.pure p (by omega) 1 (by positivity))
      (pureEnergyConstant p (by omega))) :
    (∀ ε : ℝ, 0 < ε → ∃ L w : ℝ, 0 < L ∧ 0 < w ∧
      ∀ L' w' : ℝ, L ≤ L' → w ≤ w' →
        Filter.limsup (pureMicroscopicUncovered p hp β Q L' w') atTop ≤ ε) ∧
    ∀ b : ℝ, 0 < b → Tendsto
      (fun L : ℝ => Filter.limsup (pureFixedBandUncovered p hp β Q L b) atTop)
      atTop (𝓝 (0:ℝ)) := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  obtain ⟨a,κ,δ,hEst⟩ := pure_original_capture_fixed_cap_estimates p hp h
  have hcoarse := physical_coarse_cover_of_three_physical_inputs μ β h.overlap_range
    hEst.cap_below_overlap hNorm hMean hRelocate
  exact ⟨pure_microscopic_capture_of_coarse_cover p hp h hEst hcoarse,
    pure_fixed_band_capture_of_coarse_cover p hp h hEst hcoarse⟩

/-- Version accepting the established physical norm-Q score theorem,
including its current reduction to the three even physical pair moments. -/
theorem pure_original_capture_of_normQ_score_mean_relocation
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hNorm : ∀ k : ℕ, ∀ z ∈ physicalFullAsymptoticLimitSet
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β,
      ∃ R : RandomDirectingData (ProbabilityMeasure DSHilbert) DSHilbert,
        (∀ᵐ ω ∂(R.disorderLaw), ∀ᵐ v ∂(R.directingKernel ω), ‖v‖^2=Q) ∧
        ∀ T, fullToScoreArray k z T=R.scoreLaw k T)
    (hMean : PhysicalReplicaMeanEnergy
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q
      (pureEnergyConstant p (by omega)))
    (hRelocate : PhysicalHighEnergyRelocation
      (FiniteMixture.pure p (by omega) 1 (by positivity))
      (pureEnergyConstant p (by omega))) :
    (∀ ε : ℝ, 0 < ε → ∃ L w : ℝ, 0 < L ∧ 0 < w ∧
      ∀ L' w' : ℝ, L ≤ L' → w ≤ w' →
        Filter.limsup (pureMicroscopicUncovered p hp β Q L' w') atTop ≤ ε) ∧
    ∀ b : ℝ, 0 < b → Tendsto
      (fun L : ℝ => Filter.limsup (pureFixedBandUncovered p hp β Q L b) atTop)
      atTop (𝓝 (0:ℝ)) := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  obtain ⟨a,κ,δ,hEst⟩ := pure_original_capture_fixed_cap_estimates p hp h
  have hcoarse := physical_coarse_cover_of_normQ_score_mean_relocation μ β
    h.overlap_range hEst.cap_below_overlap hNorm hMean hRelocate
  exact ⟨pure_microscopic_capture_of_coarse_cover p hp h hEst hcoarse,
    pure_fixed_band_capture_of_coarse_cover p hp h hEst hcoarse⟩

end
end SlowEquilibration.SourcePureCaptureFromPhysicalInputs
