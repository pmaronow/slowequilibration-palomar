-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSVariationalTemperatureDerivative
public import SlowEquilibration.SphericalTAPCertificate
public import SlowEquilibration.PureCapturePhysicalConvexDerivativeLimit
public import SlowEquilibration.PureCapturePhysicalNormFromPressureAndExclusionDS

@[expose] public section

open Set Filter MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel
open SlowEquilibration.SphericalForm
open SlowEquilibration.CrisantiSommers
open SlowEquilibration.CSParisiMeasure
open SlowEquilibration.SphericalTAPCertificate
open SlowEquilibration.CSVariationalTemperatureDerivative
open SlowEquilibration.PureCapturePhysicalConvexDerivativeLimit
open SlowEquilibration.PureCapturePhysicalFullOverlapArray
open SlowEquilibration.PureCapturePhysicalFullToScore
open SlowEquilibration.PureCapturePhysicalAsymptoticFullLift
open SlowEquilibration.PureCapturePhysicalReplicaExclusionLimit
open SlowEquilibration.PureCaptureRandomDirectingScoreArray
open SlowEquilibration.PureCapturePhysicalNormFromPressureAndExclusionDS
open SlowEquilibration
open OverlapPaper
open scoped Topology

namespace SlowEquilibration.PureCapturePhysicalPairMeanFromParisi

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

/-- The certificate identifies the derivative of the ordinary CS minimum
with its printed one-step covariance mean. -/
theorem certificate_variationalValue_hasDerivAt {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q) :
    HasDerivAt (variationalValue μ)
      (β * (μ.xi 1 - (1 - x) * μ.xi Q)) β := by
  have hd := CSVariationalTemperatureDerivative.variationalValue_hasDerivAt μ β
  have hi : (∫ r, μ.xi r ∂(canonicalMinimizer μ β).law) =
      (1 - x) * μ.xi Q := by
    rw [h.canonical_law, integral_twoAtom ⟨h.weight_range.1.le, h.weight_range.2.le⟩]
    rw [μ.xi_zero]
    ring
  rwa [hi] at hd

/-- Full physical Parisi pressure convergence and the source certificate
identify the true two-replica covariance mean. No independent mean premise
is supplied. -/
theorem physicalPairCovarianceMean_tendsto_of_variational_pressure
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (variationalValue μ t))) :
    Tendsto (fun n : ℕ =>
      ∫ c, μ.xi (c 0 1) ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1 - x) * μ.xi Q)) := by
  have hv := certificate_variationalValue_hasDerivAt h
  have hm := physicalPairCovarianceMean_tendsto_of_pressure_limit μ h.beta_pos
    (variationalValue μ) hp hv.differentiableAt
  convert hm using 1
  rw [hv.deriv]
  field_simp [h.beta_pos.ne']
  ring

/-- In the certificate phase, the pressure formula discharges the physical
pair-mean input of the DS-free norm-Q theorem. The remaining distinct
thermodynamic input is source replica exclusion away from Q. -/
theorem asymptoticPhysicalFullLimit_norm_Q_of_variational_pressure_exclusion
    {k : ℕ} (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hphysicalExclude : ∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q →
      ∃ m : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
        Tendsto (fun n : ℕ =>
          (physicalFullOverlapLaw (n := n) (m := m) μ β :
            Measure (FullOverlapCoordinates m)) (fullEquilateralEvent m q ρ))
          atTop (𝓝 0))
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (variationalValue μ t))) :
    ∀ z ∈ physicalFullAsymptoticLimitSet μ β,
      ∃ R : RandomDirectingData (ProbabilityMeasure DSHilbert) DSHilbert,
        (∀ᵐ ω ∂(R.disorderLaw),
          ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ^ 2 = Q) ∧
        ∀ T, fullToScoreArray k z T = R.scoreLaw k T := by
  exact asymptoticPhysicalFullLimit_norm_Q_of_pressure_exclusion_mean
    μ h.beta_pos h.weight_range h.overlap_range hphysicalExclude
    (physicalPairCovarianceMean_tendsto_of_variational_pressure μ h hp)
    (variationalValue μ) hp (certificate_variationalValue_hasDerivAt h).differentiableAt

end
end SlowEquilibration.PureCapturePhysicalPairMeanFromParisi
