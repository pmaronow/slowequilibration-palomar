-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalDSFiniteBridge
public import SlowEquilibration.PureCapturePhysicalNormFromPressureAndDecay

/-! Source directing norm-Q support with Dovbysh--Sudakov supplied by its
constructive theorem on the actual physical countable weak-limit array. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalNormFromPressureAndDecayDS

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalFullToScore
open PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalReplicaExclusionLimit
open PureCapturePhysicalNormFromPressureAndDecay
open PureCapturePhysicalDSFiniteBridge
open PureCapturePhysicalReplicaExclusionDirecting
open PureCaptureRandomDirectingScoreArray
open SlowEquilibration.DirectingPhysical
open GaussianGGEnsemble
open OverlapPaper
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The source Theorem 6.3 norm-Q conclusion for actual physical full-array
weak limits, with its DS directing representation and original-temperature
energy budget both constructed. The remaining analytic inputs are explicit
physical replica exclusion, a near-one pair cap, and the pair covariance
mean. -/
theorem asymptoticPhysicalFullLimit_norm_Q_of_pressure_and_decay_DS
    {k : ℕ} (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β) {x Q : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hphysicalExclude : ∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q →
      ∃ m : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
        Tendsto (fun n : ℕ =>
          (physicalFullOverlapLaw (n := n) (m := m) μ β :
            Measure (FullOverlapCoordinates m)) (fullEquilateralEvent m q ρ))
          atTop (𝓝 0))
    (hphysicalCap : ∃ a < (1 : ℝ),
      Tendsto (fun n : ℕ =>
        (physicalFullOverlapLaw (n := n) (m := 2) μ β :
          Measure (FullOverlapCoordinates 2)) (fullPairCapEvent a))
        atTop (𝓝 0))
    (hphysicalMean : Tendsto (fun n : ℕ =>
      ∫ c, μ.xi (c 0 1) ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1 - x) * μ.xi Q)))
    (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (p t)))
    (hpdiff : DifferentiableAt ℝ p β) :
    ∀ z ∈ physicalFullAsymptoticLimitSet μ β,
      ∃ R : RandomDirectingData (ProbabilityMeasure DSHilbert) DSHilbert,
        (∀ᵐ ω ∂(R.disorderLaw),
          ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ^ 2 = Q) ∧
        ∀ T, fullToScoreArray k z T = R.scoreLaw k T := by
  exact asymptoticPhysicalFullLimit_norm_Q_of_pressure_and_decay
    μ hβ hx hQ hphysicalExclude hphysicalCap hphysicalMean
    p hp hpdiff
    (fun z hz => physicalFullAsymptoticLimit_randomDirecting μ β hz)

end SlowEquilibration.PureCapturePhysicalNormFromPressureAndDecayDS
