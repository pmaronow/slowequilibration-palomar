-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPairMeanWeakLimit
public import SlowEquilibration.PureCapturePhysicalReplicaExclusionDirecting

/-! The annealed directing-kernel pair covariance mean is the same as
the physical full-array pair mean whenever the full finite-marginal
Dovbysh--Sudakov representation holds. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalPairMeanDirecting

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalFullArrayCubeSupport
open PureCapturePhysicalPairMeanWeakLimit
open PureCaptureDirectingFullToScore
open PureCapturePhysicalReplicaExclusionDirecting
open PureCaptureRandomDirectingScoreArray
open SlowEquilibration.DirectingPhysical
open GaussianReplicaKernel GaussianGGEnsemble
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

theorem directingPairCovarianceMean_eq_fullArrayMean
    {Ξ H : Type*} [MeasurableSpace Ξ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (μ : FiniteMixture) (R : RandomDirectingData Ξ H)
    (x : FullOverlapLawArray)
    (hrep : ∀ m, x m = directingDataFullLaw R m)
    (hcube : x ∈ cubeFullOverlapLawArrays)
    (hball : ∀ᵐ ω ∂(R.disorderLaw),
      ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ≤ 1) :
    (∫ r, μ.xi r ∂overlapLaw R.disorderLaw R.directingKernel) =
      ∫ c, μ.xi (c 0 1) ∂(x 2 : Measure (FullOverlapCoordinates 2)) := by
  letI : IsProbabilityMeasure R.disorderLaw := R.disorderProbability
  letI : IsMarkovKernel R.directingKernel := R.directingMarkov
  let ψ : ℝ → ℝ := fun r => μ.xi (clipOverlap r)
  have hψ : Continuous ψ :=
    (continuous_iff_continuousAt.mpr fun r =>
      (μ.hasDerivAt_xi r).continuousAt).comp clipOverlap_continuous
  have hpair := (overlap_hasLaw R.disorderLaw R.directingKernel
    (0 : Fin 2) 1 (by decide)).integral_comp hψ.measurable.aestronglyMeasurable
  have hfull : HasLaw (directingFullOverlapCoordinates (H := H) (m := 2))
      (directingDataFullLaw R 2) (law R.disorderLaw R.directingKernel 2) := by
    refine ⟨directingFullOverlapCoordinates_continuous.measurable.aemeasurable, ?_⟩
    rfl
  have harray := hfull.integral_comp
    (clippedPairCovariance μ).continuous.measurable.aestronglyMeasurable
  have hpoint (σ : Fin 2 → H) :
      clippedPairCovariance μ (directingFullOverlapCoordinates σ) =
        ψ (inner ℝ (σ 0) (σ 1)) := by
    rfl
  have heq : (∫ r, ψ r ∂overlapLaw R.disorderLaw R.directingKernel) =
      ∫ c, clippedPairCovariance μ c
        ∂(directingDataFullLaw R 2 : Measure (FullOverlapCoordinates 2)) := by
    rw [← hpair, ← harray]
    exact integral_congr_ae (.of_forall fun σ => (hpoint σ).symm)
  have horig : (∫ r, ψ r ∂overlapLaw R.disorderLaw R.directingKernel) =
      ∫ r, μ.xi r ∂overlapLaw R.disorderLaw R.directingKernel := by
    apply integral_congr_ae
    exact (overlapLaw_ae_Icc R.disorderLaw R.directingKernel hball).mono
      (fun r hr => by simp [ψ, clipOverlap_eq_of_mem_Icc hr])
  have harrayOrig : (∫ c, clippedPairCovariance μ c
      ∂(x 2 : Measure (FullOverlapCoordinates 2))) =
      ∫ c, μ.xi (c 0 1) ∂(x 2 : Measure (FullOverlapCoordinates 2)) := by
    apply integral_congr_ae
    exact (hcube 2).mono (fun c hc => clippedPairCovariance_eq_on_cube μ hc)
  calc
    _ = ∫ c, clippedPairCovariance μ c
        ∂(x 2 : Measure (FullOverlapCoordinates 2)) := by
      rw [← horig, heq, hrep 2]
    _ = _ := harrayOrig

theorem directingPairCovarianceMean_eq_of_physical_tendsto
    {Ξ H : Type*} [MeasurableSpace Ξ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (μ : FiniteMixture) (β L : ℝ)
    (hmean : Tendsto (fun n : ℕ =>
      ∫ c, μ.xi (c 0 1) ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 L))
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β)
    (R : RandomDirectingData Ξ H)
    (hrep : ∀ m, x m = directingDataFullLaw R m)
    (hball : ∀ᵐ ω ∂(R.disorderLaw),
      ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ≤ 1) :
    (∫ r, μ.xi r ∂overlapLaw R.disorderLaw R.directingKernel) = L := by
  rw [directingPairCovarianceMean_eq_fullArrayMean μ R x hrep
    (physicalFullAsymptoticLimitSet_cube μ β hx) hball]
  exact asymptoticPairCovarianceMean_eq_of_physical_tendsto μ β L hmean hx

end SlowEquilibration.PureCapturePhysicalPairMeanDirecting
