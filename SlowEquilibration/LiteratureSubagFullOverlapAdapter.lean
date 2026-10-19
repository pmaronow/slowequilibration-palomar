-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagReplicaExclusion
public import SlowEquilibration.PureCapturePhysicalReplicaExclusionLimit

/-!
# Subag's annealed equilateral event is the literal physical full-array event

The local full-overlap array is a map of the same disorder-averaged original
Gibbs replica law used in Subag's Definition 2.  This file proves the
identification rather than silently replacing the ensemble by a selected
or perturbed replica law.  It also translates the full-sequence exclusion
from Theorem 5 and Remark 25 into the exact premise consumed by the
physical norm-`Q` directing-measure argument.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagFullOverlapAdapter

open MeasureTheory Filter Set
open LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open LiteratureSubagReplicaExclusion
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalReplicaExclusionLimit
open scoped Topology
set_option autoImplicit false

/-- Exact equality of the two finite-dimensional annealed event
probabilities, with the diagonal ignored in both conventions. -/
theorem expectedOverlapBlockProbability_eq_fullOverlapLaw_real
    (n k : ℕ) (μ : FiniteMixture) (β q ρ : ℝ) :
    expectedOverlapBlockProbability (n+2) k μ β q ρ =
      (physicalFullOverlapLaw (n := n) (m := k) μ β :
        Measure (FullOverlapCoordinates k)).real
          (fullEquilateralEvent k q ρ) := by
  have hpre :
      physicalFullOverlapCoordinates ⁻¹' fullEquilateralEvent k q ρ =
        {σ : Fin k → SphericalModel.Vector (n+2) |
          ∀ i j, i ≠ j →
            |SphericalModel.overlap (σ i) (σ j)-q| < ρ} := by
    ext σ
    constructor
    · intro h i j hij
      simpa only [Set.mem_preimage, Set.mem_ofPred_eq,fullEquilateralEvent,
        physicalFullOverlapCoordinates,ite_eq_right hij] using h i j hij
    · intro h i j hij
      simpa only [Set.mem_preimage, Set.mem_ofPred_eq,fullEquilateralEvent,
        physicalFullOverlapCoordinates,ite_eq_right hij] using h i j hij
  change (GaussianReplicaKernel.law
      (SphericalModel.disorderLaw (n+2) μ.maxDegree)
      (SphericalModel.allDimensionGibbsKernel (SphericalModel.mixtureCoefficients μ) β)
      k).real
        {σ : Fin k → SphericalModel.Vector (n+2) |
          ∀ i j, i ≠ j → |SphericalModel.overlap (σ i) (σ j)-q| < ρ} =
    ((GaussianReplicaKernel.law
      (SphericalModel.disorderLaw (n+2) μ.maxDegree)
      (SphericalModel.allDimensionGibbsKernel (SphericalModel.mixtureCoefficients μ) β)
      k).map physicalFullOverlapCoordinates).real (fullEquilateralEvent k q ρ)
  rw [Measure.real, Measure.real,
    Measure.map_apply physicalFullOverlapCoordinates_continuous.measurable
      (fullEquilateralEvent_open k q ρ).measurableSet, hpre]

/-- The real annealed Subag probability tends to zero exactly when the
corresponding original full-overlap event has vanishing `ENNReal` mass. -/
theorem fullOverlapLaw_equilateral_tendsto_zero_of_expected
    (μ : FiniteMixture) (β q ρ : ℝ) (k : ℕ)
    (h : Tendsto (fun N : ℕ =>
      expectedOverlapBlockProbability N k μ β q ρ)
      atTop (nhds (0 : ℝ))) :
    Tendsto (fun n : ℕ =>
      (physicalFullOverlapLaw (n := n) (m := k) μ β :
        Measure (FullOverlapCoordinates k)) (fullEquilateralEvent k q ρ))
      atTop (nhds 0) := by
  have hshift := h.comp (tendsto_add_atTop_nat 2)
  have hreal : Tendsto (fun n : ℕ =>
      ((physicalFullOverlapLaw (n := n) (m := k) μ β :
        Measure (FullOverlapCoordinates k)) (fullEquilateralEvent k q ρ)).toReal)
      atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def, expectedOverlapBlockProbability_eq_fullOverlapLaw_real,
      Measure.real] using hshift
  exact (ENNReal.tendsto_toReal_zero_iff).mp hreal

/-- Exact `hphysicalExclude` premise used by the norm-`Q` directing
argument, conditional only on the cited Subag endpoints and the separately
proved strict physical TAP gap at every off-contact overlap. -/
theorem physical_full_overlap_exclusion_of_offContactTAPGap
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (h5 : Theorem5 D) (h25 : Remark25Contrapositive μ β)
    {Q : ℝ}
    (hgap : ∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q → tapValue D q < D.pressure) :
    ∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q →
      ∃ k : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
        Tendsto (fun n : ℕ =>
          (physicalFullOverlapLaw (n := n) (m := k) μ β :
            Measure (FullOverlapCoordinates k)) (fullEquilateralEvent k q ρ))
          atTop (nhds 0) := by
  intro q hq hqQ
  obtain ⟨k,ρ,hρ,hdecay⟩ :=
    equilateral_mass_tendsto_zero_of_strictTAPGap D h5 h25 hq (hgap q hq hqQ)
  exact ⟨k,ρ,hρ,fullOverlapLaw_equilateral_tendsto_zero_of_expected μ β q ρ k hdecay⟩

end SlowEquilibration.LiteratureSubagFullOverlapAdapter
