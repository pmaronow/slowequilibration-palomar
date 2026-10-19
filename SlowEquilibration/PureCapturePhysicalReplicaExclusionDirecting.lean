-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCaptureDirectingFullToScore

/-! Concrete passage from physical Gibbs replica-exclusion estimates to
the corresponding random-directing-kernel statements, whenever a full
overlap-array Dovbysh--Sudakov representation is supplied. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalReplicaExclusionDirecting

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalFullToScore
open PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalReplicaExclusionLimit
open PureCaptureDirectingFullToScore
open PureCaptureRandomDirectingScoreArray
open SlowEquilibration.DirectingPhysical
open GaussianReplicaKernel
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {Ξ H : Type*} [MeasurableSpace Ξ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

theorem directingFullOverlapCoordinates_preimage_equilateral
    (m : ℕ) (q ρ : ℝ) :
    directingFullOverlapCoordinates (H := H) ⁻¹'
        fullEquilateralEvent m q ρ =
      equilateralEvent (H := H) m q ρ := by
  ext σ
  simp only [mem_preimage, fullEquilateralEvent, equilateralEvent,
    Set.mem_ofPred_eq]
  constructor <;> intro h i j hij
  · simpa [directingFullOverlapCoordinates, hij] using h i j hij
  · simpa [directingFullOverlapCoordinates, hij] using h i j hij

theorem directingFullOverlapLaw_equilateral_mass
    (d : Measure Ξ) [IsProbabilityMeasure d]
    (G : Kernel Ξ H) [IsMarkovKernel G]
    (m : ℕ) (q ρ : ℝ) :
    (directingFullOverlapLaw d G m : Measure (FullOverlapCoordinates m))
      (fullEquilateralEvent m q ρ) =
    law d G m (equilateralEvent (H := H) m q ρ) := by
  unfold directingFullOverlapLaw
  rw [ProbabilityMeasure.map_apply' _
    directingFullOverlapCoordinates_continuous.measurable.aemeasurable
    (fullEquilateralEvent_open m q ρ).measurableSet]
  exact congrArg _ (directingFullOverlapCoordinates_preimage_equilateral m q ρ)

theorem directingFullOverlapCoordinates_preimage_pairCap (a : ℝ) :
    directingFullOverlapCoordinates (H := H) ⁻¹' fullPairCapEvent a =
      pairCapEvent (H := H) a := by
  ext σ
  simp [fullPairCapEvent, pairCapEvent, directingFullOverlapCoordinates]

theorem directingFullOverlapLaw_pairCap_mass
    (d : Measure Ξ) [IsProbabilityMeasure d]
    (G : Kernel Ξ H) [IsMarkovKernel G] (a : ℝ) :
    (directingFullOverlapLaw d G 2 : Measure (FullOverlapCoordinates 2))
      (fullPairCapEvent a) =
    law d G 2 (pairCapEvent (H := H) a) := by
  unfold directingFullOverlapLaw
  rw [ProbabilityMeasure.map_apply' _
    directingFullOverlapCoordinates_continuous.measurable.aemeasurable
    (fullPairCapEvent_open a).measurableSet]
  exact congrArg _ (directingFullOverlapCoordinates_preimage_pairCap a)

def directingDataFullLaw (R : RandomDirectingData Ξ H) (m : ℕ) :
    ProbabilityMeasure (FullOverlapCoordinates m) := by
  letI : IsProbabilityMeasure R.disorderLaw := R.disorderProbability
  letI : IsMarkovKernel R.directingKernel := R.directingMarkov
  exact directingFullOverlapLaw R.disorderLaw R.directingKernel m

/-- A full-array DS representation automatically reproduces the precise
query-plus-block capture score law. -/
theorem fullToScoreArray_eq_of_directing_full_representation
    (R : RandomDirectingData Ξ H) (k : ℕ)
    (x : FullOverlapLawArray)
    (hrep : ∀ m, x m = directingDataFullLaw R m) (T : ℕ) :
    fullToScoreArray k x T = R.scoreLaw k T := by
  letI : IsProbabilityMeasure R.disorderLaw := R.disorderProbability
  letI : IsMarkovKernel R.directingKernel := R.directingMarkov
  change (x (T*k+1)).map fullScoreProjection =
    randomDirectingScoreLaw R.disorderLaw R.directingKernel k T
  rw [hrep]
  exact directingFullOverlapLaw_map_score R.disorderLaw R.directingKernel k T

/-- Full-sequence physical equilateral exclusion transfers to the
annealed directing IID replica law. -/
theorem directing_equilateral_zero_of_physical_decay
    (μ : FiniteMixture) (β : ℝ)
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β)
    (R : RandomDirectingData Ξ H)
    (hrep : ∀ m, x m = directingDataFullLaw R m)
    (m : ℕ) (q ρ : ℝ)
    (hdecay : Tendsto (fun n : ℕ =>
      (physicalFullOverlapLaw (n := n) (m := m) μ β :
        Measure (FullOverlapCoordinates m)) (fullEquilateralEvent m q ρ))
      atTop (𝓝 0)) :
    law R.disorderLaw R.directingKernel m
      (equilateralEvent (H := H) m q ρ) = 0 := by
  letI : IsProbabilityMeasure R.disorderLaw := R.disorderProbability
  letI : IsMarkovKernel R.directingKernel := R.directingMarkov
  have hzero := asymptoticFullOverlapLaw_equilateral_zero_of_physical_decay
    μ β m q ρ hdecay hx
  rw [hrep m] at hzero
  change (directingFullOverlapLaw R.disorderLaw R.directingKernel m :
    Measure (FullOverlapCoordinates m)) (fullEquilateralEvent m q ρ) = 0 at hzero
  rw [directingFullOverlapLaw_equilateral_mass] at hzero
  exact hzero

/-- The near-one pair exclusion transfers to the annealed directing
IID pair law. -/
theorem directing_pairCap_zero_of_physical_decay
    (μ : FiniteMixture) (β a : ℝ)
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β)
    (R : RandomDirectingData Ξ H)
    (hrep : ∀ m, x m = directingDataFullLaw R m)
    (hdecay : Tendsto (fun n : ℕ =>
      (physicalFullOverlapLaw (n := n) (m := 2) μ β :
        Measure (FullOverlapCoordinates 2)) (fullPairCapEvent a))
      atTop (𝓝 0)) :
    law R.disorderLaw R.directingKernel 2
      (pairCapEvent (H := H) a) = 0 := by
  letI : IsProbabilityMeasure R.disorderLaw := R.disorderProbability
  letI : IsMarkovKernel R.directingKernel := R.directingMarkov
  have hzero := asymptoticFullOverlapLaw_pairCap_zero_of_physical_decay
    μ β a hdecay hx
  rw [hrep 2] at hzero
  change (directingFullOverlapLaw R.disorderLaw R.directingKernel 2 :
    Measure (FullOverlapCoordinates 2)) (fullPairCapEvent a) = 0 at hzero
  rw [directingFullOverlapLaw_pairCap_mass] at hzero
  exact hzero

end SlowEquilibration.PureCapturePhysicalReplicaExclusionDirecting
