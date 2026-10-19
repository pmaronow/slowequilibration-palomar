-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalDSOffDiagonalTransport
public import SlowEquilibration.PureCapturePhysicalReplicaExclusionDirecting
public import OverlapPaper.DSHilbertProjection
public import OverlapPaper.DSFiniteProjection

/-! Construct the actual random Hilbert directing kernel from the
Dovbysh--Sudakov representation of a physical full-array weak limit.
The finite IID sampling transport keeps the diagonal-one convention. -/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory
open SlowEquilibration
open SlowEquilibration.GaussianReplicaKernel
open SlowEquilibration.PureCaptureRandomDirectingScoreArray
open SlowEquilibration.PureCapturePhysicalReplicaExclusionDirecting
open SlowEquilibration.PureCapturePhysicalInfiniteArrayTightness
open SlowEquilibration.PureCapturePhysicalInfiniteAsymptoticLift
open SlowEquilibration.PureCapturePhysicalInfiniteDSInput
open SlowEquilibration.PureCapturePhysicalDSOffDiagonalTransport
open SlowEquilibration.PureCapturePhysicalFullOverlapArray
open SlowEquilibration.PureCaptureDirectingFullToScore
open OverlapPaper
open SphericalModel SphericalForm
open scoped ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace SlowEquilibration.PureCapturePhysicalDSFiniteBridge

noncomputable def probabilityEvaluationKernel (H : Type*) [MeasurableSpace H] :
    Kernel (ProbabilityMeasure H) H where
  toFun μ := (μ : Measure H)
  measurable' := measurable_subtype_coe

instance probabilityEvaluationKernel_markov (H : Type*) [MeasurableSpace H] :
    IsMarkovKernel (probabilityEvaluationKernel H) := by
  constructor
  intro μ
  change IsProbabilityMeasure (μ : Measure H)
  infer_instance

@[simp] theorem probabilityEvaluationKernel_apply (H : Type*) [MeasurableSpace H]
    (μ : ProbabilityMeasure H) : probabilityEvaluationKernel H μ = (μ : Measure H) := rfl

noncomputable def dsRandomDirectingData
    (Λ : ProbabilityMeasure (ProbabilityMeasure DSHilbert)) :
    RandomDirectingData (ProbabilityMeasure DSHilbert) DSHilbert where
  disorderLaw := Λ
  directingKernel := probabilityEvaluationKernel DSHilbert
  disorderProbability := inferInstance
  directingMarkov := inferInstance

theorem finiteSamplingKernel_eq (m : ℕ) :
    GaussianReplicaKernel.iid (probabilityEvaluationKernel DSHilbert) m =
      (iidSamplingKernel DSHilbert).map (firstFiniteSamples m) := by
  apply Kernel.ext
  intro μ
  rw [GaussianReplicaKernel.iid_apply,
    Kernel.map_apply _ (measurable_firstFiniteSamples m),
    iidSamplingKernel]
  exact (infiniteIID_firstFiniteSamples m μ).symm

theorem finiteSamplingLaw_eq
    (Λ : ProbabilityMeasure (ProbabilityMeasure DSHilbert)) (m : ℕ) :
    GaussianReplicaKernel.law (Λ : Measure (ProbabilityMeasure DSHilbert))
      (probabilityEvaluationKernel DSHilbert) m =
    (randomSamplingLaw (Λ : Measure (ProbabilityMeasure DSHilbert))).map
      (fun p => firstFiniteSamples m p.2) := by
  unfold GaussianReplicaKernel.law
  rw [finiteSamplingKernel_eq]
  rw [← Measure.map_comp _ _ (measurable_firstFiniteSamples m)]
  rw [← Measure.snd_compProd]
  unfold randomSamplingLaw
  change ((((Λ : Measure (ProbabilityMeasure DSHilbert)) ⊗ₘ
    iidSamplingKernel DSHilbert).map Prod.snd).map (firstFiniteSamples m)) = _
  rw [Measure.map_map (measurable_firstFiniteSamples m) measurable_snd]
  rfl

def fullFromRealOffDiagonal (m : ℕ) (r : ReplicaPair → ℝ) :
    FullOverlapCoordinates m := fun i j =>
  if hij : i.val < j.val then r ⟨(i.val, j.val), hij⟩ else
  if hji : j.val < i.val then r ⟨(j.val, i.val), hji⟩ else 1

theorem continuous_fullFromRealOffDiagonal (m : ℕ) :
    Continuous (fullFromRealOffDiagonal m) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold fullFromRealOffDiagonal
  split_ifs <;> fun_prop

theorem fullFromRealOffDiagonal_realOverlapArray (m : ℕ) (R : OverlapArray) :
    fullFromRealOffDiagonal m (realOverlapArray R) =
      fun i j => completeArray R i.val j.val := by
  ext i j
  rfl

theorem fullFromRealOffDiagonal_physical (m : ℕ)
    (c : InfiniteOverlapCoordinates)
    (hc : ∀ k, infiniteTruncate k c ∈ fullGramCone k)
    (hd : ∀ k, infiniteTruncate k c ∈ fullUnitDiagonal k) :
    fullFromRealOffDiagonal m (realOverlapArray (toOffDiagonal c)) =
      infiniteTruncate m c := by
  rw [fullFromRealOffDiagonal_realOverlapArray]
  ext i j
  exact completeArray_toOffDiagonal c hc hd i.val j.val

theorem fullFromRealOffDiagonal_hilbert (m : ℕ) (v : ℕ → DSHilbert) :
    fullFromRealOffDiagonal m (hilbertOffDiagonalArray v) =
      directingFullOverlapCoordinates (firstFiniteSamples m v) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [fullFromRealOffDiagonal, directingFullOverlapCoordinates]
  · by_cases hlt : i.val < j.val
    · simp [fullFromRealOffDiagonal, directingFullOverlapCoordinates, hij, hlt,
        hilbertOffDiagonalArray, firstFiniteSamples]
    · have hgt : j.val < i.val := by omega
      simp [fullFromRealOffDiagonal, directingFullOverlapCoordinates, hij, hlt,
        hgt, hilbertOffDiagonalArray, firstFiniteSamples, real_inner_comm]

theorem hilbertRandomFullLaw_eq
    (Λ : ProbabilityMeasure (ProbabilityMeasure DSHilbert)) (m : ℕ) :
    directingDataFullLaw (dsRandomDirectingData Λ) m =
      (hilbertOffDiagonalSamplingProbability Λ).map
        (fullFromRealOffDiagonal m) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (GaussianReplicaKernel.law
    (Λ : Measure (ProbabilityMeasure DSHilbert))
    (probabilityEvaluationKernel DSHilbert) m).map
      directingFullOverlapCoordinates =
    ((randomSamplingLaw (Λ : Measure (ProbabilityMeasure DSHilbert))).map
      (fun p => hilbertOffDiagonalArray p.2)).map
      (fullFromRealOffDiagonal m)
  rw [finiteSamplingLaw_eq]
  rw [Measure.map_map directingFullOverlapCoordinates_continuous.measurable
    (show Measurable (fun p : ProbabilityMeasure DSHilbert × (ℕ → DSHilbert) =>
      firstFiniteSamples m p.2) from
      (measurable_firstFiniteSamples m).comp measurable_snd),
    Measure.map_map (continuous_fullFromRealOffDiagonal m).measurable
      (show Measurable (fun p : ProbabilityMeasure DSHilbert × (ℕ → DSHilbert) =>
        hilbertOffDiagonalArray p.2) from
        measurable_hilbertOffDiagonalArray.comp measurable_snd)]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall (fun p =>
    (fullFromRealOffDiagonal_hilbert m p.2).symm)

theorem physicalFullLaw_eq_offDiagonalFullLaw
    (μ : FiniteMixture) (β : ℝ)
    {ρ : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hρ : ρ ∈ physicalInfiniteAsymptoticLimitSet μ β) (m : ℕ) :
    infiniteToFullLawArray ρ m =
      ((ρ.map toOffDiagonal).map realOverlapArray).map
        (fullFromRealOffDiagonal m) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (ρ : Measure InfiniteOverlapCoordinates).map (infiniteTruncate m) =
    (((ρ : Measure InfiniteOverlapCoordinates).map toOffDiagonal).map
      realOverlapArray).map (fullFromRealOffDiagonal m)
  rw [Measure.map_map (continuous_fullFromRealOffDiagonal m).measurable
    continuous_realOverlapArray.measurable,
    Measure.map_map
      ((continuous_fullFromRealOffDiagonal m).measurable.comp
        continuous_realOverlapArray.measurable)
      continuous_toOffDiagonal.measurable]
  apply Measure.map_congr
  have hgood : ∀ᵐ c ∂(ρ : Measure InfiniteOverlapCoordinates),
      (∀ k, infiniteTruncate k c ∈ fullGramCone k) ∧
      (∀ k, infiniteTruncate k c ∈ fullUnitDiagonal k) := by
    filter_upwards [physicalInfiniteAsymptoticLimit_gram μ β hρ,
      physicalInfiniteAsymptoticLimit_unitDiagonal μ β hρ] with c hc hd
    exact ⟨hc, hd⟩
  filter_upwards [hgood] with c hc
  exact (fullFromRealOffDiagonal_physical m c hc.1 hc.2).symm

/-- Every physical countable asymptotic overlap law has a genuine random
Hilbert directing kernel. All full finite overlap marginals agree exactly,
and the conditional Hilbert vectors lie in the unit ball almost surely. -/
theorem physicalInfiniteAsymptoticLimit_randomDirecting
    (μ : FiniteMixture) (β : ℝ)
    {ρ : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hρ : ρ ∈ physicalInfiniteAsymptoticLimitSet μ β) :
    ∃ R : RandomDirectingData (ProbabilityMeasure DSHilbert) DSHilbert,
      (∀ m, infiniteToFullLawArray ρ m = directingDataFullLaw R m) ∧
      (∀ᵐ ω ∂(R.disorderLaw), ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ≤ 1) := by
  obtain ⟨ΛBall, hΛBall⟩ :=
    physicalInfiniteAsymptoticLimit_dovbyshSudakov μ β hρ
  let Λ := hilbertUnitDirectingLaw ΛBall
  refine ⟨dsRandomDirectingData Λ, ?_, ?_⟩
  · intro m
    calc
      infiniteToFullLawArray ρ m =
          ((ρ.map toOffDiagonal).map realOverlapArray).map
            (fullFromRealOffDiagonal m) :=
        physicalFullLaw_eq_offDiagonalFullLaw μ β hρ m
      _ = (hilbertOffDiagonalSamplingProbability Λ).map
          (fullFromRealOffDiagonal m) := by
        rw [hilbertOffDiagonalSamplingProbability_unitLaw, hΛBall]
      _ = directingDataFullLaw (dsRandomDirectingData Λ) m :=
        (hilbertRandomFullLaw_eq Λ m).symm
  · change ∀ᵐ (ω : ProbabilityMeasure DSHilbert) ∂(Λ : Measure (ProbabilityMeasure DSHilbert)),
      ∀ᵐ (v : DSHilbert) ∂(ω : Measure DSHilbert), ‖v‖ ≤ 1
    exact hilbertUnitDirectingLaw_ae_norm_le_one ΛBall

/-- The physical full-array tail cluster set has an unconditional
Dovbysh--Sudakov directing representation in the concrete separable
Hilbert space used by allLean. -/
theorem physicalFullAsymptoticLimit_randomDirecting
    (μ : FiniteMixture) (β : ℝ)
    {x : FullOverlapLawArray}
    (hx : x ∈ PureCapturePhysicalAsymptoticFullLift.physicalFullAsymptoticLimitSet μ β) :
    ∃ R : RandomDirectingData (ProbabilityMeasure DSHilbert) DSHilbert,
      (∀ m, x m = directingDataFullLaw R m) ∧
      (∀ᵐ ω ∂(R.disorderLaw), ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ≤ 1) := by
  obtain ⟨ρ, hρ, hr⟩ := fullAsymptoticLimit_exists_infiniteLimit μ β hx
  obtain ⟨R, hrep, hball⟩ :=
    physicalInfiniteAsymptoticLimit_randomDirecting μ β hρ
  refine ⟨R, ?_, hball⟩
  intro m
  rw [← hr]
  exact hrep m

end SlowEquilibration.PureCapturePhysicalDSFiniteBridge
