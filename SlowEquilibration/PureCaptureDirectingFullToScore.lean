-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalAsymptoticNormSourceCompletion
public import SlowEquilibration.PureCapturePhysicalReplicaExclusionLimit

/-! The countably infinite Dovbysh--Sudakov directing ensemble uses
ordinary IID Hilbert vectors. Here their full finite overlap-array law
projects exactly to the capture-score law, including the diagonal-zero
score convention and the query-plus-block reindexing. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCaptureDirectingFullToScore

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCaptureOverlapScoreCoordinates
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalFullToScore
open PureCaptureRandomDirectingScoreArray
open SlowEquilibration.DirectingPhysical
open GaussianReplicaKernel
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {Ξ H : Type*} [MeasurableSpace Ξ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

def directingFullOverlapCoordinates {m : ℕ}
    (σ : Fin m → H) : FullOverlapCoordinates m :=
  fun i j => if i = j then 1 else inner ℝ (σ i) (σ j)

theorem directingFullOverlapCoordinates_continuous {m : ℕ} :
    Continuous (directingFullOverlapCoordinates (H := H) (m := m)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hij : i = j
  · simpa [directingFullOverlapCoordinates, hij] using
      (continuous_const : Continuous (fun _ : Fin m → H => (1 : ℝ)))
  · simpa only [directingFullOverlapCoordinates, hij, ite_false, Function.comp_def]
      using ((continuous_apply i).inner (continuous_apply j))

def directingFullOverlapLaw (d : Measure Ξ) [IsProbabilityMeasure d]
    (G : Kernel Ξ H) [IsMarkovKernel G] (m : ℕ) :
    ProbabilityMeasure (FullOverlapCoordinates m) :=
  ((law d G m).toProbabilityMeasure).map directingFullOverlapCoordinates

def unflattenDirectingReplicas {k T : ℕ}
    (σ : Fin (T*k+1) → H) : H × (Fin T → Fin k → H) :=
  (σ 0, fun b i => σ (companionIndex b i))

theorem unflattenDirectingReplicas_measurable {k T : ℕ} :
    Measurable (unflattenDirectingReplicas (H := H) (k := k) (T := T)) := by
  apply Measurable.prodMk (measurable_pi_apply 0)
  apply Measurable.of_eval
  intro b
  apply Measurable.of_eval
  intro i
  exact measurable_pi_apply (companionIndex b i)

theorem fullScoreProjection_directing {k T : ℕ}
    (σ : Fin (T*k+1) → H) :
    fullScoreProjection (directingFullOverlapCoordinates σ) =
      directingScoreCoordinates (unflattenDirectingReplicas σ) := by
  apply Prod.ext
  · funext b i
    change (if (0 : Fin (T*k+1)) = companionIndex b i then 1 else
      inner ℝ (σ 0) (σ (companionIndex b i))) =
        inner ℝ (σ 0) (σ (companionIndex b i))
    simp [companionIndex_ne_zero b i]
  · funext b i j
    change (if i = j then 0 else
      if companionIndex b i = companionIndex b j then 1 else
        inner ℝ (σ (companionIndex b i)) (σ (companionIndex b j))) =
      (if i = j then 0 else
        inner ℝ (σ (companionIndex b i)) (σ (companionIndex b j)))
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, companionIndex_injective_on_block b hij]

theorem pi_map_unflattenDirectingReplicas {k T : ℕ}
    (ν : Measure H) [IsProbabilityMeasure ν] :
    (Measure.pi (fun _ : Fin (T*k+1) => ν)).map unflattenDirectingReplicas =
      ν.prod (Measure.pi (fun _ : Fin T =>
        Measure.pi (fun _ : Fin k => ν))) := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (T*k+1) => H) 0
  let f : H × (Fin (T*k) → H) → H × (Fin T → Fin k → H) :=
    fun p => (p.1, unflattenTail p.2)
  have hfun : (unflattenDirectingReplicas (H := H) (k := k) (T := T)) = f ∘ e := by
    funext σ
    apply Prod.ext
    · rfl
    · funext b i
      simp [f, e, unflattenDirectingReplicas, unflattenTail,
        companionIndex, MeasurableEquiv.piFinSuccAbove, Fin.tail]
  have hsplit : (Measure.pi (fun _ : Fin (T*k+1) => ν)).map e =
      ν.prod (Measure.pi (fun _ : Fin (T*k) => ν)) := by
    simpa only [Fin.succAbove_zero] using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (T*k+1) => ν) 0).map_eq
  have htail : MeasurePreserving
      (unflattenTail (V := H) (k := k) (T := T))
      (Measure.pi (fun _ : Fin (T*k) => ν))
      (Measure.pi (fun _ : Fin T => Measure.pi (fun _ : Fin k => ν))) :=
    ⟨unflattenTail_measurable, pi_map_unflattenTail ν⟩
  have hprod : (ν.prod (Measure.pi (fun _ : Fin (T*k) => ν))).map f =
      ν.prod (Measure.pi (fun _ : Fin T => Measure.pi (fun _ : Fin k => ν))) :=
    ((MeasurePreserving.id ν).prod htail).map_eq
  have hf : Measurable f :=
    measurable_fst.prodMk (unflattenTail_measurable.comp measurable_snd)
  rw [hfun, ← Measure.map_map hf e.measurable, hsplit, hprod]

theorem directingReplicaLaw_map_unflatten (d : Measure Ξ)
    [IsProbabilityMeasure d] (G : Kernel Ξ H) [IsMarkovKernel G]
    {k T : ℕ} :
    (law d G (T*k+1)).map unflattenDirectingReplicas =
      companionEnsembleLaw d G k T := by
  have hkernel : (iid G (T*k+1)).map unflattenDirectingReplicas =
      companionEnsembleKernel G k T := by
    apply Kernel.ext
    intro ω
    rw [Kernel.map_apply _ unflattenDirectingReplicas_measurable,
      iid_apply, companionEnsembleKernel_apply]
    exact pi_map_unflattenDirectingReplicas (G ω)
  unfold law companionEnsembleLaw
  rw [Measure.map_comp _ _ unflattenDirectingReplicas_measurable, hkernel]

theorem directingFullOverlapLaw_map_score (d : Measure Ξ)
    [IsProbabilityMeasure d] (G : Kernel Ξ H) [IsMarkovKernel G]
    (k T : ℕ) :
    (directingFullOverlapLaw d G (T*k+1)).map fullScoreProjection =
      randomDirectingScoreLaw d G k T := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((law d G (T*k+1)).map directingFullOverlapCoordinates).map
      fullScoreProjection =
    (companionEnsembleLaw d G k T).map directingScoreCoordinates
  rw [Measure.map_map fullScoreProjection_continuous.measurable
    directingFullOverlapCoordinates_continuous.measurable]
  have hcomp : (fullScoreProjection (k := k) (T := T)) ∘
      (directingFullOverlapCoordinates (H := H) (m := T*k+1)) =
      (directingScoreCoordinates (H := H) (k := k) (T := T)) ∘
        unflattenDirectingReplicas := by
    funext σ
    exact fullScoreProjection_directing σ
  rw [hcomp, ← Measure.map_map directingScoreCoordinates_continuous.measurable
    unflattenDirectingReplicas_measurable]
  rw [directingReplicaLaw_map_unflatten]

end SlowEquilibration.PureCaptureDirectingFullToScore
