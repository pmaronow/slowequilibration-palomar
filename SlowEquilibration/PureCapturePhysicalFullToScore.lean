-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalFullOverlapArray
public import Mathlib.Probability.ProductMeasure

/-! Coordinate projection from the full physical overlap array to the
capture score, including the exact IID product law after flattening the
query and companion blocks. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalFullToScore

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFullOverlapArray
open PureCaptureOverlapScoreCoordinates
open PureCaptureScorePortmanteauTransfer
open PureCapturePhysicalFiniteEnsembleTransfer
open PureCapturePhysicalFiniteMeasurability
open PureCapturePhysicalScoreTightness
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def companionIndex {k T : ℕ} (b : Fin T) (i : Fin k) : Fin (T*k+1) :=
  Fin.succ (finProdFinEquiv (b, i))

def unflattenPhysicalReplicas {N k T : ℕ}
    (σ : Fin (T*k+1) → Vector N) : PhysicalEnsemble N k T :=
  (σ 0, fun b i => σ (companionIndex b i))

theorem unflattenPhysicalReplicas_measurable {N k T : ℕ} :
    Measurable (unflattenPhysicalReplicas (N := N) (k := k) (T := T)) := by
  apply Measurable.prodMk (measurable_pi_apply 0)
  apply Measurable.of_eval
  intro b
  apply Measurable.of_eval
  intro i
  exact measurable_pi_apply (companionIndex b i)

def fullScoreProjection {k T : ℕ}
    (c : FullOverlapCoordinates (T*k+1)) : ScoreCoordinates k T :=
  ((fun b i => c 0 (companionIndex b i)),
    (fun b i j => if i = j then 0 else c (companionIndex b i) (companionIndex b j)))

theorem fullScoreProjection_continuous {k T : ℕ} :
    Continuous (fullScoreProjection (k := k) (T := T)) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro b
    apply continuous_pi
    intro i
    exact (continuous_apply (companionIndex b i)).comp (continuous_apply 0)
  · apply continuous_pi
    intro b
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases hij : i = j
    · simpa [fullScoreProjection, hij] using
        (continuous_const : Continuous
          (fun _ : FullOverlapCoordinates (T*k+1) => (0 : ℝ)))
    · simpa only [fullScoreProjection, hij, ite_false, Function.comp_def] using
        ((continuous_apply (companionIndex b j)).comp
          (continuous_apply (companionIndex b i)))

theorem companionIndex_ne_zero {k T : ℕ} (b : Fin T) (i : Fin k) :
    (0 : Fin (T*k+1)) ≠ companionIndex b i := by
  exact (Fin.succ_ne_zero _).symm

theorem companionIndex_injective_on_block {k T : ℕ} (b : Fin T)
    {i j : Fin k} (hij : i ≠ j) :
    companionIndex b i ≠ companionIndex b j := by
  intro heq
  apply hij
  have hprod := finProdFinEquiv.injective (Fin.succ_injective _ heq)
  exact congrArg Prod.snd hprod

theorem fullScoreProjection_physical {N k T : ℕ}
    (σ : Fin (T*k+1) → Vector N) :
    fullScoreProjection (physicalFullOverlapCoordinates σ) =
      physicalScoreCoordinates (unflattenPhysicalReplicas σ) := by
  apply Prod.ext
  · funext b i
    change (if (0 : Fin (T*k+1)) = companionIndex b i then 1 else
      overlap (σ 0) (σ (companionIndex b i))) =
        overlap (σ 0) (σ (companionIndex b i))
    simp [companionIndex_ne_zero b i]
  · funext b i j
    change (if i = j then 0 else
      if companionIndex b i = companionIndex b j then 1 else
        overlap (σ (companionIndex b i)) (σ (companionIndex b j))) =
      (if i = j then 0 else
        overlap (σ (companionIndex b i)) (σ (companionIndex b j)))
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, companionIndex_injective_on_block b hij]

def unflattenTail {V : Type*} {k T : ℕ}
    (σ : Fin (T*k) → V) : Fin T → Fin k → V :=
  fun b i => σ (finProdFinEquiv (b, i))

theorem unflattenTail_measurable {V : Type*} [MeasurableSpace V]
    {k T : ℕ} : Measurable (unflattenTail (V := V) (k := k) (T := T)) := by
  apply Measurable.of_eval
  intro b
  apply Measurable.of_eval
  intro i
  exact measurable_pi_apply (finProdFinEquiv (b, i))

theorem pi_map_unflattenTail {V : Type*} [MeasurableSpace V]
    {k T : ℕ} (ν : Measure V) [IsProbabilityMeasure ν] :
    (Measure.pi (fun _ : Fin (T*k) => ν)).map unflattenTail =
      Measure.pi (fun _ : Fin T => Measure.pi (fun _ : Fin k => ν)) := by
  let e := MeasurableEquiv.piCongrLeft
    (fun _ : Fin T × Fin k => V) (finProdFinEquiv (m := T) (n := k)).symm
  let c := MeasurableEquiv.curry (Fin T) (Fin k) V
  have hfun : (unflattenTail (V := V) (k := k) (T := T)) = (⇑c) ∘ (⇑e) := by
    funext σ b i
    simp [unflattenTail, c, e, MeasurableEquiv.curry,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  have hstep1 : (Measure.pi (fun _ : Fin (T*k) => ν)).map e =
      Measure.pi (fun _ : Fin T × Fin k => ν) :=
    (measurePreserving_piCongrLeft
      (α := fun _ : Fin T × Fin k => V)
      (fun _ : Fin T × Fin k => ν)
      (finProdFinEquiv (m := T) (n := k)).symm).map_eq
  have hstep2 : (Measure.pi (fun _ : Fin T × Fin k => ν)).map c =
      Measure.pi (fun _ : Fin T => Measure.pi (fun _ : Fin k => ν)) := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry
        (fun _ : Fin T => fun _ : Fin k => ν))
  rw [hfun, ← Measure.map_map c.measurable e.measurable, hstep1, hstep2]

theorem pi_map_unflattenPhysicalReplicas {N k T : ℕ}
    (ν : Measure (Vector N)) [IsProbabilityMeasure ν] :
    (Measure.pi (fun _ : Fin (T*k+1) => ν)).map unflattenPhysicalReplicas =
      ν.prod (Measure.pi (fun _ : Fin T =>
        Measure.pi (fun _ : Fin k => ν))) := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (T*k+1) => Vector N) 0
  let f : Vector N × (Fin (T*k) → Vector N) → PhysicalEnsemble N k T :=
    fun p => (p.1, unflattenTail p.2)
  have hfun : (unflattenPhysicalReplicas (N := N) (k := k) (T := T)) = f ∘ e := by
    funext σ
    apply Prod.ext
    · rfl
    · funext b i
      simp [f, e, unflattenPhysicalReplicas, unflattenTail,
        companionIndex, MeasurableEquiv.piFinSuccAbove, Fin.tail]
  have hsplit : (Measure.pi (fun _ : Fin (T*k+1) => ν)).map e =
      ν.prod (Measure.pi (fun _ : Fin (T*k) => ν)) := by
    simpa only [Fin.succAbove_zero] using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (T*k+1) => ν) 0).map_eq
  have htail : MeasurePreserving
      (unflattenTail (V := Vector N) (k := k) (T := T))
      (Measure.pi (fun _ : Fin (T*k) => ν))
      (Measure.pi (fun _ : Fin T => Measure.pi (fun _ : Fin k => ν))) :=
    ⟨unflattenTail_measurable, pi_map_unflattenTail ν⟩
  have hprod : (ν.prod (Measure.pi (fun _ : Fin (T*k) => ν))).map f =
      ν.prod (Measure.pi (fun _ : Fin T => Measure.pi (fun _ : Fin k => ν))) :=
    ((MeasurePreserving.id ν).prod htail).map_eq
  have hf : Measurable f :=
    measurable_fst.prodMk (unflattenTail_measurable.comp measurable_snd)
  rw [hfun, ← Measure.map_map hf e.measurable, hsplit, hprod]

theorem physicalReplicaLaw_map_unflatten {n k T : ℕ}
    (μ : FiniteMixture) (β : ℝ) :
    (physicalReplicaLaw (n := n) (m := T*k+1) μ β).map
      unflattenPhysicalReplicas =
    annealedPhysicalEnsembleLaw (n := n) (k := k) (T := T) μ β := by
  let G := allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β
  have hkernel : (GaussianReplicaKernel.iid G (T*k+1)).map
      unflattenPhysicalReplicas =
      physicalEnsembleKernel (n := n) (k := k) (T := T) μ β := by
    apply Kernel.ext
    intro J
    rw [Kernel.map_apply _ unflattenPhysicalReplicas_measurable,
      GaussianReplicaKernel.iid_apply, physicalEnsembleKernel_apply]
    let : IsProbabilityMeasure
        (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)) :=
      gibbsLaw_probability (by omega) β
        (field_contDiff (mixtureCoefficients μ) J).continuous
    simpa only [G, allDimensionGibbsKernel_apply, physicalEnsembleLaw] using
      (pi_map_unflattenPhysicalReplicas
        (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)))
  unfold physicalReplicaLaw GaussianReplicaKernel.law annealedPhysicalEnsembleLaw
  rw [Measure.map_comp _ _ unflattenPhysicalReplicas_measurable, hkernel]

theorem physicalFullOverlapLaw_map_score {n k T : ℕ}
    (μ : FiniteMixture) (β : ℝ) :
    (physicalFullOverlapLaw (n := n) (m := T*k+1) μ β).map
      fullScoreProjection =
    annealedPhysicalScoreLaw (n := n) (k := k) (T := T) μ β := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((physicalReplicaLaw (n := n) (m := T*k+1) μ β).map
    physicalFullOverlapCoordinates).map fullScoreProjection =
    (annealedPhysicalEnsembleLaw (n := n) (k := k) (T := T) μ β).map
      physicalScoreCoordinates
  rw [Measure.map_map fullScoreProjection_continuous.measurable
    physicalFullOverlapCoordinates_continuous.measurable]
  have hcomp : (fullScoreProjection (k := k) (T := T)) ∘
      (physicalFullOverlapCoordinates (N := n+2) (m := T*k+1)) =
      (physicalScoreCoordinates (N := n+2) (k := k) (T := T)) ∘
        unflattenPhysicalReplicas := by
    funext σ
    exact fullScoreProjection_physical σ
  rw [hcomp, ← Measure.map_map physicalScoreCoordinates_continuous.measurable
    unflattenPhysicalReplicas_measurable]
  rw [physicalReplicaLaw_map_unflatten]

def fullToScoreArray (k : ℕ) (x : FullOverlapLawArray) : ScoreLawArray k :=
  fun T => (x (T*k+1)).map fullScoreProjection

theorem fullToScoreArray_continuous (k : ℕ) :
    Continuous (fullToScoreArray k) := by
  apply continuous_pi
  intro T
  exact (ProbabilityMeasure.continuous_map fullScoreProjection_continuous).comp
    (continuous_apply (T*k+1))

theorem fullToScoreArray_physical (k : ℕ)
    (μ : FiniteMixture) (β : ℝ) (n : ℕ) :
    fullToScoreArray k (physicalFullOverlapLawArray μ β n) =
      annealedPhysicalScoreLawArray k μ β n := by
  funext T
  exact physicalFullOverlapLaw_map_score μ β

theorem fullToScoreArray_maps_physical_limits (k : ℕ)
    (μ : FiniteMixture) (β : ℝ)
    {x : FullOverlapLawArray} (hx : x ∈ physicalFullOverlapArrayLimitSet μ β) :
    fullToScoreArray k x ∈ physicalScoreLawArrayLimitSet k μ β := by
  have hclosed : IsClosed
      (fullToScoreArray k ⁻¹' physicalScoreLawArrayLimitSet k μ β) :=
    IsClosed.preimage (fullToScoreArray_continuous k)
      (physicalScoreLawArrayLimitSet_compact k μ β).isClosed
  apply closure_minimal _ hclosed hx
  rintro x ⟨n, rfl⟩
  change fullToScoreArray k (physicalFullOverlapLawArray μ β n) ∈
    physicalScoreLawArrayLimitSet k μ β
  rw [fullToScoreArray_physical]
  exact subset_closure (Set.mem_range.mpr ⟨n, rfl⟩)

/-- Every simultaneous physical score weak limit lifts to an actual
exchangeable positive-semidefinite full overlap-array weak limit. -/
theorem physicalScoreLimit_exists_fullOverlapLimit (k : ℕ)
    (μ : FiniteMixture) (β : ℝ)
    {y : ScoreLawArray k} (hy : y ∈ physicalScoreLawArrayLimitSet k μ β) :
    ∃ x ∈ physicalFullOverlapArrayLimitSet μ β, fullToScoreArray k x = y := by
  have hclosed : IsClosed
      (fullToScoreArray k '' physicalFullOverlapArrayLimitSet μ β) :=
    ((physicalFullOverlapArrayLimitSet_compact μ β).image
      (fullToScoreArray_continuous k)).isClosed
  have hsub : Set.range (annealedPhysicalScoreLawArray k μ β) ⊆
      fullToScoreArray k '' physicalFullOverlapArrayLimitSet μ β := by
    rintro _ ⟨n, rfl⟩
    refine ⟨physicalFullOverlapLawArray μ β n,
      subset_closure (Set.mem_range.mpr ⟨n, rfl⟩), ?_⟩
    exact fullToScoreArray_physical k μ β n
  exact closure_minimal hsub hclosed hy

end SlowEquilibration.PureCapturePhysicalFullToScore
