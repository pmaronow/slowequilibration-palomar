module

public import SphericalAging.BoundedItoMultiplier
public import FourPapersCommon.ContinuousAEAdaptedPredictable

public section

/-!
# Identification of actual weighted left sums

This module connects pathwise uniform left sums to the constructed
full-filtration Itô operator. Multipliers are bounded, strongly adapted,
and almost surely continuous; continuity is not assumed on null paths.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.WeightedItoSums
open HardSphereDynamics VectorIto BoundedItoMultiplier FourPapersCommon
set_option maxHeartbeats 1200000

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def predictableProduct {G : ℝ≥0 × Ω → ℝ}
    (hG : AEStronglyMeasurable[𝓕.predictable] G (nonnegativeLebesgueMeasure.prod P))
    (K : ℝ≥0) (hK : ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ‖G p‖ ≤ K)
    (U : PredictableProcessL2 𝓕 P) : PredictableProcessL2 𝓕 P := by
  let V := boundedMulCLM (hG.mono (predictable_le_prod 𝓕)) K hK (U : TimeProcessL2 P)
  refine ⟨V, ?_⟩
  exact (hG.mul (lpMeas.aestronglyMeasurable U)).congr
    (boundedMulCLM_coe (hG.mono (predictable_le_prod 𝓕)) K hK (U : TimeProcessL2 P)).symm

omit [IsProbabilityMeasure P] in
lemma predictableProduct_coe {G : ℝ≥0 × Ω → ℝ}
    (hG : AEStronglyMeasurable[𝓕.predictable] G (nonnegativeLebesgueMeasure.prod P))
    (K : ℝ≥0) (hK : ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ‖G p‖ ≤ K)
    (U : PredictableProcessL2 𝓕 P) :
    (predictableProduct hG K hK U : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p => G p * (U : ℝ≥0 × Ω → ℝ) p :=
  boundedMulCLM_coe (hG.mono (predictable_le_prod 𝓕)) K hK (U : TimeProcessL2 P)

omit [IsProbabilityMeasure P] in
/-- Dominated convergence for bounded predictable multipliers on an actual
L² integrand. No integrability of the multiplier over infinite time is needed. -/
theorem predictableProduct_tendsto {G : ℕ → ℝ≥0 × Ω → ℝ} {g : ℝ≥0 × Ω → ℝ}
    (hG : ∀ n, AEStronglyMeasurable[𝓕.predictable] (G n) (nonnegativeLebesgueMeasure.prod P))
    (hg : AEStronglyMeasurable[𝓕.predictable] g (nonnegativeLebesgueMeasure.prod P))
    (K : ℝ≥0) (hK : ∀ n, ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ‖G n p‖ ≤ K)
    (hk : ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ‖g p‖ ≤ K)
    (hlim : ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, Tendsto (fun n => G n p) atTop (𝓝 (g p)))
    (U : PredictableProcessL2 𝓕 P) :
    Tendsto (fun n => predictableProduct (hG n) K (hK n) U) atTop
      (𝓝 (predictableProduct hg K hk U)) := by
  let μ := nonnegativeLebesgueMeasure.prod P
  let f (n : ℕ) (p : ℝ≥0 × Ω) := G n p * (U : ℝ≥0 × Ω → ℝ) p
  let v (p : ℝ≥0 × Ω) := g p * (U : ℝ≥0 × Ω → ℝ) p
  have hf (n : ℕ) : MemLp (f n) 2 μ :=
    bounded_product_memLp ((hG n).mono (predictable_le_prod 𝓕)) K (hK n) (U : TimeProcessL2 P)
  have hv : MemLp v 2 μ :=
    bounded_product_memLp (hg.mono (predictable_le_prod 𝓕)) K hk (U : TimeProcessL2 P)
  have hd : Tendsto (fun n => ∫ p, (f n p - v p)^2 ∂μ) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (μ := μ)
      (f := fun _ => (0 : ℝ)) (F := fun n p => (f n p - v p)^2)
      (fun p => (2 * (K : ℝ))^2 * (U : ℝ≥0 × Ω → ℝ) p ^ 2)
      (fun n => by convert ((hf n).aestronglyMeasurable.sub hv.aestronglyMeasurable).pow 2 using 1)
      ((Lp.memLp (U : TimeProcessL2 P)).integrable_sq.const_mul ((2 * (K : ℝ))^2))
      (fun n => by
        filter_upwards [hK n, hk] with p hn hp
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have he : ‖f n p - v p‖ ≤ 2 * (K : ℝ) * ‖(U : ℝ≥0 × Ω → ℝ) p‖ := by
          unfold f v
          rw [← sub_mul, norm_mul]
          exact mul_le_mul_of_nonneg_right
            ((norm_sub_le _ _).trans (by linarith)) (norm_nonneg _)
        have hs := pow_le_pow_left₀ (norm_nonneg _) he 2
        simpa only [mul_pow, Real.norm_eq_abs, sq_abs] using hs)
      (by
        filter_upwards [hlim] with p hp
        simpa only [f, v, sub_self, zero_pow (by norm_num : 2 ≠ 0)] using
          (((hp.mul_const ((U : ℝ≥0 × Ω → ℝ) p)).sub_const (v p)).pow 2))
    simpa only [integral_zero] using hh
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hd
  have he (n : ℕ) : ‖predictableProduct (hG n) K (hK n) U - predictableProduct hg K hk U‖ =
      Real.sqrt (∫ p, (f n p - v p)^2 ∂μ) := by
    change ‖(hf n).toLp (f n) - hv.toLp v‖ = _
    rw [← norm_sq_toLp_sub (hf n) hv, Real.sqrt_sq (norm_nonneg _)]
  simpa only [Function.comp_def, ← he, Real.sqrt_zero] using hsqrt

lemma leftStep_bound (H : ℝ≥0 → Ω → ℝ) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) (n : ℕ) (p : ℝ≥0 × Ω) :
    ‖continuousAdaptedLeftStep 𝓕 H T (n+1) p‖ ≤ K := by
  have h := continuousAdaptedLeftStep_norm_le 𝓕 H K hK T n p
  by_cases hp : p ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)
  · simpa only [indicator_of_mem hp] using h
  · rw [indicator_of_notMem hp] at h
    exact h.trans K.coe_nonneg

omit [MeasurableSpace Ω] in
lemma timeCut_bound (H : ℝ≥0 → Ω → ℝ) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) (p : ℝ≥0 × Ω) :
    ‖continuousAdaptedTimeCut H T p‖ ≤ K := by
  unfold continuousAdaptedTimeCut
  split_ifs
  · exact hK _ _
  · simp

@[expose] def weightedIntegrand (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H)
    (hcts : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) (U : PredictableProcessL2 𝓕 P) :
    PredictableProcessL2 𝓕 P := predictableProduct
      (aestronglyMeasurable_aeContinuousAdaptedTimeCut 𝓕 H hH hcts T) K
      (.of_forall (timeCut_bound H K hK T)) U

@[expose] def weightedStepIntegrand (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H)
    (K : ℝ≥0) (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0)
    (U : PredictableProcessL2 𝓕 P) (n : ℕ) : PredictableProcessL2 𝓕 P :=
  predictableProduct (stronglyMeasurable_continuousAdaptedLeftStep 𝓕 H hH T (n+1)).aestronglyMeasurable
    K (.of_forall (leftStep_bound H K hK T n)) U

theorem weightedStepIntegrand_tendsto (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H)
    (hcts : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) (U : PredictableProcessL2 𝓕 P) :
    Tendsto (weightedStepIntegrand H hH K hK T U) atTop
      (𝓝 (weightedIntegrand H hH hcts K hK T U)) := by
  apply predictableProduct_tendsto
  have hc := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hcts
  filter_upwards [hc] with p hp
  exact continuousAdaptedLeftStep_tendsto_at 𝓕 H T p hp

@[expose] def weightedLeftSum (H M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, H (uniformPartitionTime T n k) ω *
    (M (uniformPartitionTime T n (k+1)) ω - M (uniformPartitionTime T n k) ω)

omit [IsProbabilityMeasure P] in
theorem weightedStepIntegrand_eq_sum (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H)
    (K : ℝ≥0) (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0)
    (U : PredictableProcessL2 𝓕 P) (n : ℕ) :
    weightedStepIntegrand H hH K hK T U n =
      ∑ k ∈ Finset.range (n+1), predictableMulCLM
        (uniformPartitionTime T (n+1) (k+1))
        (hH (uniformPartitionTime T (n+1) k)) K (hK _) U := by
  classical
  apply Subtype.ext
  apply Lp.ext
  let E : ℕ → TimeProcessL2 P := fun k => (predictableMulCLM
    (uniformPartitionTime T (n+1) (k+1))
    (hH (uniformPartitionTime T (n+1) k)) K (hK _) U : TimeProcessL2 P)
  have he (k : ℕ) : (E k : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p => elementaryRepresentative 𝓕 (uniformPartitionTime T (n+1) k)
        (uniformPartitionTime T (n+1) (k+1)) (H (uniformPartitionTime T (n+1) k)) p *
          (U : ℝ≥0 × Ω → ℝ) p := predictableMulCLM_coe _ _ _ _ _
  have hs := eventuallyEq_sum (s := Finset.range (n+1)) (fun k _ => he k)
  simp only [Submodule.coe_sum]
  change (weightedStepIntegrand H hH K hK T U n : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
    ((∑ k ∈ Finset.range (n+1), E k : TimeProcessL2 P) : ℝ≥0 × Ω → ℝ)
  filter_upwards [predictableProduct_coe
      (stronglyMeasurable_continuousAdaptedLeftStep 𝓕 H hH T (n+1)).aestronglyMeasurable
        K (.of_forall (leftStep_bound H K hK T n)) U,
    Lp.coeFn_finsetSum (Finset.range (n+1)) E, hs] with p hl hp hs
  change (predictableProduct _ K _ U : ℝ≥0 × Ω → ℝ) p = _
  rw [hl, hp]
  simp only [Finset.sum_apply] at hs ⊢
  rw [hs]
  simp only [continuousAdaptedLeftStep, Finset.sum_mul]

lemma coordinateIto_timeSlice_coe (D : BrownianDriver N P 𝓕) (i : Fin N)
    (a b : ℝ≥0) (U : PredictableProcessL2 𝓕 P) :
    (coordinateIto D i (FourPapersCommon.FilteredBrownian.predictableTimeSlice 𝓕 a b U) : Ω → ℝ)
      =ᵐ[P] fun ω => coordinateProcess D i U b ω - coordinateProcess D i U a ω := by
  let I := FourPapersCommon.FilteredBrownian.naturalItoProcess
    (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) U
  change ((coordinateIto D i) _ : Ω → ℝ) =ᵐ[P] _
  have he : coordinateIto D i (FourPapersCommon.FilteredBrownian.predictableTimeSlice 𝓕 a b U) =
      I b - I a := (FourPapersCommon.FilteredBrownian.naturalItoProcess_sub
        (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) U a b).symm
  rw [he]
  filter_upwards [Lp.coeFn_sub (I b) (I a),
    FourPapersCommon.FilteredBrownian.naturalItoProcess_ae_eq_representative
      (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) U b,
    FourPapersCommon.FilteredBrownian.naturalItoProcess_ae_eq_representative
      (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) U a]
    with ω hsub hb ha
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hb, ha]
  rfl

/-- Exact finite-sum identification before passing to the limit. -/
theorem coordinateIto_weightedStep_coe (D : BrownianDriver N P 𝓕) (i : Fin N)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H)
    (K : ℝ≥0) (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0)
    (U : PredictableProcessL2 𝓕 P) (n : ℕ) :
    (coordinateIto D i (weightedStepIntegrand H hH K hK T U n) : Ω → ℝ) =ᵐ[P]
      weightedLeftSum H (coordinateProcess D i U) T (n+1) := by
  classical
  let A (k : ℕ) : RandomL2 P := coordinateIto D i (predictableMulCLM
    (uniformPartitionTime T (n+1) (k+1))
    (hH (uniformPartitionTime T (n+1) k)) K (hK _) U)
  have he (k : ℕ) : (A k : Ω → ℝ) =ᵐ[P] fun ω => H (uniformPartitionTime T (n+1) k) ω *
      (coordinateProcess D i U (uniformPartitionTime T (n+1) (k+1)) ω -
        coordinateProcess D i U (uniformPartitionTime T (n+1) k) ω) := by
    unfold A
    rw [coordinateIto_mul D i ((monotone_uniformPartitionTime T (n+1)) (Nat.le_succ k))]
    filter_upwards [boundedMulCLM_coe
      ((hH (uniformPartitionTime T (n+1) k)).mono (𝓕.le _)).aestronglyMeasurable K
      (.of_forall (hK _))
      (coordinateIto D i (FourPapersCommon.FilteredBrownian.predictableTimeSlice 𝓕
        (uniformPartitionTime T (n+1) k) (uniformPartitionTime T (n+1) (k+1)) U)),
      coordinateIto_timeSlice_coe D i (uniformPartitionTime T (n+1) k)
        (uniformPartitionTime T (n+1) (k+1)) U] with ω hm hi
    rw [hm, hi]
  have hid : coordinateIto D i (weightedStepIntegrand H hH K hK T U n) =
      ∑ k ∈ Finset.range (n+1), A k := by
    rw [weightedStepIntegrand_eq_sum, map_sum]
  rw [hid]
  have hs := eventuallyEq_sum (s := Finset.range (n+1)) (fun k _ => he k)
  filter_upwards [Lp.coeFn_finsetSum (Finset.range (n+1)) A, hs] with ω hsum hs
  rw [hsum]
  simpa only [Finset.sum_apply, weightedLeftSum] using hs

/-- The limit of weighted increments of the constructed scalar integral
is the constructed integral of the actual weighted predictable coefficient. -/
theorem coordinate_weightedLeftSum_tendsto (D : BrownianDriver N P 𝓕) (i : Fin N)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H)
    (hcts : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) (U : PredictableProcessL2 𝓕 P) :
    TendstoInMeasure P (fun n => weightedLeftSum H (coordinateProcess D i U) T (n+1)) atTop
      (coordinateIto D i (weightedIntegrand H hH hcts K hK T U)) := by
  have ht := (coordinateIto D i).continuous.continuousAt.tendsto.comp
    (weightedStepIntegrand_tendsto H hH hcts K hK T U)
  exact TendstoInMeasure.congr_left (coordinateIto_weightedStep_coe D i H hH K hK T U)
    (tendstoInMeasure_of_tendsto_Lp ht)

lemma weightedLeftSum_vectorProcess (D : BrownianDriver N P 𝓕)
    (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (U : Fin N → PredictableProcessL2 𝓕 P)
    (n : ℕ) (ω : Ω) :
    weightedLeftSum H (vectorProcess D U) T n ω =
      ∑ i, weightedLeftSum H (coordinateProcess D i (U i)) T n ω := by
  classical
  unfold weightedLeftSum vectorProcess
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_comm

theorem vector_weightedLeftSum_tendsto (D : BrownianDriver N P 𝓕)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H)
    (hcts : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) (U : Fin N → PredictableProcessL2 𝓕 P) :
    TendstoInMeasure P (fun n => weightedLeftSum H (vectorProcess D U) T (n+1)) atTop
      (vectorIto D (fun i => weightedIntegrand H hH hcts K hK T (U i))) := by
  have ht := VectorItoFormula.tendstoInMeasure_finsetSum Finset.univ
    (fun i n => weightedLeftSum H (coordinateProcess D i (U i)) T (n+1))
    (fun i ω => (coordinateIto D i (weightedIntegrand H hH hcts K hK T (U i)) : Ω → ℝ) ω)
    (fun i _ => coordinate_weightedLeftSum_tendsto D i H hH hcts K hK T (U i))
  apply ht.congr
  · intro n
    exact Eventually.of_forall (fun ω => (weightedLeftSum_vectorProcess D H T U (n+1) ω).symm)
  · filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun i => coordinateIto D i (weightedIntegrand H hH hcts K hK T (U i)))] with ω hω
    simpa only [Finset.sum_apply, vectorIto] using hω.symm

omit [IsProbabilityMeasure P] in
lemma weightedLeftSum_congr {M M' : ℝ≥0 → Ω → ℝ} (h : ∀ s, M s =ᵐ[P] M' s)
    (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) :
    weightedLeftSum H M T n =ᵐ[P] weightedLeftSum H M' T n := by
  have hall := ae_all_iff.mpr (fun k : ℕ => h (uniformPartitionTime T n k))
  filter_upwards [hall] with ω hω
  unfold weightedLeftSum
  exact Finset.sum_congr rfl (fun k _ => by rw [hω (k+1), hω k])

/-- The identification survives the genuine fixed-time modification used
to realize continuous martingale paths. -/
theorem vector_weightedLeftSum_modification_tendsto (D : BrownianDriver N P 𝓕)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H)
    (hcts : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) (U : Fin N → PredictableProcessL2 𝓕 P)
    (M : ℝ≥0 → Ω → ℝ) (hM : ∀ s, vectorProcess D U s =ᵐ[P] M s) :
    TendstoInMeasure P (fun n => weightedLeftSum H M T (n+1)) atTop
      (vectorIto D (fun i => weightedIntegrand H hH hcts K hK T (U i))) :=
  TendstoInMeasure.congr_left (fun n => weightedLeftSum_congr hM H T (n+1))
    (vector_weightedLeftSum_tendsto D H hH hcts K hK T U)

end SphericalAging.WeightedItoSums
