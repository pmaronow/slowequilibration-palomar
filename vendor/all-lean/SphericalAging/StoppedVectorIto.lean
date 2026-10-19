module

public import SphericalAging.RadialItoRepresentation
public import StochasticCalculus.PartitionStoppingTime

public section

/-! Genuine stopping of constructed full-filtration Itô integrals.
The bounded stopping rule is rounded upward on deterministic partitions.
Each finite identity follows from the proved adapted multiplier theorem;
the limiting predictable coefficient includes the stopping endpoint, which
has no effect on Lebesgue time integration. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.StoppedVectorIto
open HardSphereDynamics VectorIto WeightedItoSums FourPapersCommon
set_option maxHeartbeats 1400000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def beforeStop (τ : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ := fun s ω => if s < τ ω then 1 else 0

@[expose] def stoppedTimeCoefficient (τ : Ω → ℝ≥0) (T : ℝ≥0) (p : ℝ≥0 × Ω) : ℝ :=
  if p.1 ∈ Ioc 0 T ∧ p.1 ≤ τ p.2 then 1 else 0

lemma stronglyAdapted_beforeStop {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) :
    StronglyAdapted 𝓕 (beforeStop τ) := by
  intro s
  have hs : MeasurableSet[𝓕 s] {ω | s < τ ω} := by
    have h := (hτ s).compl
    convert h using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, WithTop.coe_le_coe, not_le]
  exact stronglyMeasurable_const.piecewise hs stronglyMeasurable_const

omit [MeasurableSpace Ω] in
lemma beforeStop_bound (τ : Ω → ℝ≥0) : ∀ s ω, ‖beforeStop τ s ω‖ ≤ (1 : ℝ≥0) := by
  intro s ω
  unfold beforeStop
  split_ifs <;> norm_num

omit [MeasurableSpace Ω] in
lemma stoppedTimeCoefficient_bound (τ : Ω → ℝ≥0) (T : ℝ≥0) (p : ℝ≥0 × Ω) :
    ‖stoppedTimeCoefficient τ T p‖ ≤ (1 : ℝ≥0) := by
  unfold stoppedTimeCoefficient
  split_ifs <;> norm_num

theorem beforeStop_leftStep_tendsto (τ : Ω → ℝ≥0) (T : ℝ≥0) (p : ℝ≥0 × Ω) :
    Tendsto (fun n => continuousAdaptedLeftStep 𝓕 (beforeStop τ) T (n+1) p) atTop
      (𝓝 (stoppedTimeCoefficient τ T p)) := by
  classical
  by_cases hp : p.1 ∈ Ioc 0 T
  · have hcell (n : ℕ) : ∃ i < n+1, p.1 ∈ Ioc (uniformPartitionTime T (n+1) i)
        (uniformPartitionTime T (n+1) (i+1)) := by
      apply exists_partition_cell
      simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        mul_div_cancel_right₀ T (by positivity : ((n+1 : ℕ) : ℝ≥0) ≠ 0)] using hp
    by_cases hstop : p.1 ≤ τ p.2
    · have he (n : ℕ) : continuousAdaptedLeftStep 𝓕 (beforeStop τ) T (n+1) p = 1 := by
        obtain ⟨i, hi, hc⟩ := hcell n
        rw [continuousAdaptedLeftStep_of_cell 𝓕 (beforeStop τ) T hi p hc]
        exact ite_eq_left (hc.1.trans_le hstop)
      simp only [he, stoppedTimeCoefficient, hp, hstop, and_self, ite_true]
      exact tendsto_const_nhds
    · have hgap : 0 < (p.1 : ℝ) - (τ p.2 : ℝ) := by
        have hlt : τ p.2 < p.1 := lt_of_not_ge hstop
        exact sub_pos.mpr hlt
      have hmesh : Tendsto (fun n : ℕ => ((T / ((n+1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
        have hn : Tendsto (fun n : ℕ => T / ((n+1 : ℕ) : ℝ≥0)) atTop (𝓝 0) :=
          (Filter.tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat T)
        simpa only [Function.comp_def, NNReal.coe_zero] using
          NNReal.continuous_coe.continuousAt.tendsto.comp hn
      have he : (fun n => continuousAdaptedLeftStep 𝓕 (beforeStop τ) T (n+1) p) =ᶠ[atTop] fun _ => 0 := by
        filter_upwards [hmesh.eventually (eventually_lt_nhds hgap)] with n hn
        obtain ⟨i, hi, hc⟩ := hcell n
        rw [continuousAdaptedLeftStep_of_cell 𝓕 (beforeStop τ) T hi p hc]
        have hwidth : (uniformPartitionTime T (n+1) (i+1) : ℝ) -
            (uniformPartitionTime T (n+1) i : ℝ) = (T / ((n+1 : ℕ) : ℝ≥0) : ℝ) := by
          simp only [uniformPartitionTime, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
            Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
          ring
        have hr : (p.1 : ℝ) ≤ uniformPartitionTime T (n+1) (i+1) := hc.2
        have hleft : ¬ uniformPartitionTime T (n+1) i < τ p.2 := by
          intro hl
          have hl' : (uniformPartitionTime T (n+1) i : ℝ) < τ p.2 := hl
          rw [NNReal.coe_div] at hn
          linarith
        exact ite_eq_right hleft
      rw [tendsto_congr' he]
      simp only [stoppedTimeCoefficient, hp, hstop, and_false, ite_false]
      exact tendsto_const_nhds
  · have he (n : ℕ) : continuousAdaptedLeftStep 𝓕 (beforeStop τ) T (n+1) p = 0 :=
      continuousAdaptedLeftStep_off 𝓕 (beforeStop τ) T (Nat.zero_lt_succ n) p hp
    simp only [he, stoppedTimeCoefficient, hp, false_and, ite_false]
    exact tendsto_const_nhds

lemma stronglyMeasurable_stoppedTimeCoefficient {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) (T : ℝ≥0) :
    StronglyMeasurable[𝓕.predictable] (stoppedTimeCoefficient τ T) := by
  apply stronglyMeasurable_of_tendsto atTop
    (fun n => stronglyMeasurable_continuousAdaptedLeftStep 𝓕 (beforeStop τ)
      (stronglyAdapted_beforeStop hτ) T (n+1))
  exact tendsto_pi_nhds.mpr (beforeStop_leftStep_tendsto τ T)

@[expose] def stoppedIntegrand {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) (T : ℝ≥0)
    (U : PredictableProcessL2 𝓕 P) : PredictableProcessL2 𝓕 P :=
  predictableProduct (stronglyMeasurable_stoppedTimeCoefficient hτ T).aestronglyMeasurable 1
    (.of_forall (stoppedTimeCoefficient_bound τ T)) U

omit [IsProbabilityMeasure P] in
lemma stoppedIntegrand_coe {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) (T : ℝ≥0)
    (U : PredictableProcessL2 𝓕 P) :
    (stoppedIntegrand hτ T U : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p => stoppedTimeCoefficient τ T p * (U : ℝ≥0 × Ω → ℝ) p :=
  predictableProduct_coe _ _ _ _

theorem stoppedIntegrand_bracket {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) (T : ℝ≥0)
    (hbound : ∀ ω, τ ω ≤ T) (U : PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    FilteredQuadraticVariation.predictableQuadraticVariation (stoppedIntegrand hτ T U) t =ᵐ[P]
      fun ω => ∫ s in Ioc 0 (min t (τ ω)), (U : ℝ≥0 × Ω → ℝ) (s, ω)^2 ∂nonnegativeLebesgueMeasure := by
  have hswap := (Measure.measurePreserving_swap (μ := P) (ν := nonnegativeLebesgueMeasure)).quasiMeasurePreserving.ae_eq_comp
    (stoppedIntegrand_coe hτ T U)
  have hsections := Measure.ae_ae_of_ae_prod hswap
  filter_upwards [hsections] with ω hω
  unfold FilteredQuadraticVariation.predictableQuadraticVariation
  calc
    (∫ s in Ioc (0 : ℝ≥0) t, (stoppedIntegrand hτ T U : ℝ≥0 × Ω → ℝ) (s, ω)^2
      ∂nonnegativeLebesgueMeasure) =
        ∫ s in Ioc (0 : ℝ≥0) t, (stoppedTimeCoefficient τ T (s, ω) *
          (U : ℝ≥0 × Ω → ℝ) (s, ω))^2 ∂nonnegativeLebesgueMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hω] with s hs
      have hs' : (stoppedIntegrand hτ T U : ℝ≥0 × Ω → ℝ) (s, ω) =
          stoppedTimeCoefficient τ T (s, ω) * (U : ℝ≥0 × Ω → ℝ) (s, ω) := by
        simpa only [Function.comp_apply, Prod.swap_prod_mk] using hs
      rw [hs']
    _ = _ := by
      rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      exact .of_forall (fun s => by
        have he : s ∈ Ioc (0 : ℝ≥0) t ∧ s ∈ Ioc 0 T ∧ s ≤ τ ω ↔
            s ∈ Ioc 0 (min t (τ ω)) := by
          constructor
          · rintro ⟨hs, _, hτs⟩
            exact ⟨hs.1, le_min hs.2 hτs⟩
          · intro hs
            exact ⟨⟨hs.1, hs.2.trans (min_le_left _ _)⟩,
              ⟨hs.1, (hs.2.trans (min_le_right _ _)).trans (hbound ω)⟩,
              hs.2.trans (min_le_right _ _)⟩
        by_cases hs : s ∈ Ioc (0 : ℝ≥0) t
        · by_cases hσ : s ∈ Ioc (0 : ℝ≥0) T ∧ s ≤ τ ω
          · have hm := he.mp ⟨hs, hσ⟩
            simp only [indicator_of_mem hs, indicator_of_mem hm, stoppedTimeCoefficient,
              hσ, and_self, ite_true, one_mul]
          · have hm : s ∉ Ioc (0 : ℝ≥0) (min t (τ ω)) := fun hm => hσ (he.mpr hm).2
            simp only [indicator_of_mem hs, indicator_of_notMem hm, stoppedTimeCoefficient,
              hσ, ite_false, zero_mul, zero_pow (by norm_num : 2 ≠ 0)]
        · have hm : s ∉ Ioc (0 : ℝ≥0) (min t (τ ω)) := fun hm => hs (he.mpr hm).1
          simp only [indicator_of_notMem hs, indicator_of_notMem hm])

omit [IsProbabilityMeasure P] in
theorem stoppedStepIntegrand_tendsto {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) (T : ℝ≥0)
    (U : PredictableProcessL2 𝓕 P) :
    Tendsto (weightedStepIntegrand (beforeStop τ) (stronglyAdapted_beforeStop hτ) 1
      (beforeStop_bound τ) T U) atTop (𝓝 (stoppedIntegrand hτ T U)) := by
  apply predictableProduct_tendsto
  exact .of_forall (beforeStop_leftStep_tendsto τ T)

@[expose] def ceilTime (τ : Ω → ℝ≥0) (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  uniformPartitionTime T (n+1) (uniformPartitionCeilIndex (fun ω => (τ ω : WithTop ℝ≥0))
    T (n+1) (Nat.zero_lt_succ n) (fun ω => WithTop.coe_le_coe.mpr (hbound ω)) ω)

omit [MeasurableSpace Ω] in
theorem ceilTime_tendsto (τ : Ω → ℝ≥0) (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) (ω : Ω) :
    Tendsto (fun n => ceilTime τ T hbound n ω) atTop (𝓝 (τ ω)) := by
  have ht := tendsto_uniformPartitionCeilStoppingTime (fun ω => (τ ω : WithTop ℝ≥0)) T
    (fun ω => WithTop.coe_le_coe.mpr (hbound ω)) ω
  have hu := (WithTop.tendsto_untopA (a := (τ ω : WithTop ℝ≥0)) WithTop.coe_ne_top).comp ht
  have hcoe (a : ℝ≥0) : (a : WithTop ℝ≥0).untopA = a := by
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  simpa only [Function.comp_def, uniformPartitionCeilStoppingTime, ceilTime,
    hcoe] using hu

omit [MeasurableSpace Ω] in
theorem beforeStop_weightedLeftSum (τ : Ω → ℝ≥0) (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T)
    (M : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    weightedLeftSum (beforeStop τ) M T (n+1) ω = M (ceilTime τ T hbound n ω) ω - M 0 ω := by
  classical
  let σ : Ω → WithTop ℝ≥0 := fun ω => (τ ω : WithTop ℝ≥0)
  let hb : ∀ ω, σ ω ≤ (T : WithTop ℝ≥0) := fun ω => WithTop.coe_le_coe.mpr (hbound ω)
  let j := uniformPartitionCeilIndex σ T (n+1) (Nat.zero_lt_succ n) hb ω
  have hj : j ≤ n+1 := uniformPartitionCeilIndex_le σ T (n+1) (Nat.zero_lt_succ n) hb ω
  have hlt (k : ℕ) : k < j ↔ uniformPartitionTime T (n+1) k < τ ω := by
    constructor
    · intro hk
      have hnot : ¬ σ ω ≤ (uniformPartitionTime T (n+1) k : WithTop ℝ≥0) := by
        exact Nat.find_min (exists_uniformPartitionTime_ge σ T (n+1) (Nat.zero_lt_succ n) hb ω) hk
      exact WithTop.coe_lt_coe.mp (lt_of_not_ge hnot)
    · intro hk
      by_contra hkj
      have hle := uniformPartitionCeilIndex_spec σ T (n+1) (Nat.zero_lt_succ n) hb ω
      have hmono := (monotone_uniformPartitionTime T (n+1)) (le_of_not_gt hkj)
      have hτk : τ ω ≤ uniformPartitionTime T (n+1) k :=
        (WithTop.coe_le_coe.mp hle).trans hmono
      exact not_lt_of_ge hτk hk
  let f (k : ℕ) := beforeStop τ (uniformPartitionTime T (n+1) k) ω *
    (M (uniformPartitionTime T (n+1) (k+1)) ω - M (uniformPartitionTime T (n+1) k) ω)
  have hs : (∑ k ∈ Finset.range j, f k) = ∑ k ∈ Finset.range (n+1), f k :=
    Finset.sum_subset (Finset.range_mono hj) (fun k _ hk => by
      have hnot : ¬ uniformPartitionTime T (n+1) k < τ ω :=
        mt (hlt k).mpr (fun h => hk (Finset.mem_range.mpr h))
      simp only [f, beforeStop, ite_eq_right hnot, zero_mul])
  unfold weightedLeftSum
  change (∑ k ∈ Finset.range (n+1), f k) = _
  rw [← hs]
  have hsum : (∑ k ∈ Finset.range j, f k) =
      ∑ k ∈ Finset.range j, (M (uniformPartitionTime T (n+1) (k+1)) ω -
        M (uniformPartitionTime T (n+1) k) ω) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [f, beforeStop, ite_eq_left ((hlt k).mp (Finset.mem_range.mp hk)), one_mul]
  rw [hsum, Finset.sum_range_sub (fun k => M (uniformPartitionTime T (n+1) k) ω) j]
  simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
  rfl

omit [IsProbabilityMeasure P] in
lemma weightedLeftSum_aestronglyMeasurable (H M : ℝ≥0 → Ω → ℝ)
    (hH : ∀ s, AEStronglyMeasurable (H s) P) (hM : ∀ s, AEStronglyMeasurable (M s) P)
    (T : ℝ≥0) (n : ℕ) : AEStronglyMeasurable (weightedLeftSum H M T n) P := by
  have hi (k : ℕ) : AEStronglyMeasurable (fun ω => H (uniformPartitionTime T n k) ω *
      (M (uniformPartitionTime T n (k+1)) ω - M (uniformPartitionTime T n k) ω)) P :=
    (hH _).mul ((hM _).sub (hM _))
  convert (Finset.aestronglyMeasurable_sum (Finset.range n) (fun k _ => hi k)) using 1
  funext ω
  simp only [weightedLeftSum, Finset.sum_apply]

theorem beforeStop_weightedLeftSum_tendsto {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) (M : ℝ≥0 → Ω → ℝ)
    (hM : ∀ s, AEStronglyMeasurable (M s) P)
    (hcts : ∀ᵐ ω ∂P, Continuous (fun s => M s ω)) :
    TendstoInMeasure P (fun n => weightedLeftSum (beforeStop τ) M T (n+1)) atTop
      (fun ω => M (τ ω) ω - M 0 ω) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact weightedLeftSum_aestronglyMeasurable _ M
      (fun s => ((stronglyAdapted_beforeStop hτ s).mono (𝓕.le s)).aestronglyMeasurable) hM T (n+1)
  · filter_upwards [hcts] with ω hc
    have h := (hc.continuousAt.tendsto.comp (ceilTime_tendsto τ T hbound ω)).sub_const (M 0 ω)
    simpa only [beforeStop_weightedLeftSum τ T hbound M, Function.comp_def] using h

/-- Stopping is proved for the actual scalar operator in the full
filtration, by finite grid identities and two genuine limiting arguments. -/
theorem coordinate_stopped_integral (D : BrownianDriver N P 𝓕) (i : Fin N)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) (U : PredictableProcessL2 𝓕 P)
    (M : ℝ≥0 → Ω → ℝ) (hM : ∀ s, coordinateProcess D i U s =ᵐ[P] M s)
    (hcts : ∀ᵐ ω ∂P, Continuous (fun s => M s ω)) :
    (coordinateIto D i (stoppedIntegrand hτ T U) : Ω → ℝ) =ᵐ[P]
      fun ω => M (τ ω) ω - M 0 ω := by
  have hi := (coordinateIto D i).continuous.continuousAt.tendsto.comp
    (stoppedStepIntegrand_tendsto hτ T U)
  have hoperator := tendstoInMeasure_of_tendsto_Lp hi
  have hleft : TendstoInMeasure P (fun n => weightedLeftSum (beforeStop τ) M T (n+1)) atTop
      (coordinateIto D i (stoppedIntegrand hτ T U)) := by
    apply hoperator.congr_left
    intro n
    exact (coordinateIto_weightedStep_coe D i (beforeStop τ) (stronglyAdapted_beforeStop hτ)
      1 (beforeStop_bound τ) T U n).trans (weightedLeftSum_congr hM (beforeStop τ) T (n+1))
  have hpaths := beforeStop_weightedLeftSum_tendsto hτ T hbound M
    (fun s => (VectorQuadraticVariation.coordinateProcess_memLp D i U s).aestronglyMeasurable.congr (hM s)) hcts
  exact tendstoInMeasure_ae_unique hleft hpaths

theorem vectorIto_weightedStep_coe (D : BrownianDriver N P 𝓕)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H) (K : ℝ≥0)
    (hK : ∀ s ω, ‖H s ω‖ ≤ K) (T : ℝ≥0) (U : Fin N → PredictableProcessL2 𝓕 P) (n : ℕ) :
    (vectorIto D (fun i => weightedStepIntegrand H hH K hK T (U i) n) : Ω → ℝ) =ᵐ[P]
      weightedLeftSum H (vectorProcess D U) T (n+1) := by
  have hall := ae_all_iff.mpr (fun i : Fin N => coordinateIto_weightedStep_coe D i H hH K hK T (U i) n)
  filter_upwards [hall, Lp.coeFn_finsetSum Finset.univ
    (fun i => coordinateIto D i (weightedStepIntegrand H hH K hK T (U i) n))] with ω hi hsum
  simp only [Finset.sum_apply] at hsum
  rw [weightedLeftSum_vectorProcess]
  exact hsum.trans (Finset.sum_congr rfl (fun i _ => hi i))

/-- The same actual stopping identity for a complete vector of independent
coordinate drivers; no scalar natural-filtration substitution is made. -/
theorem vector_stopped_integral (D : BrownianDriver N P 𝓕)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) (U : Fin N → PredictableProcessL2 𝓕 P)
    (M : ℝ≥0 → Ω → ℝ) (hM : ∀ s, vectorProcess D U s =ᵐ[P] M s)
    (hcts : ∀ᵐ ω ∂P, Continuous (fun s => M s ω)) :
    (vectorIto D (fun i => stoppedIntegrand hτ T (U i)) : Ω → ℝ) =ᵐ[P]
      fun ω => M (τ ω) ω - M 0 ω := by
  have hU : Tendsto (fun n i => weightedStepIntegrand (beforeStop τ)
      (stronglyAdapted_beforeStop hτ) 1 (beforeStop_bound τ) T (U i) n) atTop
      (𝓝 (fun i => stoppedIntegrand hτ T (U i))) :=
    tendsto_pi_nhds.mpr (fun i => stoppedStepIntegrand_tendsto hτ T (U i))
  have hi := (vectorItoCLM D).continuous.continuousAt.tendsto.comp hU
  have hi' : Tendsto (fun n => vectorIto D (fun i => weightedStepIntegrand (beforeStop τ)
      (stronglyAdapted_beforeStop hτ) 1 (beforeStop_bound τ) T (U i) n)) atTop
      (𝓝 (vectorIto D (fun i => stoppedIntegrand hτ T (U i)))) := by
    simpa only [Function.comp_def, vectorItoCLM_apply] using hi
  have hoperator := tendstoInMeasure_of_tendsto_Lp hi'
  have hleft : TendstoInMeasure P (fun n => weightedLeftSum (beforeStop τ) M T (n+1)) atTop
      (vectorIto D (fun i => stoppedIntegrand hτ T (U i))) := by
    apply hoperator.congr_left
    intro n
    exact (vectorIto_weightedStep_coe D (beforeStop τ) (stronglyAdapted_beforeStop hτ)
      1 (beforeStop_bound τ) T U n).trans (weightedLeftSum_congr hM (beforeStop τ) T (n+1))
  have hpaths := beforeStop_weightedLeftSum_tendsto hτ T hbound M
    (fun s => (vectorProcess_memLp_two D U s).aestronglyMeasurable.congr (hM s)) hcts
  exact tendstoInMeasure_ae_unique hleft hpaths

end SphericalAging.StoppedVectorIto
