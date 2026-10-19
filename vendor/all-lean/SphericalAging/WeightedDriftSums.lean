module

public import SphericalAging.WeightedItoSums
public import SphericalAging.PredictableDriftTime

public section

/-! Signed drift left sums converge to the actual weighted Lebesgue integral.
The nonnegative density partition theorem is applied to the positive and
negative parts, with both integrability claims proved explicitly. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.WeightedDriftSums
open WeightedItoSums FourPapersCommon
set_option maxHeartbeats 1000000

theorem signed_weighted_integral_tendsto {ν : Measure ℝ≥0}
    (q w : ℝ≥0 → ℝ) (T : ℝ≥0) (hq : IntegrableOn q (Ioc 0 T) ν)
    (hw : Continuous w) (K : ℝ≥0) (hK : ∀ s, ‖w s‖ ≤ K) :
    Tendsto (fun n => ∑ k ∈ Finset.range (n+1),
      w (uniformPartitionTime T (n+1) k) *
        ((∫ s in Ioc 0 (uniformPartitionTime T (n+1) (k+1)), q s ∂ν) -
          ∫ s in Ioc 0 (uniformPartitionTime T (n+1) k), q s ∂ν))
      atTop (𝓝 (∫ s in Ioc 0 T, w s * q s ∂ν)) := by
  let qp : ℝ≥0 → ℝ := fun s => max (q s) 0
  let qm : ℝ≥0 → ℝ := fun s => max (-q s) 0
  have hp : IntegrableOn qp (Ioc 0 T) ν := hq.pos_part
  have hm : IntegrableOn qm (Ioc 0 T) ν := hq.neg_part
  have hwp : IntegrableOn (fun s => w s * qp s) (Ioc 0 T) ν :=
    hp.bdd_mul hw.aestronglyMeasurable (.of_forall hK)
  have hwm : IntegrableOn (fun s => w s * qm s) (Ioc 0 T) ν :=
    hm.bdd_mul hw.aestronglyMeasurable (.of_forall hK)
  have hsplit (s : ℝ≥0) : q s = qp s - qm s := (max_zero_sub_max_neg_zero_eq_self _).symm
  have hprefix (a : ℝ≥0) (ha : a ≤ T) :
      ∫ s in Ioc 0 a, q s ∂ν = (∫ s in Ioc 0 a, qp s ∂ν) - ∫ s in Ioc 0 a, qm s ∂ν := by
    have hpa := hp.mono_set (Ioc_subset_Ioc_right ha)
    have hma := hm.mono_set (Ioc_subset_Ioc_right ha)
    rw [← integral_sub hpa hma]
    exact integral_congr_ae (.of_forall hsplit)
  have hlimit : (∫ s in Ioc 0 T, w s * qp s ∂ν) - (∫ s in Ioc 0 T, w s * qm s ∂ν) =
      ∫ s in Ioc 0 T, w s * q s ∂ν := by
    rw [← integral_sub hwp hwm]
    apply integral_congr_ae
    exact .of_forall (fun s => by change w s * qp s - w s * qm s = w s * q s; rw [hsplit s]; ring)
  have ht := (uniformPartition_weighted_integral_tendsto qp w T hp hwp
    (fun s => le_max_right _ _) hw.continuousOn).sub
      (uniformPartition_weighted_integral_tendsto qm w T hm hwm
        (fun s => le_max_right _ _) hw.continuousOn)
  rw [hlimit] at ht
  convert ht using 1
  funext n
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k < n+1 := Finset.mem_range.mp hk
  rw [hprefix _ (uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n)
    (Nat.succ_le_of_lt hkN)).2,
    hprefix _ (uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n)
      (Nat.le_of_lt hkN)).2]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma integrableOn_nonnegative_iff_real (μ : ℝ≥0 → ℝ) (t : ℝ≥0) :
    IntegrableOn μ (Ioc 0 t) nonnegativeLebesgueMeasure ↔
      IntegrableOn (fun s : ℝ => μ s.toNNReal) (Icc 0 (t : ℝ)) := by
  have hpres : MeasurePreserving ((↑) : ℝ≥0 → ℝ)
      (nonnegativeLebesgueMeasure.restrict (Ioc 0 t))
      (volume.restrict (Ioc 0 (t : ℝ))) :=
    ⟨NNReal.continuous_coe.measurable, map_nonnegativeLebesgueMeasure_restrict_Ioc t⟩
  have h := hpres.integrable_comp_emb measurableEmbedding_nnrealCoe_iterated
    (g := fun s : ℝ => μ s.toNNReal)
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  simpa only [Function.comp_def, Real.toNNReal_coe, IntegrableOn] using h

@[expose] def driftPrimitive (μ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in Ioc 0 t, μ s ω ∂nonnegativeLebesgueMeasure

lemma driftPrimitive_eq_integratedDrift (μ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    driftPrimitive μ t ω = integratedDrift μ t ω := by
  have h := PredictableDriftTime.primitive_eq_real_intervalIntegral
    (fun p : ℝ≥0 × Ω => μ p.1 p.2) t ω
  dsimp only [PredictableDriftTime.primitive] at h
  rw [intervalIntegral.integral_of_le t.coe_nonneg] at h
  rw [integratedDrift, integral_Icc_eq_integral_Ioc]
  exact h

lemma stronglyMeasurable_integratedDrift (μ : ℝ≥0 → Ω → ℝ)
    (hμ : Measurable (Function.uncurry μ)) (t : ℝ≥0) :
    StronglyMeasurable (integratedDrift μ t) := by
  have h := hμ.stronglyMeasurable.integral_prod_left'
    (μ := nonnegativeLebesgueMeasure.restrict (Ioc 0 t))
  convert h using 1
  funext ω
  exact (driftPrimitive_eq_integratedDrift μ t ω).symm

theorem weightedDrift_tendsto (H μ : ℝ≥0 → Ω → ℝ)
    (hcts : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0)
    (hμ : ∀ᵐ ω ∂P, IntegrableOn (fun s => μ s ω) (Ioc 0 T) nonnegativeLebesgueMeasure)
    (hleft : ∀ n, AEStronglyMeasurable
      (weightedLeftSum H (integratedDrift μ) T (n+1)) P) :
    TendstoInMeasure P (fun n => weightedLeftSum H (integratedDrift μ) T (n+1)) atTop
      (fun ω => ∫ s in Ioc 0 T, H s ω * μ s ω ∂nonnegativeLebesgueMeasure) := by
  apply tendstoInMeasure_of_tendsto_ae hleft
  filter_upwards [hcts, hμ] with ω hc hi
  have ht := signed_weighted_integral_tendsto (fun s => μ s ω) (fun s => H s ω) T hi hc K
    (fun s => hK s ω)
  simpa only [weightedLeftSum, ← driftPrimitive_eq_integratedDrift, driftPrimitive] using ht

theorem adapted_weightedDrift_tendsto {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (H μ : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H)
    (hcts : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0)
    (hμmeas : Measurable (Function.uncurry μ))
    (hμ : ∀ᵐ ω ∂P, IntegrableOn (fun s => μ s ω) (Ioc 0 T) nonnegativeLebesgueMeasure) :
    TendstoInMeasure P (fun n => weightedLeftSum H (integratedDrift μ) T (n+1)) atTop
      (fun ω => ∫ s in Ioc 0 T, H s ω * μ s ω ∂nonnegativeLebesgueMeasure) := by
  apply weightedDrift_tendsto H μ hcts K hK T hμ
  intro n
  have hi (k : ℕ) : AEStronglyMeasurable (fun ω => H (uniformPartitionTime T (n+1) k) ω *
      (integratedDrift μ (uniformPartitionTime T (n+1) (k+1)) ω -
        integratedDrift μ (uniformPartitionTime T (n+1) k) ω)) P :=
    ((hH (uniformPartitionTime T (n+1) k)).mono (𝓕.le _)).aestronglyMeasurable.mul
      ((stronglyMeasurable_integratedDrift μ hμmeas (uniformPartitionTime T (n+1) (k+1))).aestronglyMeasurable.sub
        (stronglyMeasurable_integratedDrift μ hμmeas (uniformPartitionTime T (n+1) k)).aestronglyMeasurable)
  unfold weightedLeftSum
  convert (Finset.aestronglyMeasurable_sum (Finset.range (n+1)) (fun k _ => hi k)) using 1
  funext ω
  rw [Finset.sum_apply]

end SphericalAging.WeightedDriftSums
