module

public import FourPapersCommon.ContinuousAdaptedPredictable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

public section

/-! Predictable coefficients from almost surely continuous adapted processes.
The left-step approximation uses the complete driving filtration. Unlike an
all-paths continuity premise, almost-sure continuity is the standard strong
solution regularity and does not silently require filtration completion. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace FourPapersCommon
theorem continuousAdaptedLeftStep_tendsto_at {Ω : Type*} [MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (H : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (p : ℝ≥0 × Ω) (hH : Continuous (fun t => H t p.2)) :
    Tendsto (fun n => continuousAdaptedLeftStep 𝓕 H T (n+1) p) atTop
      (𝓝 (continuousAdaptedTimeCut H T p)) := by
  classical
  by_cases hp : p.1 ∈ Ioc 0 T
  · simp only [continuousAdaptedTimeCut, if_pos hp]
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := Metric.continuousAt_iff.mp hH.continuousAt ε hε
    have hmesh : Tendsto (fun n : ℕ => ((T / ((n+1:ℕ):ℝ≥0):ℝ≥0):ℝ)) atTop (𝓝 0) := by
      have hn : Tendsto (fun n : ℕ => T / ((n+1:ℕ):ℝ≥0)) atTop (𝓝 0) :=
        (Filter.tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat T)
      simpa only [Function.comp_def, NNReal.coe_zero] using
        NNReal.continuous_coe.continuousAt.tendsto.comp hn
    filter_upwards [hmesh.eventually (eventually_lt_nhds hδ)] with n hn
    have hp' : p.1 ∈ Ioc (uniformPartitionTime T (n+1) 0)
        (uniformPartitionTime T (n+1) (n+1)) := by
      simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        mul_div_cancel_right₀ T (by positivity : ((n+1:ℕ):ℝ≥0) ≠ 0)] using hp
    obtain ⟨i, hi, hcell⟩ := exists_partition_cell hp'
    rw [continuousAdaptedLeftStep_of_cell 𝓕 H T hi p hcell]
    apply hmod
    have hd : dist (uniformPartitionTime T (n+1) i) p.1 ≤
        dist (uniformPartitionTime T (n+1) (i+1)) (uniformPartitionTime T (n+1) i) := by
      rw [NNReal.dist_eq, NNReal.dist_eq, abs_of_nonpos
        (sub_nonpos.mpr (show ((uniformPartitionTime T (n+1) i):ℝ) ≤ p.1 from hcell.1.le)),
        abs_of_nonneg (sub_nonneg.mpr (show ((uniformPartitionTime T (n+1) i):ℝ) ≤
          uniformPartitionTime T (n+1) (i+1) from (monotone_uniformPartitionTime T (n+1)) (Nat.le_succ i)))]
      have hle : (p.1:ℝ) ≤ uniformPartitionTime T (n+1) (i+1) := hcell.2
      linarith
    rw [dist_uniformPartitionTime_succ_eq T (Nat.zero_lt_succ n) i] at hd
    exact hd.trans_lt hn
  · have he : (fun n => continuousAdaptedLeftStep 𝓕 H T (n+1) p) = fun _ => 0 := by
      funext n
      exact continuousAdaptedLeftStep_off 𝓕 H T (Nat.zero_lt_succ n) p hp
    rw [he]
    simp only [continuousAdaptedTimeCut, if_neg hp]
    exact tendsto_const_nhds


variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem aestronglyMeasurable_aeContinuousAdaptedTimeCut
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted F H) (hcts : ∀ᵐ omega ∂P, Continuous (fun t => H t omega))
    (T : ℝ≥0) : AEStronglyMeasurable[F.predictable]
      (continuousAdaptedTimeCut H T) (nonnegativeLebesgueMeasure.prod P) := by
  refine ⟨fun p => limsup (fun n => continuousAdaptedLeftStep F H T (n+1) p) atTop,
    (Measurable.limsup (fun n =>
      (stronglyMeasurable_continuousAdaptedLeftStep F H hH T (n+1)).measurable)).stronglyMeasurable,
    ?_⟩
  have h := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hcts
  filter_upwards [h] with p hp
  exact (continuousAdaptedLeftStep_tendsto_at F H T p hp).limsup_eq.symm

theorem memLp_aeContinuousAdaptedTimeCut
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted F H) (hcts : ∀ᵐ omega ∂P, Continuous (fun t => H t omega))
    (K : ℝ≥0) (hK : ∀ t omega, ‖H t omega‖ ≤ K) (T : ℝ≥0) :
    MemLp (continuousAdaptedTimeCut H T) 2 (nonnegativeLebesgueMeasure.prod P) := by
  have hg := memLp_indicator_const (μ := nonnegativeLebesgueMeasure.prod P) 2
    (measurableSet_Ioc.prod MeasurableSet.univ) (K:ℝ) (Or.inr (finiteMeasure_time_rectangle T))
  exact hg.mono' ((aestronglyMeasurable_aeContinuousAdaptedTimeCut F H hH hcts T).mono
    (predictable_le_prod F)) (.of_forall (continuousAdaptedTimeCut_norm_le H K hK T))

end FourPapersCommon
