module

public import StochasticCalculus.ItoConstruction
public import StochasticCalculus.UniformPartitionSums

public section

/-! Uniform left step processes of continuous adapted coefficients are
predictable. All assertions concern the literal process on time × sample. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal Topology BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 600000

theorem exists_partition_cell {t : ℕ → ℝ≥0} {N : ℕ} {s : ℝ≥0}
    (hs : s ∈ Ioc (t 0) (t N)) :
    ∃ i < N, s ∈ Ioc (t i) (t (i+1)) := by
  induction N with
  | zero => exact False.elim (not_lt_of_ge hs.2 hs.1)
  | succ N ih =>
    by_cases h : s ≤ t N
    · obtain ⟨i, hi, hcell⟩ := ih ⟨hs.1, h⟩
      exact ⟨i, Nat.lt_succ_of_lt hi, hcell⟩
    · exact ⟨N, Nat.lt_succ_self N, lt_of_not_ge h, hs.2⟩

theorem partition_cell_unique {t : ℕ → ℝ≥0} (ht : Monotone t)
    {s : ℝ≥0} {i j : ℕ} (hi : s ∈ Ioc (t i) (t (i+1)))
    (hj : s ∈ Ioc (t j) (t (j+1))) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (not_lt_of_ge (hi.2.trans (ht h)) hj.1)
  · exact h
  · exact False.elim (not_lt_of_ge (hj.2.trans (ht h)) hi.1)

@[expose] def continuousAdaptedLeftStep {Ω : Type*} [MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (N : ℕ) (p : ℝ≥0 × Ω) : ℝ :=
  ∑ i ∈ Finset.range N, elementaryRepresentative 𝓕
    (uniformPartitionTime T N i) (uniformPartitionTime T N (i+1))
    (H (uniformPartitionTime T N i)) p

@[expose] def continuousAdaptedTimeCut {Ω : Type*} (H : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (p : ℝ≥0 × Ω) : ℝ :=
  if p.1 ∈ Ioc 0 T then H p.1 p.2 else 0

theorem continuousAdaptedLeftStep_of_cell {Ω : Type*} [MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (H : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) {N i : ℕ} (hi : i < N) (p : ℝ≥0 × Ω)
    (hp : p.1 ∈ Ioc (uniformPartitionTime T N i) (uniformPartitionTime T N (i+1))) :
    continuousAdaptedLeftStep 𝓕 H T N p = H (uniformPartitionTime T N i) p.2 := by
  classical
  unfold continuousAdaptedLeftStep
  rw [Finset.sum_eq_single i]
  · simp only [elementaryRepresentative, if_pos hp]
  · intro j _ hji
    have hj : p.1 ∉ Ioc (uniformPartitionTime T N j) (uniformPartitionTime T N (j+1)) := by
      intro hj
      exact hji (partition_cell_unique (monotone_uniformPartitionTime T N) hj hp)
    simp only [elementaryRepresentative, if_neg hj]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hi))

theorem continuousAdaptedLeftStep_off {Ω : Type*} [MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (H : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) {N : ℕ} (hN : 0 < N) (p : ℝ≥0 × Ω)
    (hp : p.1 ∉ Ioc 0 T) : continuousAdaptedLeftStep 𝓕 H T N p = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  have hb := uniformPartitionTime_mem_Icc_of_le T hN
    (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
  have hcell : p.1 ∉ Ioc (uniformPartitionTime T N i) (uniformPartitionTime T N (i+1)) := by
    intro hcell
    exact hp ⟨(bot_le : (0:ℝ≥0) ≤ _).trans_lt hcell.1, hcell.2.trans hb.2⟩
  exact if_neg hcell

theorem stronglyMeasurable_continuousAdaptedLeftStep {Ω : Type*} [MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted 𝓕 H) (T : ℝ≥0) (N : ℕ) :
    StronglyMeasurable[𝓕.predictable] (continuousAdaptedLeftStep 𝓕 H T N) := by
  classical
  unfold continuousAdaptedLeftStep
  convert (Finset.stronglyMeasurable_sum (Finset.range N) (fun i _ =>
      stronglyMeasurable_elementaryRepresentative 𝓕
        (uniformPartitionTime T N i) (uniformPartitionTime T N (i+1))
        (hH (uniformPartitionTime T N i)))) using 1
  funext p
  simp only [Finset.sum_apply]

theorem continuousAdaptedLeftStep_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (H : ℝ≥0 → Ω → ℝ)
    (hH : ∀ ω, Continuous (fun t => H t ω)) (T : ℝ≥0) (p : ℝ≥0 × Ω) :
    Tendsto (fun n => continuousAdaptedLeftStep 𝓕 H T (n+1) p) atTop
      (𝓝 (continuousAdaptedTimeCut H T p)) := by
  classical
  by_cases hp : p.1 ∈ Ioc 0 T
  · simp only [continuousAdaptedTimeCut, if_pos hp]
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := Metric.continuousAt_iff.mp (hH p.2).continuousAt ε hε
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

theorem stronglyMeasurable_continuousAdaptedTimeCut {Ω : Type*} [MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted 𝓕 H) (hcts : ∀ ω, Continuous (fun t => H t ω)) (T : ℝ≥0) :
    StronglyMeasurable[𝓕.predictable] (continuousAdaptedTimeCut H T) := by
  apply stronglyMeasurable_of_tendsto atTop
    (fun n => stronglyMeasurable_continuousAdaptedLeftStep 𝓕 H hH T (n+1))
  exact tendsto_pi_nhds.mpr (continuousAdaptedLeftStep_tendsto 𝓕 H hcts T)

end FourPapersCommon
