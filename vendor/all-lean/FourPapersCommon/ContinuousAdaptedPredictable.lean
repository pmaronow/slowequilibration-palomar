module

public import FourPapersCommon.ContinuousAdaptedSteps
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! The genuine predictable L² class of a bounded continuous adapted
coefficient, and norm convergence of its actual uniform left step classes. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal Topology BigOperators
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
set_option maxHeartbeats 800000

theorem continuousAdaptedLeftStep_norm_le (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (H : ℝ≥0 → Ω → ℝ) (K : ℝ≥0) (hK : ∀ t ω, ‖H t ω‖ ≤ K)
    (T : ℝ≥0) (n : ℕ) (p : ℝ≥0 × Ω) :
    ‖continuousAdaptedLeftStep 𝓕 H T (n+1) p‖ ≤
      (Ioc (0:ℝ≥0) T ×ˢ (univ:Set Ω)).indicator (fun _ => (K:ℝ)) p := by
  classical
  by_cases hp : p.1 ∈ Ioc 0 T
  · have hp' : p.1 ∈ Ioc (uniformPartitionTime T (n+1) 0)
        (uniformPartitionTime T (n+1) (n+1)) := by
      simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        mul_div_cancel_right₀ T (by positivity : ((n+1:ℕ):ℝ≥0) ≠ 0)] using hp
    obtain ⟨i, hi, hcell⟩ := exists_partition_cell hp'
    rw [continuousAdaptedLeftStep_of_cell 𝓕 H T hi p hcell,
      indicator_of_mem (show p ∈ Ioc (0:ℝ≥0) T ×ˢ (univ:Set Ω) from ⟨hp, mem_univ _⟩)]
    exact hK _ _
  · rw [continuousAdaptedLeftStep_off 𝓕 H T (Nat.zero_lt_succ n) p hp,
      indicator_of_notMem (show p ∉ Ioc (0:ℝ≥0) T ×ˢ (univ:Set Ω) from fun h => hp h.1)]
    simp only [norm_zero, le_refl]

theorem continuousAdaptedTimeCut_norm_le (H : ℝ≥0 → Ω → ℝ) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) (p : ℝ≥0 × Ω) :
    ‖continuousAdaptedTimeCut H T p‖ ≤
      (Ioc (0:ℝ≥0) T ×ˢ (univ:Set Ω)).indicator (fun _ => (K:ℝ)) p := by
  classical
  by_cases hp : p.1 ∈ Ioc 0 T
  · rw [continuousAdaptedTimeCut, if_pos hp,
      indicator_of_mem (show p ∈ Ioc (0:ℝ≥0) T ×ˢ (univ:Set Ω) from ⟨hp, mem_univ _⟩)]
    exact hK _ _
  · rw [continuousAdaptedTimeCut, if_neg hp,
      indicator_of_notMem (show p ∉ Ioc (0:ℝ≥0) T ×ˢ (univ:Set Ω) from fun h => hp h.1)]
    simp only [norm_zero, le_refl]

theorem finiteMeasure_time_rectangle (T : ℝ≥0) :
    (nonnegativeLebesgueMeasure.prod P) (Ioc (0:ℝ≥0) T ×ˢ (univ:Set Ω)) ≠ ∞ := by
  rw [Measure.prod_prod, measure_univ, mul_one]
  exact nonnegativeLebesgueMeasure_Ioc_ne_top 0 T

theorem memLp_continuousAdaptedTimeCut (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H)
    (hcts : ∀ ω, Continuous (fun t => H t ω)) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) :
    MemLp (continuousAdaptedTimeCut H T) 2 (nonnegativeLebesgueMeasure.prod P) := by
  have hg := memLp_indicator_const (μ := nonnegativeLebesgueMeasure.prod P) 2
    (measurableSet_Ioc.prod MeasurableSet.univ) (K:ℝ) (Or.inr (finiteMeasure_time_rectangle T))
  exact hg.mono' ((stronglyMeasurable_continuousAdaptedTimeCut 𝓕 H hH hcts T).mono
    (predictable_le_prod 𝓕)).aestronglyMeasurable
    (.of_forall (continuousAdaptedTimeCut_norm_le H K hK T))

theorem memLp_continuousAdaptedLeftStep (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) (n : ℕ) :
    MemLp (continuousAdaptedLeftStep 𝓕 H T (n+1)) 2 (nonnegativeLebesgueMeasure.prod P) := by
  have hg := memLp_indicator_const (μ := nonnegativeLebesgueMeasure.prod P) 2
    (measurableSet_Ioc.prod MeasurableSet.univ) (K:ℝ) (Or.inr (finiteMeasure_time_rectangle T))
  exact hg.mono' ((stronglyMeasurable_continuousAdaptedLeftStep 𝓕 H hH T (n+1)).mono
    (predictable_le_prod 𝓕)).aestronglyMeasurable
    (.of_forall (continuousAdaptedLeftStep_norm_le 𝓕 H K hK T n))

@[expose] def boundedContinuousPredictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H)
    (hcts : ∀ ω, Continuous (fun t => H t ω)) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) : PredictableProcessL2 𝓕 P :=
  ⟨(memLp_continuousAdaptedTimeCut 𝓕 H hH hcts K hK T).toLp _,
    (stronglyMeasurable_continuousAdaptedTimeCut 𝓕 H hH hcts T).aestronglyMeasurable.congr
      (memLp_continuousAdaptedTimeCut 𝓕 H hH hcts K hK T).coeFn_toLp.symm⟩

@[expose] def boundedAdaptedStepPredictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) (n : ℕ) : PredictableProcessL2 𝓕 P :=
  ⟨(memLp_continuousAdaptedLeftStep 𝓕 H hH K hK T n).toLp _,
    (stronglyMeasurable_continuousAdaptedLeftStep 𝓕 H hH T (n+1)).aestronglyMeasurable.congr
      (memLp_continuousAdaptedLeftStep 𝓕 H hH K hK T n).coeFn_toLp.symm⟩

theorem norm_sq_toLp_sub {S : Type*} [MeasurableSpace S] {Q : Measure S}
    {f g : S → ℝ} (hf : MemLp f 2 Q) (hg : MemLp g 2 Q) :
    ‖hf.toLp f-hg.toLp g‖^2 = ∫ x, (f x-g x)^2 ∂Q := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
    with x hs hx hy
  rw [hs, Pi.sub_apply, hx, hy]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]

theorem boundedAdaptedStepPredictable_tendsto (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H)
    (hcts : ∀ ω, Continuous (fun t => H t ω)) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) :
    Tendsto (boundedAdaptedStepPredictable (P:=P) 𝓕 H hH K hK T) atTop
      (𝓝 (boundedContinuousPredictable (P:=P) 𝓕 H hH hcts K hK T)) := by
  classical
  let A := Ioc (0:ℝ≥0) T ×ˢ (univ:Set Ω)
  have hA : MeasurableSet A := measurableSet_Ioc.prod MeasurableSet.univ
  have hbound : Integrable (A.indicator (fun _ => (2*(K:ℝ))^2)) (nonnegativeLebesgueMeasure.prod P) :=
    memLp_one_iff_integrable.mp (memLp_indicator_const 1 hA ((2*(K:ℝ))^2)
      (Or.inr (finiteMeasure_time_rectangle T)))
  have hd : Tendsto (fun n => ∫ p, (continuousAdaptedLeftStep 𝓕 H T (n+1) p-
      continuousAdaptedTimeCut H T p)^2 ∂(nonnegativeLebesgueMeasure.prod P)) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence
      (μ := nonnegativeLebesgueMeasure.prod P) (f := fun _ => (0:ℝ))
      (F := fun n p => (continuousAdaptedLeftStep 𝓕 H T (n+1) p-
        continuousAdaptedTimeCut H T p)^2)
      (A.indicator (fun _ => (2*(K:ℝ))^2))
      (fun n => by
        convert ((memLp_continuousAdaptedLeftStep (P:=P) 𝓕 H hH K hK T n).aestronglyMeasurable.sub
          (memLp_continuousAdaptedTimeCut (P:=P) 𝓕 H hH hcts K hK T).aestronglyMeasurable).pow 2 using 1
        )
      hbound (fun n => .of_forall fun p => by
        by_cases hp : p ∈ A
        · rw [indicator_of_mem hp, Real.norm_of_nonneg (sq_nonneg _)]
          have ha := continuousAdaptedLeftStep_norm_le 𝓕 H K hK T n p
          have hb := continuousAdaptedTimeCut_norm_le H K hK T p
          rw [indicator_of_mem hp] at ha hb
          have he := (norm_sub_le _ _).trans (add_le_add ha hb)
          have hs := pow_le_pow_left₀ (norm_nonneg _) he 2
          simpa only [Real.norm_eq_abs, sq_abs, two_mul] using hs
        · rw [indicator_of_notMem hp, continuousAdaptedLeftStep_off 𝓕 H T (Nat.zero_lt_succ n) p
            (fun h => hp ⟨h, mem_univ _⟩), continuousAdaptedTimeCut,
            if_neg (show p.1 ∉ Ioc 0 T from fun h => hp ⟨h, mem_univ _⟩)]
          simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), norm_zero, le_refl])
      (.of_forall fun p => by
        simpa only [sub_self, zero_pow (by norm_num : 2 ≠ 0)] using
          ((continuousAdaptedLeftStep_tendsto 𝓕 H hcts T p).sub_const
            (continuousAdaptedTimeCut H T p)).pow 2)
    simpa only [integral_zero] using hh
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hd
  have he (n : ℕ) :
      ‖boundedAdaptedStepPredictable (P:=P) 𝓕 H hH K hK T n-
        boundedContinuousPredictable (P:=P) 𝓕 H hH hcts K hK T‖ =
      Real.sqrt (∫ p, (continuousAdaptedLeftStep 𝓕 H T (n+1) p-
        continuousAdaptedTimeCut H T p)^2 ∂(nonnegativeLebesgueMeasure.prod P)) := by
    change ‖(memLp_continuousAdaptedLeftStep (P:=P) 𝓕 H hH K hK T n).toLp _-
      (memLp_continuousAdaptedTimeCut (P:=P) 𝓕 H hH hcts K hK T).toLp _‖ = _
    rw [← norm_sq_toLp_sub (memLp_continuousAdaptedLeftStep (P:=P) 𝓕 H hH K hK T n)
      (memLp_continuousAdaptedTimeCut (P:=P) 𝓕 H hH hcts K hK T), Real.sqrt_sq (norm_nonneg _)]
  simpa only [Function.comp_def, ← he, Real.sqrt_zero] using hsqrt

end FourPapersCommon
