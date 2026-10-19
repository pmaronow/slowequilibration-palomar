module

public import FourPapersCommon.FilteredBrownianIntegral
public import FourPapersCommon.ContinuousAdaptedBrownianIntegral

public section

/-! Genuine limits of bounded continuous adapted left sums in the
full Brownian filtration, including coefficients coupled to independent
Brownian coordinates. The integral is the proved L² isometric extension. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped ENNReal NNReal BigOperators
namespace FourPapersCommon.FilteredBrownian
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
set_option maxHeartbeats 1000000
@[expose] def boundedAdaptedCoefficient (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (t : ℝ≥0) : lpMeas ℝ ℝ (𝓕 t) 2 P :=
  let hm : MemLp (H t) 2 P := MemLp.of_bound
    ((hH t).mono (𝓕.le t)).aestronglyMeasurable K (.of_forall (hK t))
  ⟨hm.toLp (H t), (hH t).aestronglyMeasurable.congr hm.coeFn_toLp.symm⟩

theorem boundedAdaptedCoefficient_coeFn (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (t : ℝ≥0) :
      (boundedAdaptedCoefficient (P:=P) 𝓕 H hH K hK t : Ω → ℝ) =ᵐ[P] H t := by
  unfold boundedAdaptedCoefficient
  exact (MemLp.of_bound ((hH t).mono (𝓕.le t)).aestronglyMeasurable
    K (.of_forall (hK t)) : MemLp (H t) 2 P).coeFn_toLp

theorem elementaryPredictable_boundedCoefficient_coeFn
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (a b : ℝ≥0) :
    (elementaryPredictable 𝓕 a b (boundedAdaptedCoefficient (P:=P) 𝓕 H hH K hK a) :
      ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      elementaryRepresentative 𝓕 a b (H a) := by
  have hz : (fun p : ℝ≥0 × Ω =>
      (boundedAdaptedCoefficient (P:=P) 𝓕 H hH K hK a : Ω → ℝ) p.2) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p => H a p.2 :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp
      (boundedAdaptedCoefficient_coeFn 𝓕 H hH K hK a)
  filter_upwards [elementaryPredictable_coeFn 𝓕 a b
    (boundedAdaptedCoefficient (P:=P) 𝓕 H hH K hK a), hz] with p hp hz
  rw [hp]
  unfold elementaryRepresentative
  rw [hz]

theorem boundedAdaptedStepPredictable_eq_sum
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) (n : ℕ) :
    boundedAdaptedStepPredictable (P:=P) 𝓕 H hH K hK T n =
      ∑ i ∈ Finset.range (n+1), elementaryPredictable 𝓕
        (uniformPartitionTime T (n+1) i) (uniformPartitionTime T (n+1) (i+1))
        (boundedAdaptedCoefficient (P:=P) 𝓕 H hH K hK (uniformPartitionTime T (n+1) i)) := by
  classical
  apply Subtype.ext
  apply Lp.ext
  let E : ℕ → TimeProcessL2 P := fun i => (elementaryPredictable 𝓕
    (uniformPartitionTime T (n+1) i) (uniformPartitionTime T (n+1) (i+1))
    (boundedAdaptedCoefficient (P:=P) 𝓕 H hH K hK (uniformPartitionTime T (n+1) i)) : TimeProcessL2 P)
  have he (i : ℕ) : (E i : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      elementaryRepresentative 𝓕 (uniformPartitionTime T (n+1) i)
        (uniformPartitionTime T (n+1) (i+1)) (H (uniformPartitionTime T (n+1) i)) :=
    elementaryPredictable_boundedCoefficient_coeFn 𝓕 H hH K hK _ _
  have hs := eventuallyEq_sum (s := Finset.range (n+1)) (fun i _ => he i)
  have hl : (boundedAdaptedStepPredictable (P:=P) 𝓕 H hH K hK T n : ℝ≥0 × Ω → ℝ)
      =ᵐ[nonnegativeLebesgueMeasure.prod P] continuousAdaptedLeftStep 𝓕 H T (n+1) :=
    (memLp_continuousAdaptedLeftStep (P:=P) 𝓕 H hH K hK T n).coeFn_toLp
  simp only [Submodule.coe_sum]
  change (boundedAdaptedStepPredictable (P:=P) 𝓕 H hH K hK T n : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
    ((∑ i ∈ Finset.range (n+1), E i : TimeProcessL2 P) : ℝ≥0 × Ω → ℝ)
  filter_upwards [hl, Lp.coeFn_finsetSum (Finset.range (n+1)) E, hs] with p hl hp hs
  rw [hl, hp]
  simpa only [continuousAdaptedLeftStep, Finset.sum_apply] using hs.symm

@[expose] def boundedContinuousBrownianIntegral (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H)
    (hcts : ∀ ω, Continuous (fun t => H t ω)) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) : RandomL2 P :=
  naturalItoIntegral hB hsm hfiltered (boundedContinuousPredictable 𝓕 H hH hcts K hK T)

theorem naturalItoIntegral_boundedAdaptedStep_coeFn
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) (n : ℕ) :
    (naturalItoIntegral hB hsm hfiltered
      (boundedAdaptedStepPredictable (P:=P) 𝓕 H hH K hK T n) : Ω → ℝ) =ᵐ[P]
      uniformAdaptedMartingaleLeftSumProcess B H T (n+1) T := by
  classical
  let A : ℕ → RandomL2 P := fun i => elementaryBrownianValue hB hsm hfiltered
    ((monotone_uniformPartitionTime T (n+1)) (Nat.le_succ i))
    (boundedAdaptedCoefficient (P:=P) 𝓕 H hH K hK (uniformPartitionTime T (n+1) i))
  have he (i : ℕ) : (A i : Ω → ℝ) =ᵐ[P] fun ω =>
      H (uniformPartitionTime T (n+1) i) ω*
        (B (uniformPartitionTime T (n+1) (i+1)) ω-B (uniformPartitionTime T (n+1) i) ω) := by
    filter_upwards [coeFn_elementaryBrownianValue hB hsm hfiltered
      ((monotone_uniformPartitionTime T (n+1)) (Nat.le_succ i))
      (boundedAdaptedCoefficient (P:=P) 𝓕 H hH K hK (uniformPartitionTime T (n+1) i)),
      boundedAdaptedCoefficient_coeFn (P:=P) 𝓕 H hH K hK (uniformPartitionTime T (n+1) i)]
      with ω hω hz
    rw [hω, hz]
  have hid : naturalItoIntegral hB hsm hfiltered
      (boundedAdaptedStepPredictable (P:=P) 𝓕 H hH K hK T n) = ∑ i ∈ Finset.range (n+1), A i := by
    rw [boundedAdaptedStepPredictable_eq_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact naturalItoIntegral_elementaryPredictable hB hsm hfiltered _ _
  rw [hid]
  have hs := eventuallyEq_sum (s := Finset.range (n+1)) (fun i _ => he i)
  filter_upwards [Lp.coeFn_finsetSum (Finset.range (n+1)) A, hs] with ω hω hs
  rw [hω, uniformAdaptedMartingaleLeftSumProcess_terminal]
  simpa only [Finset.sum_apply] using hs

theorem tendstoInMeasure_uniformLeftSum_boundedContinuous
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (hfiltered : IsFilteredPreBrownian B 𝓕 P)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H)
    (hcts : ∀ ω, Continuous (fun t => H t ω)) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) :
    TendstoInMeasure P (fun n => uniformAdaptedMartingaleLeftSumProcess B H T (n+1) T)
      atTop (boundedContinuousBrownianIntegral B hB hsm 𝓕 hfiltered H hH hcts K hK T) := by
  have hh := (naturalItoIntegral hB hsm hfiltered).continuous.continuousAt.tendsto.comp
    (boundedAdaptedStepPredictable_tendsto (P:=P) 𝓕 H hH hcts K hK T)
  exact TendstoInMeasure.congr_left
    (fun n => (naturalItoIntegral_boundedAdaptedStep_coeFn B hB hsm 𝓕 hfiltered H hH K hK T n))
    (tendstoInMeasure_of_tendsto_Lp hh)

end FourPapersCommon.FilteredBrownian
