module
public import Paper.DiracShift
public import StochasticCalculus.ItoMaximal

@[expose] public section

/-! A genuine continuous martingale on an arbitrary continuous monotone
deterministic clock, including clocks with flat intervals. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal
namespace FourPapersCommon
open Paper

def timeChangedBrownian (A : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : BrownianSample → ℝ :=
  canonicalBrownian (A t)

def timeChangedBrownianFiltration (A : ℝ≥0 → ℝ≥0) (hm : Monotone A) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace BrownianSample) :=
  monotoneReindexFiltration canonicalBrownianFiltration A hm

theorem continuous_timeChangedBrownian (A : ℝ≥0 → ℝ≥0) (hc : Continuous A)
    (ω : BrownianSample) : Continuous (fun t => timeChangedBrownian A t ω) :=
  (continuous_canonicalBrownian ω).comp hc

theorem measurable_timeChangedBrownian (A : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    Measurable (timeChangedBrownian A t) := measurable_canonicalBrownian (A t)

theorem martingale_timeChangedBrownian (A : ℝ≥0 → ℝ≥0) (hm : Monotone A) :
    Martingale (timeChangedBrownian A) (timeChangedBrownianFiltration A hm)
      canonicalBrownianMeasure := by
  have hb := martingale_brownian_natural isBrownianReal_canonicalBrownian.toIsPreBrownianReal
    (fun t => (measurable_canonicalBrownian t).stronglyMeasurable)
  exact martingale_comp_monotone hb A hm

theorem memLp_timeChangedBrownian (A : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    MemLp (timeChangedBrownian A t) 2 canonicalBrownianMeasure :=
  (isBrownianReal_canonicalBrownian.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval (A t)).memLp_two

theorem timeChangedBrownian_zero (A : ℝ≥0 → ℝ≥0) (h0 : A 0 = 0) (ω : BrownianSample) :
    timeChangedBrownian A 0 ω = 0 := by simp [timeChangedBrownian, h0]

theorem quadraticVariation_timeChangedBrownian (A : ℝ≥0 → ℝ≥0) (h0 : A 0 = 0)
    (hc : Continuous A) (hm : Monotone A) (t : ℝ≥0) :
    HasQuadraticVariationAt (timeChangedBrownian A) canonicalBrownianMeasure t (A t : ℝ) :=
  quadraticVariation_timeChanged_brownian isBrownianReal_canonicalBrownian A h0 hc hm t

theorem quadraticVariationBeforeStop_timeChangedBrownian (A : ℝ≥0 → ℝ≥0)
    (h0 : A 0 = 0) (hc : Continuous A) (hm : Monotone A) :
    HasQuadraticVariationBeforeStopProcessInProbability (timeChangedBrownian A)
      (fun t _ => (A t : ℝ)) canonicalBrownianMeasure := by
  intro T a
  let a' := min T a
  have hclock : Continuous (fun s => A (min s a')) := hc.comp (continuous_id.min continuous_const)
  have hmono : Monotone (fun s => A (min s a')) := fun _ _ h => hm (min_le_min h le_rfl)
  have hzero : A (min 0 a') = 0 := by simpa using h0
  have hstop := (quadraticVariation_timeChanged_brownian isBrownianReal_canonicalBrownian
    (fun s => A (min s a')) hzero hclock hmono T).to_inProbability
  have hcross : TendstoInMeasure canonicalBrownianMeasure
      (fun n => quadraticVariationCrossingStopApprox (timeChangedBrownian A) T (n+1) a')
      atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      unfold quadraticVariationCrossingStopApprox
      apply Finset.aestronglyMeasurable_fun_sum
      intro i hi
      exact ((measurable_timeChangedBrownian A a').aestronglyMeasurable.sub
        (measurable_timeChangedBrownian A _).aestronglyMeasurable).pow 2
    · exact .of_forall fun ω => quadraticVariationCrossingStopApprox_tendsto_zero_of_continuousOn
        (timeChangedBrownian A) T a' ω ⟨bot_le,min_le_left _ _⟩
        (continuous_timeChangedBrownian A hc ω).continuousOn
  have hresult := hstop.sub_real_noMeas hcross
  have heq (n : ℕ) :
      (fun ω => quadraticVariationApprox (fun s => timeChangedBrownian A (min s a')) T (n+1) ω -
        quadraticVariationCrossingStopApprox (timeChangedBrownian A) T (n+1) a' ω) =
      quadraticVariationBeforeStopApprox (timeChangedBrownian A) T (n+1) a' := by
    funext ω
    rw [quadraticVariationApprox_stop_eq_before_add_crossing]
    ring
  have hresult' := hresult.congr_left (fun n => .of_forall (congrFun (heq n)))
  have hbefore (n : ℕ) : quadraticVariationBeforeStopApprox (timeChangedBrownian A) T (n+1) a' =
      quadraticVariationBeforeStopApprox (timeChangedBrownian A) T (n+1) a := by
    funext ω
    unfold quadraticVariationBeforeStopApprox
    apply Finset.sum_congr rfl
    intro i hi
    have hit := uniformPartitionTime_mem_Icc_of_le T (Nat.succ_pos n)
      (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
    have hiff : uniformPartitionTime T (n+1) (i+1) ≤ a' ↔
        uniformPartitionTime T (n+1) (i+1) ≤ a := by
      exact le_min_iff.trans (and_iff_right hit.2)
    simp only [hiff]
  convert hresult'.congr_left (fun n => .of_forall (congrFun (hbefore n))) using 1
  · funext ω
    dsimp [a']
    rw [min_eq_right (min_le_left T a), sub_zero]

end FourPapersCommon
