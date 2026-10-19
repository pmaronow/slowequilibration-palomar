module
public import FourPapersCommon.AdditiveStateMeasurable
public import FourPapersCommon.RateClock
public import FourPapersCommon.VariableItoExpectation

@[expose] public section

/-! A genuine adapted diffusion with the covariance clock of a continuous
nonnegative rate. All stochastic characteristics are proved for the chosen
pathwise integral solution. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal ENNReal
namespace FourPapersCommon
open Paper
section State
variable (d : AdditiveDriftData) (c : NonnegativeRate) (h T : ℝ) (hT : 0 ≤ T)

def rateNoiseReal (ω : BrownianSample) (t : ℝ) : ℝ :=
  timeChangedBrownian (rateClock c) t.toNNReal ω

theorem continuous_rateNoiseReal (ω : BrownianSample) : Continuous (rateNoiseReal c ω) :=
  (continuous_timeChangedBrownian (rateClock c) (continuous_rateClock c) ω).comp continuous_real_toNNReal

def rateNoisePath (ω : BrownianSample) : C(Icc (0 : ℝ) T,ℝ) :=
  ⟨fun t => rateNoiseReal c ω t,(continuous_rateNoiseReal c ω).comp continuous_subtype_val⟩

def clockedStateReal (ω : BrownianSample) : ℝ → ℝ :=
  additiveStateReal d h T hT (rateNoiseReal c ω) (continuous_rateNoiseReal c ω)

theorem continuous_clockedStateReal (ω : BrownianSample) : Continuous (clockedStateReal d c h T hT ω) :=
  continuous_additiveStateReal d h T hT _ _

theorem clockedStateReal_eq_path (ω : BrownianSample) (t : Icc (0 : ℝ) T) :
    clockedStateReal d c h T hT ω t = additiveStatePath d h T hT (rateNoisePath c T ω) t := by
  rw [additiveStatePath_apply]
  apply additiveStateReal_causal d h T hT ⟨hT,le_rfl⟩
    (rateNoiseReal c ω) (parisiNoiseExtension hT (rateNoisePath c T ω))
    (continuous_rateNoiseReal c ω) (continuous_parisiNoiseExtension hT _)
    (fun s hs => by simp [parisiNoiseExtension,rateNoisePath,projIcc_of_mem hT hs]) t.property

theorem clockedStateReal_integral_equation (ω : BrownianSample) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    clockedStateReal d c h T hT ω t = h+rateNoiseReal c ω t+
      ∫ s in 0..t, d.coefficient s*d.gradient s (clockedStateReal d c h T hT ω s) :=
  additiveStateReal_integral_equation d h T hT _ _ ht

def clockedItoState (t : ℝ≥0) (ω : BrownianSample) : ℝ :=
  clockedStateReal d c h T hT ω (min (t : ℝ) T)+
    (timeChangedBrownian (rateClock c) t ω-rateNoiseReal c ω (min (t : ℝ) T))

def clockedItoDrift (t : ℝ≥0) (ω : BrownianSample) : ℝ :=
  if (t : ℝ) ≤ T then d.coefficient t*d.gradient t (clockedItoState d c h T hT t ω) else 0

theorem clockedItoState_eq {t : ℝ≥0} (ht : (t : ℝ) ≤ T) (ω : BrownianSample) :
    clockedItoState d c h T hT t ω = clockedStateReal d c h T hT ω t := by
  simp [clockedItoState,rateNoiseReal,min_eq_left ht]

theorem clockedItoState_zero (ω : BrownianSample) : clockedItoState d c h T hT 0 ω = h := by
  rw [clockedItoState_eq d c h T hT (t := 0) (by simpa using hT)]
  apply additiveStateReal_initial
  simp [rateNoiseReal,rateClock_zero,timeChangedBrownian]

theorem continuous_clockedItoState (ω : BrownianSample) :
    Continuous (fun t => clockedItoState d c h T hT t ω) := by
  have hm : Continuous (fun t : ℝ≥0 => min (t : ℝ) T) := NNReal.continuous_coe.min continuous_const
  exact ((continuous_clockedStateReal d c h T hT ω).comp hm).add
    ((continuous_timeChangedBrownian _ (continuous_rateClock c) ω).sub
      ((continuous_rateNoiseReal c ω).comp hm))

theorem stronglyAdapted_clockedItoState :
    StronglyAdapted (timeChangedBrownianFiltration (rateClock c) (monotone_rateClock c))
      (clockedItoState d c h T hT) := by
  intro t
  let F := timeChangedBrownianFiltration (rateClock c) (monotone_rateClock c)
  let mt : MeasurableSpace BrownianSample := F t
  letI : MeasurableSpace BrownianSample := mt
  have hB (s : ℝ≥0) (hs : s ≤ t) : Measurable (timeChangedBrownian (rateClock c) s) :=
    ((martingale_timeChangedBrownian (rateClock c) (monotone_rateClock c)).stronglyAdapted s).measurable.mono
      (F.mono hs) le_rfl
  let r : Icc (0 : ℝ) T := ⟨min (t : ℝ) T,le_min t.coe_nonneg hT,min_le_right _ _⟩
  have hr : (r : ℝ).toNNReal ≤ t := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ r.property.1]
    exact min_le_left _ _
  have hX : Measurable (fun ω => clockedStateReal d c h T hT ω r) := by
    simp_rw [clockedStateReal_eq_path]
    apply measurable_additiveState_eval_of_measurable_past d h T hT r
    rw [ContinuousMap.measurable_iff_eval]
    intro s
    apply hB s.1.toNNReal
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ s.property.1]
    exact s.property.2.trans (min_le_left _ _)
  exact (hX.add ((hB t le_rfl).sub (hB _ hr))).stronglyMeasurable

theorem measurable_clockedItoState : Measurable (Function.uncurry (clockedItoState d c h T hT)) := by
  apply measurable_uncurry_of_continuous_of_measurable (continuous_clockedItoState d c h T hT)
  intro t
  exact ((stronglyAdapted_clockedItoState d c h T hT t).measurable).mono (Filtration.le _ t) le_rfl

theorem measurable_clockedItoDrift : Measurable (Function.uncurry (clockedItoDrift d c h T hT)) := by
  unfold clockedItoDrift Function.uncurry
  apply Measurable.ite
  · exact measurableSet_le measurable_fst.coe_nnreal_real measurable_const
  · exact (d.coefficient_measurable.comp measurable_fst.coe_nnreal_real).mul
      (d.gradient_continuous.measurable.comp (measurable_fst.coe_nnreal_real.prodMk
        (measurable_clockedItoState d c h T hT)))
  · exact measurable_const

theorem norm_clockedItoDrift_le (t : ℝ≥0) (ω : BrownianSample) :
    ‖clockedItoDrift d c h T hT t ω‖ ≤ d.radius := by
  unfold clockedItoDrift
  split_ifs
  · rw [norm_mul]
    exact (mul_le_mul (d.coefficient_bound t) (d.gradient_bound t _) (norm_nonneg _) d.radius.2).trans_eq (mul_one _)
  · simpa using d.radius.2

theorem integratedDrift_clockedItoDrift (t : ℝ≥0) (ω : BrownianSample) :
    integratedDrift (clockedItoDrift d c h T hT) t ω =
      ∫ s in 0..min (t : ℝ) T, d.coefficient s*d.gradient s (clockedStateReal d c h T hT ω s) := by
  unfold integratedDrift
  have he : (∫ s in Icc (0 : ℝ) (t : ℝ), clockedItoDrift d c h T hT s.toNNReal ω) =
      ∫ s in Icc (0 : ℝ) (t : ℝ), (Icc (0 : ℝ) T).indicator
        (fun s => d.coefficient s*d.gradient s (clockedStateReal d c h T hT ω s)) s := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    unfold clockedItoDrift
    dsimp only
    rw [Real.coe_toNNReal s hs.1]
    by_cases hsT : s ≤ T
    · rw [ite_eq_left hsT,indicator_of_mem (show s ∈ Icc (0 : ℝ) T from ⟨hs.1,hsT⟩),
        clockedItoState_eq d c h T hT (by simpa only [Real.coe_toNNReal s hs.1] using hsT)]
      simp only [Real.coe_toNNReal s hs.1]
    · rw [ite_eq_right hsT,indicator_of_notMem (show s ∉ Icc (0 : ℝ) T from fun hx => hsT hx.2)]
  rw [he,setIntegral_indicator measurableSet_Icc,Icc_inter_Icc,max_self,
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (le_min t.coe_nonneg hT)]

theorem clockedItoState_decomposition (t : ℝ≥0) (ω : BrownianSample) :
    clockedItoState d c h T hT t ω = clockedItoState d c h T hT 0 ω+
      integratedDrift (clockedItoDrift d c h T hT) t ω+timeChangedBrownian (rateClock c) t ω := by
  rw [clockedItoState_zero,integratedDrift_clockedItoDrift]
  unfold clockedItoState
  rw [clockedStateReal_integral_equation d c h T hT ω ⟨le_min t.coe_nonneg hT,min_le_right _ _⟩]
  ring

theorem boundedDriftVariableItoCharacteristics_clockedItoState :
    BoundedDriftVariableItoCharacteristics canonicalBrownianMeasure
      (timeChangedBrownianFiltration (rateClock c) (monotone_rateClock c))
      (clockedItoState d c h T hT) (clockedItoDrift d c h T hT)
      (timeChangedBrownian (rateClock c)) (rateVolatility c) := by
  exact ⟨continuous_rateVolatility c,continuous_clockedItoState d c h T hT,
    stronglyAdapted_clockedItoState d c h T hT,measurable_clockedItoDrift d c h T hT,
    ⟨d.radius,norm_clockedItoDrift_le d c h T hT⟩,clockedItoState_decomposition d c h T hT,
    martingale_timeChangedBrownian _ (monotone_rateClock c),memLp_timeChangedBrownian _,
    rateBrownian_quadratic_variation c⟩

end State
end FourPapersCommon
