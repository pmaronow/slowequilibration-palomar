module
public import FourPapersCommon.SignedColeHopfBounds
public import FourPapersCommon.ScalarBrownianControl
public import FourPapersCommon.ClockedAdditiveState

@[expose] public section

/-! The actual strong Brownian feedback control for a signed scalar heat log.
The construction uses the already proved pathwise Picard solution and is
identified with the literal controlled state on the entire physical interval. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus FRSB
open scoped Topology NNReal ContDiff
namespace FourPapersCommon
open Paper
set_option maxHeartbeats 1000000

def unitRate : NonnegativeRate := ⟨fun _=>1,continuous_const,fun _=>zero_le_one⟩

@[simp] theorem rateClock_unitRate (t : ℝ≥0) : rateClock unitRate t=t := by
  apply Subtype.ext
  simp [rateClock,rateClockReal,unitRate]

@[simp] theorem timeChangedBrownian_unitRate (t : ℝ≥0) :
    timeChangedBrownian (rateClock unitRate) t=canonicalBrownian t := by
  simp [timeChangedBrownian]

theorem timeChangedBrownianFiltration_unitRate :
    timeChangedBrownianFiltration (rateClock unitRate) (monotone_rateClock unitRate)=
      canonicalBrownianFiltration := by
  apply Filtration.ext
  funext t
  change canonicalBrownianFiltration (rateClock unitRate t)=canonicalBrownianFiltration t
  rw [rateClock_unitRate]

theorem exists_actual_signedHeatFeedback {F : ℝ → ℝ} (hF : SignedScalarDatum F)
    (m x : ℝ) (hm : m≠0) :
    ∃ A : ℝ → BrownianSample → ℝ,IsScalarBrownianControl A ∧
      ∀ t ∈ Icc (0 : ℝ) 1,∀ sample,
        A t sample=signedHeatLogDx (fun y=>Real.exp (m*F y)) m (1-t)
          (scalarControlledState m x A t.toNNReal sample) := by
  obtain ⟨L,hL⟩ := hF.lipschitz
  obtain ⟨K,hK⟩ := exists_lipschitz_signedHeatLogDx_exp hF m hm
  let C : ℝ≥0 := L+1
  have hC : 0<(C : ℝ) := by dsimp [C];positivity
  have hDx := (continuous_signedHeatLog_jets (hF.expHeatDatum m) m
    (fun v y=>(gaussianHeatFlow_exp_pos hF m v y).ne')).2.1
  let Qx : ℝ → ℝ → ℝ := fun t y=>signedHeatLogDx (fun z=>Real.exp (m*F z)) m (1-t) y
  have hQc : Continuous (Function.uncurry Qx) := by
    exact hDx.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)
  have hQb (t y : ℝ) : ‖Qx t y‖≤C :=
    (norm_signedHeatLogDx_exp_le hF L hL m (1-t) y hm).trans (by dsimp [C];norm_num)
  let d : AdditiveDriftData := {
    coefficient := fun _=>m*C
    gradient := fun t y=>Qx t y/C
    radius := ⟨|m*C|,abs_nonneg _⟩
    gradientLip := K/C
    coefficient_measurable := measurable_const
    coefficient_bound := fun _=>by
      change ‖m*(C : ℝ)‖≤|m*(C : ℝ)|
      rw [Real.norm_eq_abs]
    gradient_continuous := hQc.div_const C
    gradient_bound := fun t y=>by
      rw [norm_div,Real.norm_of_nonneg hC.le]
      exact (div_le_one hC).mpr (hQb t y)
    gradient_lipschitz := fun t=>by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      have hh := (hK (1-t)).dist_le_mul y z
      simp only [Real.dist_eq] at hh ⊢
      rw [←sub_div,abs_div,abs_of_pos hC,NNReal.coe_div,div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hh hC.le }
  let X := clockedItoState d unitRate x 1 (by norm_num)
  let A : ℝ → BrownianSample → ℝ := fun t sample=>Qx t (X t.toNNReal sample)
  have hXc : ∀ sample,Continuous (fun t=>X t sample) := continuous_clockedItoState d unitRate x 1 (by norm_num)
  have hXm : Measurable (Function.uncurry X) := measurable_clockedItoState d unitRate x 1 (by norm_num)
  have hXa : StronglyAdapted canonicalBrownianFiltration X := by
    simpa only [timeChangedBrownianFiltration_unitRate] using
      stronglyAdapted_clockedItoState d unitRate x 1 (by norm_num)
  have hAc (sample : BrownianSample) : Continuous (fun t=>A t sample) :=
    hQc.comp (continuous_id.prodMk ((hXc sample).comp continuous_real_toNNReal))
  have hAa : StronglyAdapted canonicalBrownianFiltration (fun t sample=>A t sample) := by
    intro t
    have hh := hQc.comp_stronglyMeasurable
      ((stronglyMeasurable_const : StronglyMeasurable[canonicalBrownianFiltration t]
        (fun _ : BrownianSample=>(t : ℝ))).prodMk (hXa t))
    simpa only [A,Real.toNNReal_coe,Function.uncurry] using hh
  have hAm : Measurable (Function.uncurry A) := by
    exact hQc.measurable.comp (measurable_fst.prodMk
      (hXm.comp (measurable_real_toNNReal.prodMap measurable_id)))
  have hAb : ∀ t sample,‖A t sample‖≤C := fun t sample=>hQb t _
  have hctrl : IsScalarBrownianControl A := ⟨hAc,hAa,hAm,C,hAb⟩
  have hde (t : ℝ≥0) (ht : (t : ℝ)≤1) (sample : BrownianSample) :
      clockedItoDrift d unitRate x 1 (by norm_num) t sample=scalarControlDrift m A t sample := by
    simp only [clockedItoDrift,ite_eq_left ht,scalarControlDrift,A,Real.toNNReal_coe]
    change m*C*(Qx t (X t sample)/C)=m*Qx t (X t sample)
    field_simp
  have hstate (t : ℝ≥0) (ht : (t : ℝ)≤1) (sample : BrownianSample) :
      scalarControlledState m x A t sample=X t sample := by
    have he := clockedItoState_decomposition d unitRate x 1 (by norm_num) t sample
    rw [clockedItoState_zero,timeChangedBrownian_unitRate] at he
    have hi : integratedDrift (clockedItoDrift d unitRate x 1 (by norm_num)) t sample=
        integratedDrift (scalarControlDrift m A) t sample := by
      unfold integratedDrift
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      apply hde
      rw [Real.coe_toNNReal _ hs.1]
      exact hs.2.trans ht
    rw [hi] at he
    exact he.symm
  refine ⟨A,hctrl,?_⟩
  intro t ht sample
  dsimp only [A,Qx]
  rw [hstate t.toNNReal (by rw [Real.coe_toNNReal _ ht.1];exact ht.2) sample]

end FourPapersCommon
