module
public import FourPapersCommon.TimeChangedBrownian

@[expose] public section

/-! The actual integrated clock of a continuous nonnegative covariance rate.
Its Brownian bracket is the integral of the displayed square-root volatility. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal
namespace FourPapersCommon
open Paper

structure NonnegativeRate where
  rate : ℝ≥0 → ℝ
  continuous_rate : Continuous rate
  nonneg : ∀ t, 0 ≤ rate t

def rateClockReal (c : NonnegativeRate) (t : ℝ) : ℝ := ∫ s in 0..t, c.rate s.toNNReal

theorem rateClockReal_nonneg (c : NonnegativeRate) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ rateClockReal c t := intervalIntegral.integral_nonneg ht (fun s _ => c.nonneg _)

def rateClock (c : NonnegativeRate) (t : ℝ≥0) : ℝ≥0 :=
  ⟨rateClockReal c t,rateClockReal_nonneg c t.coe_nonneg⟩

theorem hasDerivAt_rateClockReal (c : NonnegativeRate) (t : ℝ) :
    HasDerivAt (rateClockReal c) (c.rate t.toNNReal) t := by
  have hc := c.continuous_rate.comp continuous_real_toNNReal
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem continuous_rateClockReal (c : NonnegativeRate) : Continuous (rateClockReal c) :=
  (show Differentiable ℝ (rateClockReal c) from
    fun t => (hasDerivAt_rateClockReal c t).differentiableAt).continuous

theorem continuous_rateClock (c : NonnegativeRate) : Continuous (rateClock c) :=
  ((continuous_rateClockReal c).comp NNReal.continuous_coe).subtype_mk _

theorem rateClock_zero (c : NonnegativeRate) : rateClock c 0 = 0 := by
  apply Subtype.ext
  simp [rateClock,rateClockReal]

theorem monotone_rateClock (c : NonnegativeRate) : Monotone (rateClock c) := by
  intro s t hst
  apply NNReal.coe_le_coe.mp
  change rateClockReal c s ≤ rateClockReal c t
  have hc := c.continuous_rate.comp continuous_real_toNNReal
  have he := intervalIntegral.integral_interval_sub_left (μ := volume)
    (f := fun r => c.rate r.toNNReal) (hc.intervalIntegrable 0 s) (hc.intervalIntegrable 0 t)
  have hn : 0 ≤ ∫ r in (s : ℝ)..(t : ℝ), c.rate r.toNNReal :=
    intervalIntegral.integral_nonneg (by exact_mod_cast hst) (fun r _ => c.nonneg _)
  rw [intervalIntegral.integral_symm (a := (s : ℝ)) (b := (t : ℝ))] at he
  unfold rateClockReal
  linarith

def rateVolatility (c : NonnegativeRate) (t : ℝ≥0) : ℝ := Real.sqrt (c.rate t)

theorem continuous_rateVolatility (c : NonnegativeRate) : Continuous (rateVolatility c) :=
  c.continuous_rate.sqrt

theorem rateVolatility_sq (c : NonnegativeRate) (t : ℝ≥0) : (rateVolatility c t)^2 = c.rate t :=
  Real.sq_sqrt (c.nonneg t)

theorem rateClock_eq_volatility_integral (c : NonnegativeRate) (t : ℝ≥0) :
    (rateClock c t : ℝ) = ∫ s in Ioc (0 : ℝ≥0) t, (rateVolatility c s)^2 ∂nonnegativeLebesgueMeasure := by
  rw [integral_nonnegative_Ioc_eq_real_Icc (fun (s : ℝ≥0) (_ : Unit) => (rateVolatility c s)^2) t ()]
  simp_rw [rateVolatility_sq]
  change (∫ s in 0..(t : ℝ), c.rate s.toNNReal) = ∫ s in Icc (0 : ℝ) t, c.rate s.toNNReal
  rw [intervalIntegral.integral_of_le t.coe_nonneg,integral_Icc_eq_integral_Ioc]

theorem rateBrownian_quadratic_variation (c : NonnegativeRate) :
    ∀ T a, TendstoInMeasure canonicalBrownianMeasure
      (fun n => quadraticVariationBeforeStopApprox (timeChangedBrownian (rateClock c)) T (n+1) a)
      atTop (fun _ => ∫ s in Ioc (0 : ℝ≥0) (min T a),
        (rateVolatility c s)^2 ∂nonnegativeLebesgueMeasure) := by
  intro T a
  rw [← rateClock_eq_volatility_integral]
  exact quadraticVariationBeforeStop_timeChangedBrownian (rateClock c)
    (rateClock_zero c) (continuous_rateClock c) (monotone_rateClock c) T a

theorem rateClock_dist_le_of_rate_bound (c d : NonnegativeRate) {T δ : ℝ}
    (hT : 0 ≤ T) (hδ : 0 ≤ δ)
    (hb : ∀ s ∈ Icc (0 : ℝ) T, ‖c.rate s.toNNReal-d.rate s.toNNReal‖ ≤ δ)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ T) : dist (rateClock c t) (rateClock d t) ≤ δ*T := by
  rw [NNReal.dist_eq]
  change |rateClockReal c t-rateClockReal d t| ≤ δ*T
  unfold rateClockReal
  rw [← intervalIntegral.integral_sub (f := fun s => c.rate s.toNNReal)
    (g := fun s => d.rate s.toNNReal)
    ((c.continuous_rate.comp continuous_real_toNNReal).intervalIntegrable _ _)
    ((d.continuous_rate.comp continuous_real_toNNReal).intervalIntegrable _ _),← Real.norm_eq_abs]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun s =>
    c.rate s.toNNReal-d.rate s.toNNReal) (a := (0 : ℝ)) (b := (t : ℝ)) (C := δ) (by
      intro s hs
      rw [uIoc_of_le t.coe_nonneg] at hs
      exact hb s ⟨hs.1.le,hs.2.trans ht⟩)
  exact hi.trans (by rw [sub_zero,abs_of_nonneg t.coe_nonneg]; exact mul_le_mul_of_nonneg_left ht hδ)

end FourPapersCommon
