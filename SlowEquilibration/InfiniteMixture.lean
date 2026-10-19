-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.MixtureCurvature
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The literal infinite nonnegative mixture of Section 17, with its stated
weighted square-root summability condition. Analyticity is derived from the
actual scalar power series, rather than included in the model's hypotheses. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration
open Set Filter
open scoped Topology ENNReal

structure InfiniteMixture where
  coeff : ℕ → ℝ
  nonneg : ∀ p, 0 ≤ coeff p
  zero_below_two : ∀ p, p < 2 → coeff p = 0
  nonzero : coeff ≠ 0
  weighted_summable : Summable (fun p : ℕ => (p:ℝ) ^ (5/2:ℝ) * Real.sqrt (coeff p))

namespace InfiniteMixture
variable (μ : InfiniteMixture)

/-- The source covariance is the actual infinite power series. -/
def xi (r : ℝ) : ℝ := ∑' p, μ.coeff p * r^p

/-- Weighted coefficient moments, including the endpoint derivatives. -/
def coefficientMoment (k : ℕ) : ℝ := ∑' p : ℕ, (p:ℝ)^k * μ.coeff p

lemma weighted_nonneg (p : ℕ) : 0 ≤ (p:ℝ) ^ (5/2:ℝ) * Real.sqrt (μ.coeff p) := by positivity

lemma weighted_sq (p : ℕ) :
    ((p:ℝ) ^ (5/2:ℝ) * Real.sqrt (μ.coeff p))^2=(p:ℝ)^5*μ.coeff p := by
  rw [mul_pow,Real.sq_sqrt (μ.nonneg p),← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
  norm_num

/-- The manuscript's square-root summability implies the fifth coefficient
moment is finite, including for power series of radius exactly one. -/
theorem summable_fifth_moment : Summable (fun p : ℕ => (p:ℝ)^5*μ.coeff p) := by
  let w : ℕ → ℝ := fun p => (p:ℝ) ^ (5/2:ℝ) * Real.sqrt (μ.coeff p)
  have hw : Summable w := μ.weighted_summable
  have hs : Summable (fun p => w p ^ 2) := by
    apply (hw.mul_left (∑' p, w p)).of_nonneg_of_le (fun p => sq_nonneg (w p))
    intro p
    have hp : w p ≤ ∑' k, w k := hw.le_tsum p (fun p _ => μ.weighted_nonneg p)
    nlinarith [μ.weighted_nonneg p]
  dsimp only [w] at hs
  simpa only [μ.weighted_sq] using hs

/-- Every coefficient moment of order at most five is absolutely summable. -/
theorem summable_moment {k : ℕ} (hk : k ≤ 5) :
    Summable (fun p : ℕ => (p:ℝ)^k*μ.coeff p) := by
  apply μ.summable_fifth_moment.of_nonneg_of_le (fun p => mul_nonneg (pow_nonneg (Nat.cast_nonneg p) _) (μ.nonneg p))
  intro p
  by_cases hp : p<2
  · simp [μ.zero_below_two p hp]
  · exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by exact_mod_cast (show 1≤p by omega)) hk) (μ.nonneg p)

theorem summable_coeff : Summable μ.coeff := by simpa using μ.summable_moment (k := 0) (by omega)

lemma norm_power_term_le {r : ℝ} (hr : |r|≤1) (p : ℕ) :
    ‖μ.coeff p*r^p‖ ≤ μ.coeff p := by
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (μ.nonneg p),norm_pow,Real.norm_eq_abs]
  exact mul_le_of_le_one_right (μ.nonneg p) (pow_le_one₀ (abs_nonneg r) hr)

theorem summable_xi {r : ℝ} (hr : |r|≤1) : Summable (fun p => μ.coeff p*r^p) :=
  .of_norm_bounded μ.summable_coeff (μ.norm_power_term_le hr)

theorem continuousOn_xi : ContinuousOn μ.xi (Icc (-1:ℝ) 1) := by
  apply continuousOn_tsum (fun p => (continuous_const.mul (continuous_id.pow p)).continuousOn)
    μ.summable_coeff
  intro p r hr
  exact μ.norm_power_term_le (abs_le.mpr hr) p

/-- The true scalar series has radius at least one. -/
theorem one_le_radius : (1:ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℝ μ.coeff).radius := by
  apply (FormalMultilinearSeries.ofScalars ℝ μ.coeff).le_radius_of_summable_norm (r := 1)
  simpa only [FormalMultilinearSeries.ofScalars_norm,NNReal.coe_one,one_pow,mul_one,
    Real.norm_eq_abs,abs_of_nonneg (μ.nonneg _)] using μ.summable_coeff

/-- Analyticity throughout the open unit interval follows from the actual
infinite scalar series and the proved radius bound. -/
theorem analyticOnNhd_xi : AnalyticOnNhd ℝ μ.xi (Ioo (-1:ℝ) 1) := by
  intro r hr
  have he : r ∈ Metric.eball (0:ℝ) (FormalMultilinearSeries.ofScalars ℝ μ.coeff).radius := by
    change edist r 0 < _
    apply lt_of_lt_of_le ?_ μ.one_le_radius
    simpa only [edist_dist,dist_zero_right,Real.norm_eq_abs,ENNReal.ofReal_lt_one] using abs_lt.mpr hr
  have h := (FormalMultilinearSeries.ofScalars ℝ μ.coeff).analyticOnNhd r he
  change AnalyticAt ℝ (FormalMultilinearSeries.ofScalarsSum μ.coeff) r at h
  change AnalyticAt ℝ (fun x => ∑' p, μ.coeff p*x^p) r
  simpa only [FormalMultilinearSeries.ofScalarsSum_eq_tsum,smul_eq_mul] using h

@[simp] theorem xi_zero : μ.xi 0=0 := by
  unfold xi
  have hz : (fun p : ℕ => μ.coeff p * (0:ℝ)^p)=0 := by
    funext p
    by_cases hp : p=0
    · subst p;simp [μ.zero_below_two 0 (by omega)]
    · simp [zero_pow hp]
  rw [hz]
  exact tsum_zero

end InfiniteMixture
end SlowEquilibration
