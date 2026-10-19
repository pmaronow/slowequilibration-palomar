-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixtureCalculus

/-! The actual continuous extension of (1-r) ξ'(r)/r, including its analytic
removable singularity, for every source infinite mixture. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture
open Set Filter
open scoped Topology ENNReal
variable (μ : InfiniteMixture)

/-- Coefficients of the divided derivative after removing the two zero terms. -/
def dividedCoefficients (p : ℕ) : ℝ := (p+2:ℕ)*μ.coeff (p+2)

/-- The actual analytic extension of the dynamical threshold function. -/
def A (r : ℝ) : ℝ := (1-r)*(∑' p, μ.dividedCoefficients p*r^p)

lemma dividedCoefficients_nonneg (p : ℕ) : 0≤μ.dividedCoefficients p := by
  exact mul_nonneg (Nat.cast_nonneg _) (μ.nonneg _)

theorem summable_dividedCoefficients : Summable μ.dividedCoefficients := by
  have h : Summable (fun p : ℕ => (p:ℝ)*μ.coeff p) := by
    simpa using μ.summable_moment (k := 1) (by omega)
  exact (summable_nat_add_iff 2).2 h

lemma norm_divided_term_le {r : ℝ} (hr : |r|≤1) (p : ℕ) :
    ‖μ.dividedCoefficients p*r^p‖ ≤ μ.dividedCoefficients p := by
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (μ.dividedCoefficients_nonneg p),norm_pow,Real.norm_eq_abs]
  exact mul_le_of_le_one_right (μ.dividedCoefficients_nonneg p) (pow_le_one₀ (abs_nonneg r) hr)

theorem continuousOn_A : ContinuousOn μ.A (Icc (-1:ℝ) 1) := by
  exact (continuous_const.sub continuous_id).continuousOn.mul
    (continuousOn_tsum (fun p => (continuous_const.mul (continuous_id.pow p)).continuousOn)
      μ.summable_dividedCoefficients (fun p r hr => μ.norm_divided_term_le (abs_le.mpr hr) p))

theorem analyticOnNhd_A : AnalyticOnNhd ℝ μ.A (Ioo (-1:ℝ) 1) := by
  have hrad : (1:ℝ≥0∞)≤(FormalMultilinearSeries.ofScalars ℝ μ.dividedCoefficients).radius := by
    apply (FormalMultilinearSeries.ofScalars ℝ μ.dividedCoefficients).le_radius_of_summable_norm (r := 1)
    simpa only [FormalMultilinearSeries.ofScalars_norm,NNReal.coe_one,one_pow,mul_one,
      Real.norm_eq_abs,abs_of_nonneg (μ.dividedCoefficients_nonneg _)] using μ.summable_dividedCoefficients
  intro r hr
  have he : r∈Metric.eball (0:ℝ) (FormalMultilinearSeries.ofScalars ℝ μ.dividedCoefficients).radius := by
    change edist r 0 < _
    apply lt_of_lt_of_le ?_ hrad
    simpa only [edist_dist,dist_zero_right,Real.norm_eq_abs,ENNReal.ofReal_lt_one] using abs_lt.mpr hr
  have h := (FormalMultilinearSeries.ofScalars ℝ μ.dividedCoefficients).analyticOnNhd r he
  change AnalyticAt ℝ (FormalMultilinearSeries.ofScalarsSum μ.dividedCoefficients) r at h
  have hs : AnalyticAt ℝ (fun r => ∑' p, μ.dividedCoefficients p*r^p) r := by
    simpa only [FormalMultilinearSeries.ofScalarsSum_eq_tsum,smul_eq_mul] using h
  exact (analyticAt_const.sub analyticAt_id).mul hs

@[simp] theorem A_one : μ.A 1=0 := by simp [A]

@[simp] theorem A_zero : μ.A 0=2*μ.coeff 2 := by
  unfold A
  simp only [sub_zero,one_mul]
  rw [tsum_eq_single 0 (fun p hp => by simp [zero_pow hp])]
  simp [dividedCoefficients]

lemma jet_one_eq_mul_divided {r : ℝ} (hr : |r|≤1) :
    μ.jet 1 r=r*(∑' p, μ.dividedCoefficients p*r^p) := by
  have hs := (μ.summable_jet (k := 1) (by omega) hr).sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    μ.zero_below_two 0 (by omega),μ.zero_below_two 1 (by omega),zero_mul,add_zero] at hs
  change (∑' p, μ.coeff p*(p.descFactorial 1:ℝ)*r^(p-1))=_
  rw [← hs,← tsum_mul_left]
  apply tsum_congr
  intro p
  simp only [dividedCoefficients,Nat.descFactorial_one,show p+2-1=p+1 by omega,pow_succ]
  ring

/-- The analytically extended A agrees with the literal source formula
using the actual derivative of the infinite covariance. -/
theorem A_eq_threshold {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) : μ.A r=Thresholds.A μ.xi r := by
  rw [Thresholds.A,(μ.hasDerivAt_xi ⟨by linarith [hr.1],hr.2⟩).deriv,
    μ.jet_one_eq_mul_divided (abs_le.mpr ⟨by linarith [hr.1],hr.2.le⟩),A]
  field_simp [hr.1.ne']

end SlowEquilibration.InfiniteMixture
