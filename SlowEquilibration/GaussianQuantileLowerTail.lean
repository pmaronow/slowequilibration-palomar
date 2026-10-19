-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianQuantileConvolution
public import Mathlib.Probability.Moments.Variance

/-!
# One-dimensional quantile bounds for smooth Gaussian lower tails

The secant argument needs concavity only along the smoothing coordinate.
-/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianQuantileLowerTail
open Set MeasureTheory ProbabilityTheory
open OAI.GaussianPropeller.Quantile
open scoped Topology NNReal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The elementary secant estimate underlying the convex Gaussian lower tail. -/
theorem concave_secant_lower_tail {Q : ℝ → ℝ} (hQ : ConcaveOn ℝ univ Q)
    {m σ u : ℝ} (hσ : 0 < σ) (hu : 2*σ ≤ u)
    (hleft : Q (m-2*σ) ≤ -(1/2 : ℝ))
    (hright : (1/2 : ℝ) ≤ Q (m+2*σ)) :
    Q (m-u) ≤ -u/(4*σ) := by
  have hden : 0 < u+2*σ := by linarith
  let a := 4*σ/(u+2*σ)
  let b := (u-2*σ)/(u+2*σ)
  have ha : 0 < a := div_pos (by positivity) hden
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hu) hden.le
  have hab : a+b = 1 := by
    change 4*σ/(u+2*σ)+(u-2*σ)/(u+2*σ) = 1
    rw [← add_div]
    apply (div_eq_one_iff_eq hden.ne').mpr
    ring
  have haeq : a*(u+2*σ) = 4*σ := div_mul_cancel₀ _ hden.ne'
  have hx : a • (m-u) + b • (m+2*σ) = m-2*σ := by
    change a*(m-u)+b*(m+2*σ) = m-2*σ
    nlinarith [congrArg (fun t : ℝ => t*m) hab,
      congrArg (fun t : ℝ => t*(2*σ)) hab]
  have h := hQ.2 (mem_univ (m-u)) (mem_univ (m+2*σ)) ha.le hb hab
  rw [hx] at h
  simp only [smul_eq_mul] at h
  have hs : a * Q (m-u) + b * (1/2 : ℝ) ≤ -(1/2 : ℝ) :=
    by nlinarith [h.trans hleft, mul_le_mul_of_nonneg_left hright hb]
  have ht : a * (-u/(4*σ)) + b*(1/2 : ℝ) = -(1/2 : ℝ) := by
    have hσ4 : 4*σ ≠ 0 := by positivity
    apply (mul_right_cancel₀ hσ4)
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hσ4]
    nlinarith [congrArg (fun t : ℝ => t*(2*σ)) hab]
  rw [← ht] at hs
  exact (mul_le_mul_iff_left₀ ha).mp (by linarith)

/-- The standard Gaussian density is at most one half. -/
theorem normal_density_le_half (x : ℝ) : φ x ≤ (1/2 : ℝ) := by
  apply (φ_le_zero x).trans
  have hp := Real.two_le_pi
  have hs : 2 ≤ Real.sqrt (2*Real.pi) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith
  simp only [φ, zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div,
    Real.exp_zero, mul_one]
  simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hs

/-- A deliberately coarse derivative estimate suffices for the two anchors. -/
theorem normal_cdf_lipschitz : LipschitzWith (1/2 : ℝ≥0) Φ := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_Φ x).differentiableAt)
  intro x
  rw [(hasDerivAt_Φ x).deriv]
  apply (NNReal.coe_le_coe).mp
  simpa only [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (φ_pos x), NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_ofNat] using normal_density_le_half x

/-- Coarse numerical CDF bounds used with Chebyshev's inequality. -/
theorem normal_cdf_half_le : Φ (1/2) ≤ (3/4 : ℝ) := by
  have h := normal_cdf_lipschitz.dist_le_mul (1/2) 0
  rw [Real.dist_eq, Real.dist_eq, Φ_zero] at h
  norm_num at h
  linarith [le_abs_self (Φ (1/2)-1/2)]

theorem quarter_le_normal_cdf_neg_half : (1/4 : ℝ) ≤ Φ (-(1/2)) := by
  rw [Φ_neg]
  linarith [normal_cdf_half_le]

/-- Chebyshev supplies the two quantile anchors, with no atomlessness
assumption beyond the explicit positivity of the smoothed distribution. -/
theorem cdf_le_normal_of_concave_quantile {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Measurable X) (hX2 : MemLp X 2 μ)
    (hmem : ∀ s : ℝ, μ.real {ω | X ω ≤ s} ∈ Ioo (0 : ℝ) 1)
    (hconc : ConcaveOn ℝ univ (fun s : ℝ => q (μ.real {ω | X ω ≤ s})))
    {σ u : ℝ} (hσ : 0 < σ) (hvar : variance X μ = σ^2) (hu : 2*σ ≤ u) :
    μ.real {ω | X ω ≤ (∫ ω, X ω ∂μ)-u} ≤ Φ (-u/(4*σ)) := by
  let m := ∫ ω, X ω ∂μ
  have hcheb : μ.real {ω | 2*σ ≤ |X ω-m|} ≤ (1/4 : ℝ) := by
    have h := ENNReal.toReal_mono (by finiteness)
      (meas_ge_le_variance_div_sq hX2 (show 0 < (2:ℝ)*σ by positivity))
    rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _)), hvar] at h
    have heq : σ^2/(2*σ)^2 = (1/4 : ℝ) := by
      apply (div_eq_iff (pow_ne_zero 2 (mul_ne_zero (by norm_num) hσ.ne'))).mpr
      ring
    simpa only [Measure.real, heq] using h
  have hleftP : μ.real {ω | X ω ≤ m-2*σ} ≤ (1/4 : ℝ) := by
    apply (measureReal_mono (fun ω hω => ?_)).trans hcheb
    change X ω ≤ m-2*σ at hω
    exact (le_trans (by linarith : 2*σ ≤ -(X ω-m)) (neg_le_abs _))
  have hrightP : (3/4 : ℝ) ≤ μ.real {ω | X ω ≤ m+2*σ} := by
    have hcompl : μ.real {ω | X ω ≤ m+2*σ}ᶜ ≤ (1/4 : ℝ) := by
      apply (measureReal_mono (fun ω hω => ?_)).trans hcheb
      simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hω
      exact (le_trans (by linarith : 2*σ ≤ X ω-m) (le_abs_self _))
    rw [probReal_compl_eq_one_sub (measurableSet_le hX measurable_const)] at hcompl
    linarith
  have hl : q (μ.real {ω | X ω ≤ m-2*σ}) ≤ -(1/2 : ℝ) := by
    simpa only [q_Φ] using strictMonoOn_q.monotoneOn (hmem (m-2*σ))
      (Φ_mem (-(1/2 : ℝ))) (hleftP.trans quarter_le_normal_cdf_neg_half)
  have hr : (1/2 : ℝ) ≤ q (μ.real {ω | X ω ≤ m+2*σ}) := by
    simpa only [q_Φ] using strictMonoOn_q.monotoneOn (Φ_mem (1/2 : ℝ))
      (hmem (m+2*σ)) (normal_cdf_half_le.trans hrightP)
  have hsec := concave_secant_lower_tail hconc hσ hu hl hr
  calc
    _ = Φ (q (μ.real {ω | X ω ≤ m-u})) := (Φ_q (hmem (m-u))).symm
    _ ≤ _ := strictMono_Φ.monotone hsec

/-- A concave Gaussian quantile turns the variance bound into a Gaussian
lower-tail envelope, with a universal numerical constant. -/
theorem cdf_le_exp_of_concave_quantile {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Measurable X) (hX2 : MemLp X 2 μ)
    (hmem : ∀ s : ℝ, μ.real {ω | X ω ≤ s} ∈ Ioo (0 : ℝ) 1)
    (hconc : ConcaveOn ℝ univ (fun s : ℝ => q (μ.real {ω | X ω ≤ s})))
    {σ u : ℝ} (hσ : 0 < σ) (hvar : variance X μ = σ^2) (hu : 2*σ ≤ u) :
    μ.real {ω | X ω ≤ (∫ ω, X ω ∂μ)-u} ≤ Real.exp (-u^2/(32*σ^2)) := by
  have hu0 : 0 ≤ u := by linarith
  have hr : 0 ≤ u/(4*σ) := div_nonneg hu0 (by positivity)
  calc
    _ ≤ Φ (-u/(4*σ)) :=
      cdf_le_normal_of_concave_quantile μ X hX hX2 hmem hconc hσ hvar hu
    _ = Φ (-(u/(4*σ))) := by congr 1; ring
    _ ≤ Real.exp (-(u/(4*σ))^2/2) :=
      GaussianQuantileConvolution.Φ_neg_le_exp hr
    _ = Real.exp (-u^2/(32*σ^2)) := by
      congr 1
      field_simp [hσ.ne']
      ring

/-- Absorb the fixed factor from the independent-noise transfer by halving
the Gaussian exponent once the deviation is eight standard deviations. -/
theorem two_mul_exp_variance_bound {σ u : ℝ} (hσ : 0 < σ) (hu : 8*σ ≤ u) :
    2*Real.exp (-u^2/(32*σ^2)) ≤ Real.exp (-u^2/(64*σ^2)) := by
  have hx : 1 ≤ u^2/(64*σ^2) := by
    apply (le_div_iff₀ (by positivity : 0 < 64*σ^2)).mpr
    nlinarith [mul_nonneg (show 0 ≤ u-8*σ by linarith)
      (show 0 ≤ u+8*σ by linarith)]
  have htwo : (2:ℝ) ≤ Real.exp (u^2/(64*σ^2)) := by
    have he : (2:ℝ) ≤ Real.exp 1 := by
      linarith [Real.add_one_le_exp (1:ℝ)]
    exact he.trans (Real.exp_le_exp.mpr hx)
  calc
    _ ≤ Real.exp (u^2/(64*σ^2))*Real.exp (-u^2/(32*σ^2)) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (-u^2/(64*σ^2)) := by
      rw [← Real.exp_add]
      congr 1
      field_simp [hσ.ne']
      ring

end SlowEquilibration.GaussianQuantileLowerTail
